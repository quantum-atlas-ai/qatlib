module

import Qatlib.Papers.QSearchBoyer98.MainResults.IntegerRestartBudget

/-!
# Consumer checks for the integer restart budget

This ordinary module instantiates the uniform integer restart theorems on a concrete
non-degenerate search space: `Fin 40000` with the single marked address `0` and angle
`arcsin (1 / 200)`.  It checks that the absolute constant from
`integer_restart_paid_uniform` applies, and that the actual bit-oracle receipt theorem produces a
positive success probability and finite expected paid time.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.RestartLaw
open Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Papers.QSearchBoyer98.MainResults
open Qatlib.Papers.QSearchBoyer98.MainResults

namespace QatlibTests.QSearchBoyer98IntegerRestartConsumer

noncomputable section

/-- A concrete non-degenerate instance: one marked address in `Fin 40000`, with
`sin θ = 1 / 200`, so `sin² θ = 1 / 40000` is exactly the marked fraction. -/
def θ : ℝ := Real.arcsin (1 / 200)

/-- The marked set of the concrete instance. -/
def A : Finset (Fin 40000) := {0}

/-- Exactly one address is marked. -/
theorem A_card : A.card = 1 := by
  simp [A]

/-- The marked set is nonempty. -/
theorem A_pos : 0 < A.card := by
  rw [A_card]
  norm_num

/-- The concrete angle has the prescribed sine. -/
theorem sin_θ : Real.sin θ = 1 / 200 := by
  unfold θ
  rw [Real.sin_arcsin] <;> norm_num

/-- The concrete angle is positive. -/
theorem θ_pos : 0 < θ := by
  unfold θ
  exact Real.arcsin_pos.mpr (by norm_num)

/-- The concrete angle is in the small-angle range of the restart theorem. -/
theorem θ_lt : θ < 1 / 100 := by
  unfold θ
  rw [Real.arcsin_lt_iff_lt_sin]
  · have h := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1 / 100)
    norm_num at h ⊢
    linarith
  · norm_num
  · constructor <;> linarith [Real.pi_gt_d2]

/-- The squared sine matches the exact marked fraction. -/
theorem marked_fraction : Real.sin θ ^ 2 = (A.card : ℝ) / (Fintype.card (Fin 40000) : ℝ) := by
  rw [sin_θ, A_card]
  norm_num

/-- The uniform integer restart constant applies to the concrete instance, giving a guaranteed
marked success above `78 / 100` and a paid iteration cost bounded by `C / θ`. -/
example : ∃ C z : ℝ, 0 < C ∧ C < Real.pi / 4 ∧
    (78 / 100 : ℝ) < MeasureProb (GroverState A ⌊z / (4 * θ)⌋₊) A ∧
      (⌊z / (4 * θ)⌋₊ + 1 : ℝ) /
          MeasureProb (GroverState A ⌊z / (4 * θ)⌋₊) A ≤ C / θ := by
  obtain ⟨z₀, ⟨hz₀, hz₀lo, hz₀hi⟩, _⟩ := section3OptimalAngleSubgoal
  obtain ⟨z, hzlo, hzhi, hzroot⟩ :=
    exists_stationary_root_close hz₀ hz₀lo hz₀hi θ θ_pos (by linarith [θ_lt])
  obtain ⟨C, hCpos, hCpi, hbound⟩ := integer_restart_paid_uniform
  exact ⟨C, z, hCpos, hCpi,
    hbound A θ z z₀ ⌊z / (4 * θ)⌋₊ A_pos marked_fraction θ_pos θ_lt
      hz₀ hz₀lo hz₀hi hzlo hzhi hzroot rfl⟩

/-- The actual bit-oracle search word at the same concrete budget has positive success and the
paid receipt predicted by `actual_integer_restart_receipt`. -/
example : ∃ z : ℝ,
    let j := ⌊z / (4 * θ)⌋₊
    let T' := (1 : Matrix (Fin 40000) (Fin 40000) ℂ)
    let v := Uniform (Fin 40000)
    ∃ hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j),
      ∃ hv : Normalized v,
        let p := MeasureProb (GroverState A j) A
        let next := bbhtActualRestartNextPrice T' v j A hC hv (j + 1)
        QueryCount (bbhtBitSearchCircuit T' v j) + 1 = j + 1 ∧
          0 < p ∧
          generalNeverMass (branchClockNext next) (branchClockEmbed (Sum.inr ())) = 0 ∧
          generalUnboundedTime (branchClockNext next) (branchClockEmbed (Sum.inr ())) =
            ENNReal.ofReal ((j + 1 : ℝ) / p) := by
  obtain ⟨z₀, ⟨hz₀, hz₀lo, hz₀hi⟩, _⟩ := section3OptimalAngleSubgoal
  obtain ⟨z, hzlo, hzhi, _⟩ :=
    exists_stationary_root_close hz₀ hz₀lo hz₀hi θ θ_pos (by linarith [θ_lt])
  have hN : 0 < Fintype.card (Fin 40000) := by norm_num
  have hword := actualRestartSearchWord (Fin 40000) hN
    (1 : Matrix (Fin 40000) (Fin 40000) ℂ) (Uniform (Fin 40000))
    (Submonoid.one_mem _) (normalized_uniform hN) (by simp) A ⌊z / (4 * θ)⌋₊
  refine ⟨z, hword.1, normalized_uniform hN, ?_⟩
  exact actual_integer_restart_receipt A θ z z₀ ⌊z / (4 * θ)⌋₊
    A_pos marked_fraction θ_pos θ_lt hz₀ hz₀lo hz₀hi hzlo hzhi rfl
    (1 : Matrix (Fin 40000) (Fin 40000) ℂ) (Uniform (Fin 40000))
    (Submonoid.one_mem _) (normalized_uniform hN) (by simp) hword.1

end

end QatlibTests.QSearchBoyer98IntegerRestartConsumer
