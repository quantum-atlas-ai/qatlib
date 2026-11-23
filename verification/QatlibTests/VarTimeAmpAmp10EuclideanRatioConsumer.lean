module

import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.EuclideanRatio
import Mathlib.Tactic.FinCases

/-!
# Consumer checks for the Euclidean Corollary 1 assembly

This ordinary module instantiates the new Euclidean ratio theorem on a
non-degenerate one-dimensional branch space. The normalized branch state has one
unit coefficient, its stopping law has unit mass at stage zero, and the branch
success probability is the Lemma 8 witness `1/4`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.VarTimeAmpAmp10EuclideanRatioConsumer

open Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

/-- The normalized branch state on the one-dimensional encoded register. -/
def oneState : EuclideanSpace ℂ (Fin 1) :=
  WithLp.toLp 2 ![1]

/-- The non-degenerate stopping law: all mass is at stage zero. -/
def stopLaw : Fin 1 → ℕ → ℝ := fun _ s => if s = 0 then 1 else 0

/-- The Lemma 8 success-probability witness for `ε = κ = 1`. -/
noncomputable def branchQ : Fin 1 → ℝ := ![1 / 4]

/-- The concrete branch state is normalized in the Euclidean norm. -/
theorem oneState_norm : ‖oneState‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [oneState]

/-- The concrete stopping moment is one. -/
theorem stop_moment :
    ∑ s ∈ Finset.range 2, stopLaw 0 s * ((2 : ℝ) ^ s) ^ 2 = 1 := by
  simp [stopLaw]

/-- The Euclidean theorem applies to the concrete non-degenerate instance and
gives the explicit uniform ratio bound. -/
example :
    (1 : ℝ) / Real.sqrt (1 / 4) ≤ 4 := by
  have hbound := source_corollary1_euclidean
    (branchCount := 1) (by norm_num : 0 < 1) oneState
    (fun _ => 0) (fun _ => 0) stopLaw branchQ
    1 (1 / 4) 1 1 1
    (by norm_num) (by norm_num) (by norm_num) oneState_norm
    (by intro i s; dsimp only [stopLaw]; split <;> norm_num)
    (by
      intro i
      fin_cases i
      simp [stopLaw])
    (by
      intro i
      fin_cases i
      norm_num)
    (by
      have hinner : ∑ i : Fin 1, ‖oneState i‖ ^ 2 *
          (∑ s ∈ Finset.range 2, stopLaw i s * ((2 : ℝ) ^ s) ^ 2) = 1 := by
        simp [oneState, stopLaw]
      rw [hinner]
      norm_num)
    (by
      simp [oneState, branchQ])
    (by
      intro i
      fin_cases i
      norm_num [branchQ])
  have hrhs : 4 * (1 : ℝ) * (1 / 1) = 4 := by norm_num
  rw [hrhs] at hbound
  exact hbound

end QatlibTests.VarTimeAmpAmp10EuclideanRatioConsumer
