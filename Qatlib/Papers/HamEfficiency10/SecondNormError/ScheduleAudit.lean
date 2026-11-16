/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamEfficiency10.SecondNormError.ModelAudit

@[expose] public section


/-! # Low-order words admitted by the legacy high-order schedule

Normalization and bounded coefficient mass do not impose Suzuki's recursive
order conditions. A zero-padded Strang schedule at k=2 is accepted by the
literal model but has cubic rather than fifth-order error. The fixed paper
uses the actual recursive construction; no paper upper bound is refuted here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Papers.HamEfficiency10.SuzukiWord
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily

namespace Qatlib.Papers.HamEfficiency10.SecondNormError.ScheduleAudit

/-- A padded Strang schedule satisfies every literal k=2 coefficient condition. -/
def padded : TwoTermSchedule 2 := {
  z := ![1, 0, 0, 0, 0]
  s := ![1/2, 1/2, 0, 0, 0, 0]
  sum_z := by
    change (∑ j : Fin 5, (![1, 0, 0, 0, 0] : Fin 5 → ℝ) j) = 1
    norm_num [Fin.sum_univ_succ]
  sum_s := by
    change (∑ j : Fin 6, (![1/2, 1/2, 0, 0, 0, 0] : Fin 6 → ℝ) j) = 1
    norm_num [Fin.sum_univ_succ]
  mass_le := by
    change (∑ j : Fin 6, |(![1/2, 1/2, 0, 0, 0, 0] : Fin 6 → ℝ) j|) +
      (∑ j : Fin 5, |(![1, 0, 0, 0, 0] : Fin 5 → ℝ) j|) ≤ scalingConstant 2
    norm_num [Fin.sum_univ_succ, scalingConstant] }

/-- Zero padding does not change the actual Strang product or its error. -/
theorem paddedError (t : ℝ) :
    ‖hamiltonianEvolution (hZ + hX) (-t) -
      twoTermWord hZ hX (5 ^ (2 - 1)) padded.z padded.s (-t)‖ = ‖error t‖ := by
  rw [actual_execution, norm_sub_rev]
  congr 1
  simp [padded, twoTermWord, hamiltonianEvolution, total, genZ, genX,
    smul_add, ← smul_assoc, Complex.real_smul, mul_assoc, mul_comm,
    div_eq_mul_inv]

/-- The positive scalar coefficient in the old normalized k=2 fifth-order bound. -/
def oldCoefficient : ℝ := 4 / (Nat.factorial 5 : ℝ) * scalingConstant 2 ^ 5

/-- Some actual admissible nonzero step violates that literal fifth-order bound. -/
theorem violatesOrder :
    ∃ dt : ℝ, scalingConstant 2 * |dt| ≤ (2 : ℝ) + 1 ∧
      4 * ‖hX‖ / (Nat.factorial (2 * 2 + 1) : ℝ) *
          (scalingConstant 2 * |dt|) ^ (2 * 2 + 1) <
        ‖hamiltonianEvolution (hZ + hX) dt -
          twoTermWord hZ hX (5 ^ (2 - 1)) padded.z padded.s dt‖ := by
  have hc : 0 < scalingConstant 2 := scalingConstant_pos _
  let δ := min 1 (3 / scalingConstant 2)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨t, ht, htd, hv⟩ := not_fourth_order oldCoefficient δ hd
  have ht1 : t ≤ 1 := htd.trans (min_le_left _ _)
  have htc : t ≤ 3 / scalingConstant 2 := htd.trans (min_le_right _ _)
  have hB : ‖hX‖ ≤ 1 := by simpa [genX, norm_smul] using gen_norms.2
  have hC : 0 ≤ oldCoefficient := by unfold oldCoefficient; positivity
  have hp : t^5 ≤ t^4 := by
    calc t^5 = t^4 * t := by ring
      _ ≤ t^4 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = t^4 := mul_one _
  refine ⟨-t, ?_, ?_⟩
  · rw [abs_neg, abs_of_pos ht]
    have hb : t * scalingConstant 2 ≤ 3 := (le_div_iff₀ hc).mp htc
    nlinarith
  · rw [paddedError, abs_neg, abs_of_pos ht]
    have hbound : 4 * ‖hX‖ / (Nat.factorial (2 * 2 + 1) : ℝ) *
        (scalingConstant 2 * t) ^ (2 * 2 + 1) ≤ oldCoefficient * t^5 := by
      calc _ = ‖hX‖ * (oldCoefficient * t^5) := by
             norm_num [oldCoefficient, Nat.factorial]; ring
        _ ≤ 1 * (oldCoefficient * t^5) :=
             mul_le_mul_of_nonneg_right hB (by positivity)
        _ = _ := one_mul _
    exact (hbound.trans (mul_le_mul_of_nonneg_left hp hC)).trans_lt hv

/-- Every remaining Hermiticity and normalization premise holds in this full k=2 countermodel. -/
theorem fullCountermodel : hZ.IsHermitian ∧ hX.IsHermitian ∧ ‖hZ‖ = 1 ∧ ‖hX‖ ≤ 1 ∧
    ∃ dt : ℝ, scalingConstant 2 * |dt| ≤ (2 : ℝ) + 1 ∧
      ¬ ‖hamiltonianEvolution (hZ + hX) dt -
          twoTermWord hZ hX (5 ^ (2 - 1)) padded.z padded.s dt‖ ≤
        4 * ‖hX‖ / (Nat.factorial (2 * 2 + 1) : ℝ) *
          (scalingConstant 2 * |dt|) ^ (2 * 2 + 1) := by
  have hn : ‖hZ‖ = 1 := ModelAudit.firstNorm
  have hB : ‖hX‖ ≤ 1 := by simpa [genX, norm_smul] using gen_norms.2
  refine ⟨hermitian_hZ, hermitian_hX, hn, hB, ?_⟩
  obtain ⟨dt, hs, hv⟩ := violatesOrder
  exact ⟨dt, hs, not_le_of_gt hv⟩

end Qatlib.Papers.HamEfficiency10.SecondNormError.ScheduleAudit
