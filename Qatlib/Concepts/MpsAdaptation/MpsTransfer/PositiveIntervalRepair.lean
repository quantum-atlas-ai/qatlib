/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.PositiveIntervalRepairDefs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Repair into a positive matrix interval

This module proves that `positiveIntervalRepair` lies between zero and `q` times the identity
whenever `q ≥ 0` and the repair radius is positive. A Hermitian approximation within radius `r`
of a matrix in that interval satisfies the repair guard.

The repaired matrix is within `2 * r * q / (q + 2 * r)` of the target, and hence within `2 * r`.
The order and operator-norm estimates use the matrix-analysis framework of [Bhatia1997].

## Main statements

* `positive_interval_repair_mem`: The repaired matrix lies in the specified positive interval.
* `positive_interval_repair_guard_of_error`: A sufficiently accurate Hermitian approximation
  satisfies the guard.
* `positive_interval_repair_error`: The repair has the stated quantitative approximation bounds.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Matrix
open scoped Classical Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable local instance repairMatrixCStar : CStarAlgebra (Matrix N N ℂ) where

/-- For `q ≥ 0` and `r > 0`, the repair weight lies in `[0, 1)` and satisfies the two scalar
identities relating it to `q` and `r`. -/
private theorem repair_weight_properties (q r : ℝ) (hq : 0 ≤ q) (hr : 0 < r) :
    0 ≤ positiveIntervalRepairWeight q r ∧
    positiveIntervalRepairWeight q r < 1 ∧
    positiveIntervalRepairWeight q r * (q + 2*r) = q ∧
    (1-positiveIntervalRepairWeight q r)*q = 2*positiveIntervalRepairWeight q r*r := by
  have hd : 0 < q + 2*r := by linarith
  have ht0 : 0 ≤ q / (q + 2*r) := div_nonneg hq hd.le
  have ht1 : q / (q + 2*r) < 1 := (div_lt_one hd).mpr (by linarith)
  have hm : q / (q + 2*r) * (q + 2*r) = q := div_mul_cancel₀ q hd.ne'
  exact ⟨ht0, ht1, hm, by
    change (1-q/(q+2*r))*q = 2*(q/(q+2*r))*r
    nlinarith [hm]⟩

/-- Multiplying the identity matrix by ordered real scalars preserves their order in the
positive semidefinite matrix order. -/
private theorem repair_smul_one_mono {a b : ℝ} (hab : a ≤ b) :
    a • (1 : Matrix N N ℂ) ≤ b • (1 : Matrix N N ℂ) := by
  rw [Matrix.le_iff]
  simpa only [sub_smul] using
    (Matrix.PosSemidef.one (n := N) (R := ℂ)).smul (sub_nonneg.mpr hab)

/-- A Hermitian matrix of operator norm at most `r` lies between `-r • 1` and `r • 1` in the
positive semidefinite order. -/
private theorem repair_norm_order_bounds (H : Matrix N N ℂ) (r : ℝ)
    (hH : H.IsHermitian) (hn : ‖H‖ ≤ r) :
    (H + r • (1 : Matrix N N ℂ)).PosSemidef ∧
    (r • (1 : Matrix N N ℂ) - H).PosSemidef := by
  have hu : H ≤ ‖H‖ • (1 : Matrix N N ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hH.isSelfAdjoint.le_algebraMap_norm_self
  have hl : -(‖H‖ • (1 : Matrix N N ℂ)) ≤ H := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      hH.isSelfAdjoint.neg_algebraMap_norm_le_self
  have hs : ‖H‖ • (1 : Matrix N N ℂ) ≤ r • (1 : Matrix N N ℂ) :=
    repair_smul_one_mono hn
  constructor
  · simpa only [Matrix.le_iff, sub_neg_eq_add] using (neg_le_neg hs).trans hl
  · exact hu.trans hs

/-- A Hermitian matrix lying between `-c • 1` and `c • 1` for nonnegative `c` has operator norm
at most `c`. -/
private theorem repair_norm_le_of_order_bounds (H : Matrix N N ℂ) (c : ℝ)
    (hc : 0 ≤ c) (hH : H.IsHermitian)
    (hl : (H + c • (1 : Matrix N N ℂ)).PosSemidef)
    (hu : (c • (1 : Matrix N N ℂ) - H).PosSemidef) : ‖H‖ ≤ c := by
  have hl' : algebraMap ℝ (Matrix N N ℂ) (-c) ≤ H := by
    simpa only [Matrix.le_iff, Algebra.algebraMap_eq_smul_one, neg_smul,
      sub_neg_eq_add] using hl
  have hu' : H ≤ algebraMap ℝ (Matrix N N ℂ) c := by
    simpa only [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] using hu
  have hls := (algebraMap_le_iff_le_spectrum hH.isSelfAdjoint).mp hl'
  have hus := (le_algebraMap_iff_spectrum_le hH.isSelfAdjoint).mp hu'
  have hn : ‖cfc (id : ℝ → ℝ) H‖ ≤ c := by
    apply norm_cfc_le hc
    intro x hx
    change ‖x‖ ≤ c
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hls x hx, hus x hx⟩
  simpa only [cfc_id ℝ H hH.isSelfAdjoint] using hn

/-- For nonnegative `q` and positive `r`, the repaired matrix is positive semidefinite and
bounded above by `q • 1`. -/
theorem positive_interval_repair_mem (M : Matrix N N ℂ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 0 < r) :
    (positiveIntervalRepair M q r).PosSemidef ∧
    (q • (1 : Matrix N N ℂ) - positiveIntervalRepair M q r).PosSemidef := by
  obtain ⟨ht0, ht1, hm, hb⟩ := repair_weight_properties q r hq hr
  by_cases hg : positiveIntervalRepairGuard M q r
  · rw [positiveIntervalRepair, if_pos hg]
    constructor
    · exact hg.1.smul ht0
    · have he : q • (1 : Matrix N N ℂ) -
          positiveIntervalRepairWeight q r • (M + r • (1 : Matrix N N ℂ)) =
          positiveIntervalRepairWeight q r • ((q+r) • (1 : Matrix N N ℂ) - M) := by
        rw [smul_add, smul_sub, smul_smul, smul_smul]
        rw [show positiveIntervalRepairWeight q r * (q+r) =
          q-positiveIntervalRepairWeight q r*r by nlinarith [hm], sub_smul]
        abel
      rw [he]
      exact hg.2.smul ht0
  · simp only [positiveIntervalRepair, if_neg hg, sub_zero]
    exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.one.smul hq⟩

/-- Repair with upper endpoint zero returns the zero matrix for every input and radius. -/
theorem positive_interval_repair_zero (M : Matrix N N ℂ) (r : ℝ) :
    positiveIntervalRepair M 0 r = 0 := by
  simp [positiveIntervalRepair, positiveIntervalRepairWeight]

/-- A Hermitian matrix within operator-norm distance `r` of a positive matrix bounded above by
`q • 1` satisfies the repair guard when `q ≥ 0` and `r > 0`. -/
theorem positive_interval_repair_guard_of_error (M E : Matrix N N ℂ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 0 < r) (hM : M.IsHermitian) (hE : E.PosSemidef)
    (hcap : (q • (1 : Matrix N N ℂ) - E).PosSemidef) (herr : ‖M-E‖ ≤ r) :
    positiveIntervalRepairGuard M q r := by
  have hb := repair_norm_order_bounds (M-E) r (hM.sub hE.isHermitian) herr
  constructor
  · convert hb.1.add hE using 1 <;> abel
  · convert hcap.add hb.2 using 1
    rw [add_smul]
    abel

/-- Repairing a Hermitian approximation within distance `r` of a matrix in `[0, q • 1]` gives
error at most `2 * r * q / (q + 2 * r)` and at most `2 * r`, for `q ≥ 0` and `r > 0`. -/
theorem positive_interval_repair_error (M E : Matrix N N ℂ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 0 < r) (hM : M.IsHermitian) (hE : E.PosSemidef)
    (hcap : (q • (1 : Matrix N N ℂ) - E).PosSemidef) (herr : ‖M-E‖ ≤ r) :
    ‖positiveIntervalRepair M q r-E‖ ≤ 2*r*q/(q+2*r) ∧
    ‖positiveIntervalRepair M q r-E‖ ≤ 2*r := by
  let t := positiveIntervalRepairWeight q r
  let K : Matrix N N ℂ := (t*r) • (1 : Matrix N N ℂ) - (1-t) • E
  obtain ⟨ht0, ht1, hm, hb⟩ := repair_weight_properties q r hq hr
  change 0 ≤ t at ht0
  change t < 1 at ht1
  change (1-t)*q = 2*t*r at hb
  have htcomp : 0 ≤ 1-t := by linarith
  have hK : K.IsHermitian :=
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all (t*r))).sub
      (hE.isHermitian.smul (IsSelfAdjoint.all (1-t)))
  have hKl : (K + (t*r) • (1 : Matrix N N ℂ)).PosSemidef := by
    convert hcap.smul htcomp using 1
    dsimp only [K]
    rw [smul_sub, smul_smul, hb, show 2*t*r = t*r+t*r by ring, add_smul]
    abel
  have hKu : ((t*r) • (1 : Matrix N N ℂ) - K).PosSemidef := by
    convert hE.smul htcomp using 1
    dsimp only [K]
    abel
  have hKn : ‖K‖ ≤ t*r :=
    repair_norm_le_of_order_bounds K (t*r) (mul_nonneg ht0 hr.le) hK hKl hKu
  have hg := positive_interval_repair_guard_of_error M E q r hq hr hM hE hcap herr
  have he : positiveIntervalRepair M q r - E = t • (M-E) + K := by
    rw [positiveIntervalRepair, if_pos hg]
    change t • (M + r • (1 : Matrix N N ℂ)) - E = t • (M-E) + K
    dsimp only [K]
    rw [smul_add, smul_sub, smul_smul, sub_smul, one_smul]
    abel
  have hn : ‖positiveIntervalRepair M q r-E‖ ≤ 2*t*r := calc
    ‖positiveIntervalRepair M q r-E‖ = ‖t • (M-E) + K‖ := congrArg norm he
    _ ≤ ‖t • (M-E)‖ + ‖K‖ := norm_add_le _ _
    _ = t*‖M-E‖ + ‖K‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    _ ≤ t*r + t*r := add_le_add (mul_le_mul_of_nonneg_left herr ht0) hKn
    _ = 2*t*r := by ring
  have hc : 2*t*r = 2*r*q/(q+2*r) := by
    dsimp only [t, positiveIntervalRepairWeight]
    ring
  constructor
  · rwa [← hc]
  · exact hn.trans (by nlinarith [mul_le_mul_of_nonneg_right (le_of_lt ht1) hr.le])

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
