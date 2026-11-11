/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-!
# Gaussian overlap beyond the cutoff radius

This module proves the strict threshold guarantee for the scalar Gaussian overlap formula. If
both exponents are bounded below by a positive `aMin` and the nonnegative separation exceeds
`cutoffDistance aMin k`, the overlap is strictly below `10⁻ᵏ`. See [McCleanEtAl2014].

## Main statements

* `gaussOverlap_lt_threshold`: If `a, b ≥ aMin > 0` and the nonnegative separation `R` strictly
  exceeds `cutoffDistance aMin k`, then `gaussOverlap a b R < 10⁻ᵏ`.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.SparseLocality

open Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-- If `a, b ≥ aMin > 0` and the nonnegative separation `R` strictly exceeds `cutoffDistance
aMin k`, then `gaussOverlap a b R < 10⁻ᵏ`. See [McCleanEtAl2014]. -/
theorem gaussOverlap_lt_threshold {a b R aMin : ℝ} {k : ℕ}
    (haMin : 0 < aMin) (ha : aMin ≤ a) (hb : aMin ≤ b) (_hR : 0 ≤ R)
    (hcut : cutoffDistance aMin k < R) :
    gaussOverlap a b R < (10 : ℝ) ^ (-(k : ℝ)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set A : ℝ := Real.pi / (2 * aMin) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have habpos : 0 < a + b := by linarith

  have hRpos : 0 < R := lt_of_le_of_lt (Real.sqrt_nonneg _) hcut

  have hDlt : aMin⁻¹ * Real.log (A ^ 3 * (10 : ℝ) ^ (2 * k)) < R ^ 2 := by
    rw [cutoffDistance] at hcut
    rw [← hAdef] at hcut
    exact (Real.sqrt_lt' hRpos).mp hcut

  have hlogeq : Real.log (A ^ 3 * (10 : ℝ) ^ (2 * k))
      = 3 * Real.log A + (2 * (k : ℝ)) * Real.log 10 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring

  have hlogS_eq : Real.log (gaussOverlap a b R)
      = (3 / 2) * Real.log (Real.pi / (a + b)) - (a * b / (a + b)) * R ^ 2 := by
    unfold gaussOverlap
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_exp]
    ring
  have hlog_le : Real.log (gaussOverlap a b R)
      ≤ (3 / 2) * Real.log A - (aMin / 2) * R ^ 2 := by
    rw [hlogS_eq]
    have hbase : Real.log (Real.pi / (a + b)) ≤ Real.log A := by
      rw [hAdef]
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hab : aMin / 2 ≤ a * b / (a + b) := by
      rw [le_div_iff₀ habpos]
      nlinarith
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    have hcoef : (aMin / 2) * R ^ 2 ≤ (a * b / (a + b)) * R ^ 2 :=
      mul_le_mul_of_nonneg_right hab hR2
    have hc1 : (3 / 2) * Real.log (Real.pi / (a + b)) ≤ (3 / 2) * Real.log A :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    linarith

  have hrel : (3 / 2) * Real.log A - (aMin / 2) * R ^ 2
      < -(k : ℝ) * Real.log 10 := by
    have hmul := mul_lt_mul_of_pos_left hDlt haMin
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt haMin), one_mul] at hmul
    rw [hlogeq] at hmul
    nlinarith
  have hTlog : Real.log ((10 : ℝ) ^ (-(k : ℝ))) = -(k : ℝ) * Real.log 10 := by
    rw [Real.log_rpow (by norm_num)]
  have hlt : Real.log (gaussOverlap a b R) < Real.log ((10 : ℝ) ^ (-(k : ℝ))) := by
    rw [hTlog]
    linarith
  have hSpos : 0 < gaussOverlap a b R := by
    unfold gaussOverlap
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  exact (Real.log_lt_log_iff hSpos (by positivity)).mp hlt

end Qatlib.Papers.QChemistry14.ScalarModels.SparseLocality
