/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFRootStep

/-!
# Root-based segment counts and local budgets

This module defines `rootFactor` and the positive integer segment `count` by a ceiling
construction. For nonnegative scaled time and coefficient mass with positive tolerance, the
count keeps each scaled step at most 1/2.

For positive order, the accumulated polynomial local-error bound is at most ε/(12π), supplying
the scalar budget for the long-time multi-product analysis associated with [AftabAnTrivisa2026].

## Main statements

* `count_upper`: bounds the ceiling overhead by one.
* `step_control`: bounds the scaled step.
* `accumulated_local`: proves the accumulated local-error budget.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFSegments

/-- The real power (1 + 8πzA/ε)^(1/(2m)) used to choose the segment count. -/
def rootFactor (z A ε : ℝ) (m : ℕ) : ℝ :=
  (1 + 8 * Real.pi * z * A / ε) ^ (((2 * m : ℕ) : ℝ)⁻¹)

/-- The maximum of 1 and the natural-number ceiling of 2z times the root factor. -/
def count (z A ε : ℝ) (m : ℕ) : ℕ := max 1 (Nat.ceil (2 * z * rootFactor z A ε m))

/-- The selected segment count is strictly positive. -/
theorem count_pos (z A ε : ℝ) (m : ℕ) : 0 < count z A ε m := by
  exact lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

/-- For z ≥ 0, A ≥ 0, and ε > 0, the root factor is at least 1. -/
theorem rootFactor_one_le (z A ε : ℝ) (m : ℕ) (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    1 ≤ rootFactor z A ε m := by
  apply Real.one_le_rpow
  · have h : 0 ≤ 8 * Real.pi * z * A / ε := by positivity
    linarith
  · positivity

/-- For positive m, nonnegative z and A, and ε > 0, the 2m-th power of the root factor equals 1
+ 8πzA/ε. -/
theorem rootFactor_pow (z A ε : ℝ) (m : ℕ) (hm : 0 < m)
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    rootFactor z A ε m ^ (2 * m) = 1 + 8 * Real.pi * z * A / ε :=
  Real.rpow_inv_natCast_pow (by positivity) (by omega)

/-- The real segment count is at least 2z times the root factor. -/
theorem count_lower (z A ε : ℝ) (m : ℕ) :
    2 * z * rootFactor z A ε m ≤ (count z A ε m : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (2 * z * rootFactor z A ε m))))

/-- For z > 0, A ≥ 0, and ε > 0, the segment count equals the ceiling of 2z times the root
factor. -/
theorem count_eq_ceil (z A ε : ℝ) (m : ℕ) (hz : 0 < z) (hA : 0 ≤ A) (hε : 0 < ε) :
    count z A ε m = Nat.ceil (2 * z * rootFactor z A ε m) := by
  have hr : 0 < 2 * z * rootFactor z A ε m :=
    mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (rootFactor_one_le z A ε m hz.le hA hε))
  exact max_eq_right (Nat.succ_le_iff.mpr (Nat.ceil_pos.mpr hr))

/-- At zero scaled time, the segment count is 1. -/
theorem count_zero (A ε : ℝ) (m : ℕ) : count 0 A ε m = 1 := by
  simp [count]

/-- For z ≥ 0, A ≥ 0, and ε > 0, the real segment count is at most 2z times the root factor plus
1. -/
theorem count_upper (z A ε : ℝ) (m : ℕ) (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    (count z A ε m : ℝ) ≤ 2 * z * rootFactor z A ε m + 1 := by
  by_cases hz0 : z = 0
  · subst z
    rw [count_zero]
    norm_num
  · rw [count_eq_ceil z A ε m (lt_of_le_of_ne hz (Ne.symm hz0)) hA hε]
    have hR := rootFactor_one_le z A ε m hz hA hε
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * z * rootFactor z A ε m)).le

/-- The scaled time per segment multiplied by the root factor is at most 1/2. -/
theorem scaled_step (z A ε : ℝ) (m : ℕ) :
    (z / (count z A ε m : ℝ)) * rootFactor z A ε m ≤ 1 / 2 := by
  have hr : 0 < (count z A ε m : ℝ) := by exact_mod_cast count_pos z A ε m
  calc
    _ = (z * rootFactor z A ε m) / (count z A ε m : ℝ) := by ring
    _ ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith [count_lower z A ε m])

/-- For nonnegative z and A and positive ε, the scaled time per segment is at most 1/2. -/
theorem step_control (z A ε : ℝ) (m : ℕ) (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    z / (count z A ε m : ℝ) ≤ 1 / 2 := by
  have hr : 0 ≤ z / (count z A ε m : ℝ) := by positivity
  exact (le_mul_of_one_le_right hr (rootFactor_one_le z A ε m hz hA hε)).trans
    (scaled_step z A ε m)

/-- For positive m, nonnegative z and A, and positive ε, the segment count times
(8/3)A(z/count)^(2m + 1) is at most ε/(12π). -/
theorem accumulated_local (z A ε : ℝ) (m : ℕ) (hm : 0 < m)
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hε : 0 < ε) :
    (count z A ε m : ℝ) * ((8 / 3 : ℝ) * A * (z / (count z A ε m : ℝ)) ^ (2 * m + 1)) ≤
      ε / (12 * Real.pi) := by
  let r : ℝ := count z A ε m
  let b := z / r
  let R := rootFactor z A ε m
  let B := 1 + 8 * Real.pi * z * A / ε
  have hr : 0 < r := by
    change 0 < (count z A ε m : ℝ)
    exact_mod_cast count_pos z A ε m
  have hb : 0 ≤ b := div_nonneg hz hr.le
  have hR : 0 ≤ R := (rootFactor_one_le z A ε m hz hA hε).trans' (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hpow : b ^ (2 * m) * B ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (mul_nonneg hb hR) (scaled_step z A ε m) (2 * m)
    rw [mul_pow, rootFactor_pow z A ε m hm hz hA hε] at h
    have hsmall : (1 / 2 : ℝ) ^ (2 * m) ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact h.trans (by norm_num at hsmall ⊢; exact hsmall)
  have hscale : r * b ^ (2 * m + 1) = z * b ^ (2 * m) := by
    rw [pow_succ]
    dsimp [b]
    field_simp
  have hbudget : (r * ((8 / 3 : ℝ) * A * b ^ (2 * m + 1))) * B ≤ (2 / 3 : ℝ) * A * z := by
    calc
      _ = ((8 / 3 : ℝ) * A * B) * (r * b ^ (2 * m + 1)) := by ring
      _ = ((8 / 3 : ℝ) * A * z) * (b ^ (2 * m) * B) := by rw [hscale]; ring
      _ ≤ ((8 / 3 : ℝ) * A * z) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hright : (2 / 3 : ℝ) * A * z ≤ (ε / (12 * Real.pi)) * B := by
    have he : (ε / (12 * Real.pi)) * B = ε / (12 * Real.pi) + (2 / 3 : ℝ) * A * z := by
      dsimp [B]
      field_simp
      ring
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  exact (mul_le_mul_iff_left₀ hB).mp (hbudget.trans hright)

end Qatlib.Papers.CommutLCHS26.MainResults.MPFSegments
