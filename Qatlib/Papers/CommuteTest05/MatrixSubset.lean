/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Counting subsets containing a fixed pair

This module proves the binomial identities for the fraction of `r`-subsets of a `k`-element set
that contain a specified pair, as used for matrix-subset marking in [Itakura2005]. The
real-valued fraction is `r * (r - 1) / (k * (k - 1))` when `2 ≤ r ≤ k`.

## Main statements

* `choose_marked_fraction`: Evaluates the fixed-pair inclusion fraction.
* `choose_marked_le_one`: Bounds the resulting fraction by one.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MatrixSubset

/-- For natural `k` and `r ≥ 2`, relates `choose k r * r * (r - 1)` to `k * (k - 1) * choose (k
- 2) (r - 2)`, with all factors interpreted in the reals. -/
theorem choose_marked_mul (k r : ℕ) (hr2 : 2 ≤ r) :
    (Nat.choose k r : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) =
      ((k : ℝ) * ((k : ℝ) - 1)) * (Nat.choose (k - 2) (r - 2) : ℝ) := by
  have h := Nat.choose_mul (n := k) (k := r) (s := 2) hr2
  have hcast : (Nat.choose k r : ℝ) * (Nat.choose r 2 : ℝ) =
      (Nat.choose k 2 : ℝ) * (Nat.choose (k - 2) (r - 2) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hcast
  nlinarith [hcast]

/-- For `2 ≤ r ≤ k`, the fraction of `r`-subsets containing a fixed pair is `choose (k - 2) (r -
2) / choose k r = r * (r - 1) / (k * (k - 1))`. This is the marking fraction used in
Algorithm 4 of [Itakura2005]. -/
theorem choose_marked_fraction (k r : ℕ) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    (Nat.choose (k - 2) (r - 2) : ℝ) / (Nat.choose k r : ℝ) =
      ((r : ℝ) * ((r : ℝ) - 1)) / ((k : ℝ) * ((k : ℝ) - 1)) := by
  have hmul := choose_marked_mul k r hr2
  have hk2 : 2 ≤ k := le_trans hr2 hrk
  have hkr : (Nat.choose k r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hrk).ne'
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk2).trans_le (le_refl (k : ℕ))
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hk2)
    linarith
  have hk : ((k : ℝ) * ((k : ℝ) - 1)) ≠ 0 := by
    exact (mul_pos hkpos hk1).ne'
  field_simp [hkr, hk]
  linarith [hmul]

/-- For `2 ≤ r ≤ k`, the real-valued fixed-pair inclusion fraction `r * (r - 1) / (k * (k - 1))`
is at most one, as used in [Itakura2005]. -/
theorem choose_marked_le_one (k r : ℕ) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    ((r : ℝ) * ((r : ℝ) - 1)) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 := by
  have hk2 : 2 ≤ k := le_trans hr2 hrk
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk2).trans_le (le_refl (k : ℕ))
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hk2)
    linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := mul_pos hkpos hk1
  have hrle : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hr1le : (r : ℝ) - 1 ≤ (k : ℝ) - 1 := by linarith
  have hr1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ r := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hr2)
    linarith
  have hnum : (r : ℝ) * ((r : ℝ) - 1) ≤ (k : ℝ) * ((k : ℝ) - 1) :=
    mul_le_mul hrle hr1le hr1 hkpos.le
  rw [div_le_one hden]
  exact hnum

end Qatlib.Papers.CommuteTest05.MatrixSubset
