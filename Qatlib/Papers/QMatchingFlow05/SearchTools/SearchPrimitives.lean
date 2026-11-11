/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs

/-!
# Enumeration costs and repeated failure bounds

This module records scalar enumeration and counting costs and elementary repetition bounds for
the search tools in [AmbainisSpalek2006]. The enumeration expression factors into `(√k + 1) *
√l`, and the counting cost is bounded by a linear expression for `n ≥ 1`.

The quantity `repeatFailure r` is `3 ^ (-r)` expressed as `(1 / 3) ^ r`. A supplied inequality
`t * n ≤ 3 ^ r` gives the union-bound and complementary success expressions.

## Main statements

* `enumCost_le_two_mul`: a linear bound on the enumeration expression.
* `countCost_le_linear`: a linear bound on the counting expression.
* `amplified_union_bound`: bounds `t` times the repeated failure expression by `1 / n`.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.SearchTools

/-- The enumeration-cost expression `c * (√(k * l) + √l)`. -/
def enumCost (c k l : ℝ) : ℝ := c * (Real.sqrt (k * l) + Real.sqrt l)

/-- For nonnegative `k` and `l`, the enumeration cost equals `c * (√k + 1) * √l`. See
[AmbainisSpalek2006]. -/
theorem enumCost_eq (c k l : ℝ) (hk : 0 ≤ k) (_hl : 0 ≤ l) :
    enumCost c k l = c * (Real.sqrt k + 1) * Real.sqrt l := by
  unfold enumCost
  rw [Real.sqrt_mul hk]
  ring

/-- For `c ≥ 0`, `0 ≤ k ≤ l`, and `l ≥ 1`, the enumeration cost is at most `2 * c * l`. See
[AmbainisSpalek2006]. -/
theorem enumCost_le_two_mul (c k l : ℝ) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hkl : k ≤ l) (hl1 : 1 ≤ l) :
    enumCost c k l ≤ 2 * c * l := by
  have hl : (0 : ℝ) ≤ l := by linarith
  have hle : k * l ≤ l * l := by nlinarith [hk, hl, hkl]
  have hsq : Real.sqrt (l * l) = l := by
    rw [show l * l = l ^ 2 by ring, Real.sqrt_sq hl]
  have h1 : Real.sqrt (k * l) ≤ l := by
    calc Real.sqrt (k * l) ≤ Real.sqrt (l * l) := Real.sqrt_le_sqrt hle
      _ = l := hsq
  have hll : l ≤ l * l := by nlinarith [hl1]
  have h2 : Real.sqrt l ≤ l := by
    calc Real.sqrt l ≤ Real.sqrt (l * l) := Real.sqrt_le_sqrt hll
      _ = l := hsq
  unfold enumCost
  nlinarith [hc, h1, h2, hl]

/-- The counting-cost expression `c * √n`. -/
def countCost (c n : ℝ) : ℝ := c * Real.sqrt n

/-- The counting-error expression `c * √n`. -/
def countError (c n : ℝ) : ℝ := c * Real.sqrt n

/-- For nonnegative `c` and `n ≥ 1`, the counting cost is at most `c * n`. See
[AmbainisSpalek2006]. -/
theorem countCost_le_linear (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    countCost c n ≤ c * n := by
  unfold countCost
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hsqrt_mul : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
  have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hn_ge : Real.sqrt n ≤ n := by nlinarith [hsqrt_mul, h1, hsq0]
  exact mul_le_mul_of_nonneg_left hn_ge hc

/-- The repeated-failure expression `(1 / 3) ^ r`. -/
def repeatFailure (r : ℕ) : ℝ := (1 / 3 : ℝ) ^ r

/-- The repeated-failure expression is nonnegative. -/
theorem repeatFailure_nonneg (r : ℕ) : 0 ≤ repeatFailure r := by
  unfold repeatFailure
  positivity

/-- If `n > 0` and `t * n ≤ 3 ^ r`, then `t * repeatFailure r ≤ 1 / n`. See
[AmbainisSpalek2006]. -/
theorem amplified_union_bound (t n r : ℕ) (hn : 0 < n)
    (hr : (t : ℝ) * (n : ℝ) ≤ (3 : ℝ) ^ r) :
    (t : ℝ) * repeatFailure r ≤ 1 / (n : ℝ) := by
  unfold repeatFailure
  have h3 : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : (1 / 3 : ℝ) ^ r = 1 / (3 : ℝ) ^ r := by
    rw [one_div, inv_pow, one_div]
  rw [hpow, one_div, one_div]
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have h3inv : (0 : ℝ) ≤ ((3 : ℝ) ^ r)⁻¹ := by positivity
  have hmul : (t : ℝ) ≤ (n : ℝ)⁻¹ * (3 : ℝ) ^ r := by
    have h1 := mul_le_mul_of_nonneg_right hr hninv
    have ht : ((t : ℝ) * (n : ℝ)) * (n : ℝ)⁻¹ = (t : ℝ) := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hn'), mul_one]
    have h2 : ((3 : ℝ) ^ r) * (n : ℝ)⁻¹ = (n : ℝ)⁻¹ * (3 : ℝ) ^ r := by ring
    rwa [ht, h2] at h1
  calc (t : ℝ) * ((3 : ℝ) ^ r)⁻¹
      ≤ ((n : ℝ)⁻¹ * (3 : ℝ) ^ r) * ((3 : ℝ) ^ r)⁻¹ :=
        mul_le_mul_of_nonneg_right hmul h3inv
    _ = (n : ℝ)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h3), mul_one]

/-- If `n > 0` and `t * n ≤ 3 ^ r`, then `1 - t * repeatFailure r ≥ 1 - 1 / n`. See
[AmbainisSpalek2006]. -/
theorem amplified_success_bound (t n r : ℕ) (hn : 0 < n)
    (hr : (t : ℝ) * (n : ℝ) ≤ (3 : ℝ) ^ r) :
    1 - (t : ℝ) * repeatFailure r ≥ 1 - 1 / (n : ℝ) := by
  have hle := amplified_union_bound t n r hn hr
  linarith

end Qatlib.Papers.QMatchingFlow05.SearchTools

end
