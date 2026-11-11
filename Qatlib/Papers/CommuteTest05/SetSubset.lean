/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Scalar bounds for subset-based search

This module compares setup and search-cost expressions for subset-based commutativity testing in
[Itakura2005]. It bounds a restricted setup cost by full reading, simplifies a pair-search
square root, compares two outer-search scales, and factors a lower-bound expression.

## Main statements

* `alg7_setup_le_full_read`: Bounds setup under the stated subset-size inequalities.
* `element_distinctness_outer_le`: Compares the element-distinctness outer scale with the linear
  outer scale.
* `set_lower_bound_eq`: Simplifies the square-root lower-bound expression.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.SetSubset

/-- For the stated nonnegative size parameters and inequalities `t ≤ m`, `r ≤ k`, and `s ≤ n`,
the setup expression `t * r * s * n` is at most `m * k * n ^ 2`. This is a setup comparison
for Algorithm 7 of [Itakura2005]. -/
theorem alg7_setup_le_full_read (m k n t r s : ℝ)
    (hm : 0 ≤ m) (hk : 0 ≤ k) (hn : 0 ≤ n) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (htm : t ≤ m) (hrk : r ≤ k) (hsn : s ≤ n) :
    t * r * s * n ≤ m * k * n ^ 2 := by
  have hmk : 0 ≤ m * k := mul_nonneg hm hk
  have h1 : t * r ≤ m * k := mul_le_mul htm hrk hr hm
  have h2 : t * r * s ≤ m * k * n := mul_le_mul h1 hsn hs hmk
  have h3 : t * r * s * n ≤ m * k * n * n :=
    mul_le_mul h2 (le_refl n) hn (mul_nonneg hmk hn)
  nlinarith [h3]

/-- For nonnegative `m` and `k`, `sqrt(m ^ 2 * k ^ 2) = m * k`. -/
theorem grover_pair_iterations (m k : ℝ) (hm : 0 ≤ m) (hk : 0 ≤ k) :
    Real.sqrt (m ^ 2 * k ^ 2) = m * k := by
  rw [show m ^ 2 * k ^ 2 = (m * k) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hm hk)]

/-- For nonnegative `m` and `k`, the pair-search cost expression simplifies to `m * k * n ^ (5 /
3)`, as used in [Itakura2005]. -/
theorem grover_pair_search_cost (m k n : ℝ) (hm : 0 ≤ m) (hk : 0 ≤ k) :
    Real.sqrt (m ^ 2 * k ^ 2) * n ^ ((5 : ℝ) / 3) = m * k * n ^ ((5 : ℝ) / 3) := by
  rw [grover_pair_iterations m k hm hk]

/-- For `m ≥ 1` and nonnegative `k` and `n`, the outer scale `m ^ (2 / 3) * k * n ^ (5 / 3)` is
at most `m * k * n ^ (5 / 3)`. This compares the search expressions in [Itakura2005]. -/
theorem element_distinctness_outer_le (m k n : ℝ) (hm : 1 ≤ m) (hk : 0 ≤ k) (hn : 0 ≤ n) :
    m ^ ((2 : ℝ) / 3) * k * n ^ ((5 : ℝ) / 3) ≤ m * k * n ^ ((5 : ℝ) / 3) := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hpow : m ^ ((2 : ℝ) / 3) ≤ m := by
    have h := Real.rpow_le_rpow_of_exponent_le hm (by norm_num : (2 : ℝ) / 3 ≤ 1)
    rwa [Real.rpow_one] at h
  have h1 : m ^ ((2 : ℝ) / 3) * k ≤ m * k := mul_le_mul hpow (le_refl k) hk hm0
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn _)

/-- For nonnegative `m`, `k`, and `n`, `sqrt(m / 2 * k * n ^ 2) = sqrt(m * k / 2) * n`, giving
the factored lower-bound expression used in [Itakura2005]. -/
theorem set_lower_bound_eq (m k n : ℝ) (hm : 0 ≤ m) (hk : 0 ≤ k) (hn : 0 ≤ n) :
    Real.sqrt (m / 2 * k * n ^ 2) = Real.sqrt (m * k / 2) * n := by
  have harg : m / 2 * k * n ^ 2 = (m * k / 2) * n ^ 2 := by ring
  rw [harg, Real.sqrt_mul (div_nonneg (mul_nonneg hm hk) (by norm_num)), Real.sqrt_sq hn]

end Qatlib.Papers.CommuteTest05.SetSubset
