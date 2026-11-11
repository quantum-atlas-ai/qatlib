/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Scalar adversary bounds and search specializations

This module bounds total adversary progress from bounded one-step changes and records elementary
properties of the expression `sqrt(m * m') / l`. These scalar estimates support the
relation-based query lower-bound analysis in [Itakura2005].

The search specializations simplify the adversary expression to `sqrt n` and, for nonnegative
`n`, to `n`.

## Main statements

* `adversary_query_lower`: Bounds required total progress by the number of steps times the
  per-step bound.
* `adversary_bound_mono_m`: Proves monotonicity in a numerator parameter.
* `product_search_lower_bound`: Evaluates the product-search scalar expression.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.RelationAdv

/-- If each of the first `t` increments of `W` has absolute value at most `C` and the total
change is at least `Rcard / 8`, then `Rcard / 8 ≤ t * C`. This is the telescoping progress
estimate used for adversary bounds in [Itakura2005]. -/
theorem adversary_query_lower
    (W : ℕ → ℝ) (C Rcard : ℝ) (t : ℕ)
    (hstep : ∀ j, j < t → |W (j + 1) - W j| ≤ C)
    (hchange : Rcard / 8 ≤ |W t - W 0|) :
    Rcard / 8 ≤ (t : ℝ) * C := by
  have htel : (∑ j ∈ Finset.range t, (W (j + 1) - W j)) = W t - W 0 :=
    Finset.sum_range_sub W t
  have habs : |W t - W 0| ≤
      ∑ j ∈ Finset.range t, |W (j + 1) - W j| := by
    rw [← htel]
    exact Finset.abs_sum_le_sum_abs _ _
  have hsum : (∑ j ∈ Finset.range t, |W (j + 1) - W j|) ≤
      ∑ j ∈ Finset.range t, C := by
    apply Finset.sum_le_sum
    intro j hj
    exact hstep j (Finset.mem_range.mp hj)
  have hconst : (∑ _j ∈ Finset.range t, C) = (t : ℝ) * C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-- For nonnegative `m`, factors `sqrt(m * m')` as `sqrt m * sqrt m'`. -/
theorem adversary_bound_factor {m m' : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (m * m') = Real.sqrt m * Real.sqrt m' :=
  Real.sqrt_mul hm m'

/-- For `m ≤ m2`, nonnegative `m'`, and nonnegative `l`, increasing the first numerator
parameter does not decrease `sqrt(m * m') / l`. -/
theorem adversary_bound_mono_m {m m2 m' l : ℝ}
    (hmm : m ≤ m2) (hm' : 0 ≤ m') (hl : 0 ≤ l) :
    Real.sqrt (m * m') / l ≤ Real.sqrt (m2 * m') / l := by
  apply div_le_div_of_nonneg_right _ hl
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right hmm hm'

/-- For positive `l` and `l ≤ l2`, replacing the denominator `l` by `l2` does not increase
`sqrt(m * m') / l`. -/
theorem adversary_bound_antitone_l {m m' l l2 : ℝ}
    (hl : 0 < l) (hll : l ≤ l2) :
    Real.sqrt (m * m') / l2 ≤ Real.sqrt (m * m') / l := by
  apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hl hll

/-- The scalar adversary expression `sqrt(1 * n) / 1` simplifies to `sqrt n`, the search scale
used in [Itakura2005]. -/
theorem or_search_lower_bound (n : ℝ) :
    Real.sqrt (1 * n) / 1 = Real.sqrt n := by
  rw [one_mul, div_one]

/-- For nonnegative `n`, the scalar expression `sqrt(n * n) / 1` equals `n`. -/
theorem product_search_lower_bound (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt (n * n) / 1 = n := by
  rw [div_one, Real.sqrt_mul_self hn]

end Qatlib.Papers.CommuteTest05.RelationAdv
