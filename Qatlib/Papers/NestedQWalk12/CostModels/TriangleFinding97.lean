/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The 9/7 triangle-finding cost expression

This module evaluates `triangleCost97`, the scalar cost expression associated with Theorem 3.5
of [JefferyKothariMagniez2013]. At r1 = n^(4/7) and r2 = n^(5/7), its setup, inner-update, and
checking terms equal n^(9/7), while the outer-update term equals n^(17/14).

The exact value is 3 * n^(9/7) + n^(17/14) for positive n. For n ≥ 1, the latter term is also
bounded by n^(9/7), giving a uniform constant-four bound on the expression.

## Main statements

* `theorem35_cost_eval`: the exact substituted cost.
* `theorem35_cost_bound`: the explicit bound by 4 * n^(9/7).
* `theorem35_bigO`: a positive uniform constant for the exponent 9/7.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option autoImplicit false
noncomputable section

open scoped Real BigOperators

namespace Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding97

/-- The scalar cost r1 * r2 + sqrt(n) * r2 + n * sqrt(r1) + n^(3/2)/(r1^(1/6) * r2^(1/6)) for
the 9/7 triangle-finding parameter calculation. -/
def triangleCost97 (n r1 r2 : ℝ) : ℝ :=
  r1 * r2 + Real.sqrt n * r2 + n * Real.sqrt r1
    + n ^ (3 / 2 : ℝ) / (r1 ^ (1 / 6 : ℝ) * r2 ^ (1 / 6 : ℝ))

/-- For positive n, the setup term at r1 = n^(4/7) and r2 = n^(5/7) equals n^(9/7). -/
theorem term97_setup {n : ℝ} (hn : 0 < n) :
    n ^ (4 / 7 : ℝ) * n ^ (5 / 7 : ℝ) = n ^ (9 / 7 : ℝ) := by
  rw [← Real.rpow_add hn]
  norm_num

/-- For positive n, the outer-update term at r2 = n^(5/7) equals n^(17/14). -/
theorem term97_outer_update {n : ℝ} (hn : 0 < n) :
    Real.sqrt n * n ^ (5 / 7 : ℝ) = n ^ (17 / 14 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  norm_num

/-- For positive n, the inner-update term at r1 = n^(4/7) equals n^(9/7). -/
theorem term97_inner_update {n : ℝ} (hn : 0 < n) :
    n * Real.sqrt (n ^ (4 / 7 : ℝ)) = n ^ (9 / 7 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  norm_num
  rw [show (9 / 7 : ℝ) = 1 + 2 / 7 by norm_num,
    Real.rpow_add hn, Real.rpow_one]

/-- For positive n, the checking term at r1 = n^(4/7) and r2 = n^(5/7) equals n^(9/7). -/
theorem term97_checking {n : ℝ} (hn : 0 < n) :
    n ^ (3 / 2 : ℝ) /
        ((n ^ (4 / 7 : ℝ)) ^ (1 / 6 : ℝ) * (n ^ (5 / 7 : ℝ)) ^ (1 / 6 : ℝ)) =
      n ^ (9 / 7 : ℝ) := by
  rw [← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le]
  norm_num
  rw [← Real.rpow_add hn]
  norm_num
  rw [← Real.rpow_sub hn]
  norm_num

/-- For positive n, the defined cost at r1 = n^(4/7) and r2 = n^(5/7) equals 3 * n^(9/7) +
n^(17/14), giving the scalar evaluation associated with [Jeffery et al., Theorem
3.5][JefferyKothariMagniez2013]. -/
theorem theorem35_cost_eval {n : ℝ} (hn : 0 < n) :
    triangleCost97 n (n ^ (4 / 7 : ℝ)) (n ^ (5 / 7 : ℝ)) =
      3 * n ^ (9 / 7 : ℝ) + n ^ (17 / 14 : ℝ) := by
  unfold triangleCost97
  rw [term97_setup hn, term97_outer_update hn, term97_inner_update hn,
    term97_checking hn]
  ring

/-- For n ≥ 1, the defined triangle cost at r1 = n^(4/7) and r2 = n^(5/7) is at most 4 *
n^(9/7), as in the scalar cost analysis of [JefferyKothariMagniez2013]. -/
theorem theorem35_cost_bound {n : ℝ} (hn : 1 ≤ n) :
    triangleCost97 n (n ^ (4 / 7 : ℝ)) (n ^ (5 / 7 : ℝ)) ≤
      4 * n ^ (9 / 7 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rw [theorem35_cost_eval hn0]
  have hle : n ^ (17 / 14 : ℝ) ≤ n ^ (9 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

  nlinarith [hle]

/-- A positive uniform constant bounds the substituted scalar triangle cost by that constant
times n^(9/7) for n ≥ 1, as in the cost calculation for [Jeffery et al., Theorem
3.5][JefferyKothariMagniez2013]. -/
theorem theorem35_bigO :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℝ, 1 ≤ n →
      triangleCost97 n (n ^ (4 / 7 : ℝ)) (n ^ (5 / 7 : ℝ)) ≤
        c * n ^ (9 / 7 : ℝ) :=
  ⟨4, by norm_num, fun n hn => theorem35_cost_bound hn⟩

end Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding97
