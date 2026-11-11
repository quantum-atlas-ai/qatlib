/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The 35/27 triangle-finding cost expression

This module evaluates `triangleCost35`, the scalar cost expression associated with Theorem 3.4
of [JefferyKothariMagniez2013]. Substituting r = n^(2/3) and s = n^(-1/27) makes the setup,
outer-update, and checking terms each equal n^(35/27).

The complete expression equals 3 * n^(35/27) + n for positive n, and is at most 4 * n^(35/27)
for n ≥ 1. These are bounds on the defined scalar expression.

## Main statements

* `theorem34_cost_eval`: exact evaluation at the specified parameters.
* `theorem34_cost_bound`: the explicit constant-four bound.
* `theorem34_bigO`: a uniform positive-constant bound with exponent 35/27.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option autoImplicit false
noncomputable section

open scoped Real

namespace Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding35

/-- The scalar cost s * r² + n * s * sqrt(r) + n + n^(3/2)/(sqrt(s) * r^(1/3)) for the 35/27
triangle-finding parameter calculation. -/
def triangleCost35 (n r s : ℝ) : ℝ :=
  s * r ^ 2 + n * s * Real.sqrt r + n + n ^ (3 / 2 : ℝ) / (Real.sqrt s * r ^ (1 / 3 : ℝ))

/-- For positive n, the setup term at r = n^(2/3) and s = n^(-1/27) equals n^(35/27). -/
theorem term_setup {n : ℝ} (hn : 0 < n) :
    n ^ (-(1 / 27) : ℝ) * (n ^ (2 / 3 : ℝ)) ^ 2 = n ^ (35 / 27 : ℝ) := by
  rw [pow_two, ← Real.rpow_add hn]
  norm_num
  rw [show (35 / 27 : ℝ) = -(1 / 27) + 4 / 3 by norm_num, Real.rpow_add hn]

/-- For positive n, the outer-update term at r = n^(2/3) and s = n^(-1/27) equals n^(35/27). -/
theorem term_outer_update {n : ℝ} (hn : 0 < n) :
    n * n ^ (-(1 / 27) : ℝ) * Real.sqrt (n ^ (2 / 3 : ℝ)) = n ^ (35 / 27 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  norm_num
  rw [show (35 / 27 : ℝ) = 1 + (-(1 / 27) + 1 / 3) by norm_num,
    Real.rpow_add hn, Real.rpow_one, Real.rpow_add hn]
  ring

/-- For positive n, the checking term at r = n^(2/3) and s = n^(-1/27) equals n^(35/27). -/
theorem term_checking {n : ℝ} (hn : 0 < n) :
    n ^ (3 / 2 : ℝ) /
        (Real.sqrt (n ^ (-(1 / 27) : ℝ)) * (n ^ (2 / 3 : ℝ)) ^ (1 / 3 : ℝ)) =
      n ^ (35 / 27 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le]
  norm_num
  rw [← Real.rpow_add hn]
  norm_num
  rw [← Real.rpow_sub hn]
  norm_num

/-- For positive n, the defined triangle cost at r = n^(2/3) and s = n^(-1/27) equals 3 *
n^(35/27) + n, giving the scalar evaluation associated with [Jeffery et al., Theorem
3.4][JefferyKothariMagniez2013]. -/
theorem theorem34_cost_eval {n : ℝ} (hn : 0 < n) :
    triangleCost35 n (n ^ (2 / 3 : ℝ)) (n ^ (-(1 / 27) : ℝ)) =
      3 * n ^ (35 / 27 : ℝ) + n := by
  unfold triangleCost35
  rw [term_setup hn, term_outer_update hn, term_checking hn]
  ring

/-- For n ≥ 1, the defined triangle cost at r = n^(2/3) and s = n^(-1/27) is at most 4 *
n^(35/27). -/
theorem theorem34_cost_bound {n : ℝ} (hn : 1 ≤ n) :
    triangleCost35 n (n ^ (2 / 3 : ℝ)) (n ^ (-(1 / 27) : ℝ)) ≤
      4 * n ^ (35 / 27 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rw [theorem34_cost_eval hn0]
  have hnle : n ≤ n ^ (35 / 27 : ℝ) := by
    rw [show (35 / 27 : ℝ) = 1 + 8 / 27 by norm_num,
      Real.rpow_add hn0, Real.rpow_one]
    exact le_mul_of_one_le_right hn0.le
      (Real.one_le_rpow hn (by norm_num : (0 : ℝ) ≤ 8 / 27))
  nlinarith [hnle]

/-- A positive uniform constant bounds the substituted scalar triangle cost by that constant
times n^(35/27) for n ≥ 1, as in the cost calculation for [Jeffery et al., Theorem
3.4][JefferyKothariMagniez2013]. -/
theorem theorem34_bigO :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℝ, 1 ≤ n →
      triangleCost35 n (n ^ (2 / 3 : ℝ)) (n ^ (-(1 / 27) : ℝ)) ≤
        c * n ^ (35 / 27 : ℝ) :=
  ⟨4, by norm_num, fun n hn => theorem34_cost_bound hn⟩

end Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding35
