/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.MainResults.CostBounds

@[expose] public section

/-!
# Algorithm 6 cost accounting at `r = s`

Section 3.2.3 of [Itakura2005] totals the Algorithm 6 setup and update costs as
`r * s * n + (k * n / (r * s)) * sqrt (max r s) * (r * n + s * n)`. At the balanced choice
`r = s` this module identifies the printed form with the published cost expression
`Qatlib.Papers.CommuteTest05.MainResults.CostBounds.alg6Cost`.

Both statements are equalities over the paper's own cost ledger. They do not model the caching
process that would produce the individual query counts, and the balanced feasibility window
`k ^ (2 / 3) ≲ n ≲ k ^ (3 / 2)` is a separate arithmetic statement not proved here.

## Main statements

* `alg6_T_eq`: at `r = s` the walk factor `(k * n / (r * s)) * sqrt (max r s)` equals
  `k * n / r ^ (3 / 2)`.
* `alg6Cost_from_accounting`: the printed setup and update total equals `alg6Cost`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults

open Qatlib.Papers.CommuteTest05.MainResults.CostBounds

/-- At `r = s`, the Algorithm 6 walk factor `(k * n / (r * s)) * sqrt (max r s)` equals
`k * n / r ^ (3 / 2)`. -/
theorem alg6_T_eq (k n r s : ℝ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (hrs : r = s) :
    k * n / (r * s) * Real.sqrt (max r s) = k * n / r ^ ((3 : ℝ) / 2) := by
  subst hrs
  rw [max_self, eq_div_iff (by positivity : r ^ ((3 : ℝ) / 2) ≠ 0)]
  have hr32 : r ^ ((3 : ℝ) / 2) = r * Real.sqrt r := by
    have h : r ^ (1 : ℝ) * r ^ ((1 : ℝ) / 2) = r ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add hr]
      norm_num
    rw [Real.sqrt_eq_rpow, ← h, Real.rpow_one]
  rw [hr32]
  conv_lhs => rw [div_mul_eq_mul_div]
  field_simp
  rw [Real.sq_sqrt hr.le]

/-- The Algorithm 6 setup and update total at `r = s` reproduces the published cost expression
`alg6Cost`. -/
theorem alg6Cost_from_accounting (k n r : ℝ) (_hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    r * r * n + k * n / (r * r) * Real.sqrt (max r r) * (r * n + r * n) =
      alg6Cost k n r := by
  rw [max_self]
  unfold alg6Cost
  field_simp
  ring_nf
  rw [Real.sq_sqrt hr.le]

end Qatlib.Papers.CommuteTest05.MainResults
