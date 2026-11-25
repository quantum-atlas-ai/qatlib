/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.MainResults.CostBounds

@[expose] public section

/-!
# Algorithm 5 cost accounting

Section 3.2.2 of [Itakura2005] states an update cost `O(n)`, a checking cost of zero, a
discrimination gap `δ ≥ 1 / r`, and an error `ε = r ^ 4 / (n ^ 4 * k ^ 4)`. Feeding these into
the Szegedy time `1 / sqrt (δ * ε)` gives the walk factor `n ^ 3 * k ^ 2 / r ^ (3 / 2)`, which is
the second summand of the Algorithm 5 cost expression already published as
`Qatlib.Papers.CommuteTest05.MainResults.CostBounds.alg5Cost`.

This module supplies the missing algebraic link from the paper's stated `δ` and `ε` to that
expression. The walk itself and the query counts of the setup, update and checking steps are not
constructed here.

## Main statements

* `szegedyTime_alg5`: the Szegedy time at the stated `δ` and `ε`, multiplied by the `n` update
  factor, equals `n ^ 3 * k ^ 2 / r ^ (3 / 2)`.
* `alg5Cost_from_accounting`: the setup term plus the walk term reproduces `alg5Cost`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults

open Qatlib.Papers.CommuteTest05.MainResults.CostBounds

/-- For positive `k`, `n` and `r`, the Szegedy time at the Algorithm 5 parameters
`δ = 1 / r` and `ε = r ^ 4 / (n ^ 4 * k ^ 4)`, multiplied by the `n` update factor, equals
`n ^ 3 * k ^ 2 / r ^ (3 / 2)`. -/
theorem szegedyTime_alg5 (k n r : ℝ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    szegedyTime (1 / r) (r ^ 4 / (n ^ 4 * k ^ 4)) * n =
      n ^ 3 * k ^ 2 / r ^ ((3 : ℝ) / 2) := by
  unfold szegedyTime
  have hsq : (r ^ ((3 : ℝ) / 2) / (n ^ 2 * k ^ 2)) ^ 2 =
      (1 / r) * (r ^ 4 / (n ^ 4 * k ^ 4)) := by
    have h1 : (r ^ ((3 : ℝ) / 2)) ^ 2 = r ^ 3 := by
      rw [← Real.rpow_natCast (r ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hr.le]
      rw [show (3 : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have h2 : (n ^ 2 * k ^ 2) ^ 2 = n ^ 4 * k ^ 4 := by ring
    rw [div_pow, h1, h2]
    field_simp
  have hpos : 0 ≤ r ^ ((3 : ℝ) / 2) / (n ^ 2 * k ^ 2) := by positivity
  have hsqrt : Real.sqrt ((1 / r) * (r ^ 4 / (n ^ 4 * k ^ 4))) =
      r ^ ((3 : ℝ) / 2) / (n ^ 2 * k ^ 2) := by
    rw [← hsq, Real.sqrt_sq hpos]
  rw [hsqrt]
  field_simp

/-- The Algorithm 5 setup term `r * n` plus the walk term from the stated `δ` and `ε` reproduces
the published cost expression `alg5Cost`. -/
theorem alg5Cost_from_accounting (k n r : ℝ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r) :
    r * n + szegedyTime (1 / r) (r ^ 4 / (n ^ 4 * k ^ 4)) * n = alg5Cost k n r := by
  rw [szegedyTime_alg5 k n r hk hn hr]
  unfold alg5Cost
  rfl

end Qatlib.Papers.CommuteTest05.MainResults
