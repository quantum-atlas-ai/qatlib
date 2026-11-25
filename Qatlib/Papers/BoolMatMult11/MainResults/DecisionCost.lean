/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolMatMult11.MainResults.GraphCollision.DegreeCounting

@[expose] public section

/-!
# Decision cost of graph collision

The decision specialization of Theorem 3.1 replaces the listing
search by a single search. The scalar budget charges the two
square-root-of-n terms and the branch reading term separately.
-/

set_option autoImplicit false

open Qatlib.Papers.BoolMatMult11.MainResults.GraphCollision

namespace Qatlib.Papers.BoolMatMult11.MainResults

/-- The decision ledger has a square-root bound independent of the
number of marked collisions. -/
theorem gc_decision_cost_bound_lambda_free (n m : ℕ) :
    2 * Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) ≤
      3 * (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) := by
  linarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg (m : ℝ)]

/-- Paying for the actual c non-neighbors in the read branch stays
within the same decision budget when the branch's test holds. -/
theorem gc_read_branch_cost_le (n m c : ℕ) (hc : c * c ≤ m) :
    2 * Real.sqrt (n : ℝ) + (c : ℝ) ≤
      3 * (Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ)) :=
  (add_le_add le_rfl (case1_read_cost_le hc)).trans
    (gc_decision_cost_bound_lambda_free n m)

end Qatlib.Papers.BoolMatMult11.MainResults
