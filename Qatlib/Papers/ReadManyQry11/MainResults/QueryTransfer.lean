/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ReadManyQry11.MainResults.SourceModel

@[expose] public section

/-!
# Combining bounded-error query programs for read-many formulas

A witness to an upper bound carries its workspace, decision program and actual query
count. Enlarging the budget preserves the same witness, and successive transfers preserve
the common budget. To combine the three algorithms in Theorem 2, choose the witness for
the least of the three budgets.
-/

set_option autoImplicit false

open Qatlib.Papers.ReadManyQry11.MainResults

namespace Qatlib.Papers.ReadManyQry11.MainResults

/-- Increasing the upper budget preserves the same bounded-error decision program. -/
theorem query_budget_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {b b' : ℝ}
    (h : b ≤ b') (hb : BoundedErrorQueryAtMost f b) : BoundedErrorQueryAtMost f b' := by
  obtain ⟨W, hW, hEq, P, hcorrect, hcost⟩ := hb
  exact ⟨W, hW, hEq, P, hcorrect, hcost.trans h⟩

/-- Two consecutive reductions transfer a bounded-error budget to the final function. -/
theorem query_reduction_trans {n m k : ℕ} {f : (Fin n → Bool) → Bool}
    {g : (Fin m → Bool) → Bool} {h : (Fin k → Bool) → Bool}
    (hgf : QueryReduction g f) (hhg : QueryReduction h g) : QueryReduction h f := by
  exact fun b hb => hgf b (hhg b hb)

/-- The three-term benchmark is positive on formulas with positive size and gate count
and at least two inputs. -/
theorem main_bound_pos (n S G : ℕ) (hn : 2 ≤ n) (hS : 1 ≤ S) (hG : 1 ≤ G) :
    0 < mainBound n S G := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS' : (0 : ℝ) < S := by exact_mod_cast (show 0 < S by omega)
  have hG' : (0 : ℝ) < G := by exact_mod_cast (show 0 < G by omega)
  simp only [mainBound, min3, lt_min_iff, pruningBound]
  exact ⟨hn', Real.sqrt_pos.2 hS',
    mul_pos (Real.rpow_pos_of_pos hn' _) (Real.rpow_pos_of_pos hG' _)⟩

/-- Theorem 2's minimum-budget step, given three programs bounded with a common
constant in the three source query budgets. -/
theorem query_budget_min {n S G : ℕ} {f : (Fin n → Bool) → Bool} {C : ℝ}
    (hread : BoundedErrorQueryAtMost f (C * n))
    (hsize : BoundedErrorQueryAtMost f (C * Real.sqrt S))
    (hprune : BoundedErrorQueryAtMost f (C * pruningBound n G)) :
    BoundedErrorQueryAtMost f (C * mainBound n S G) := by
  unfold mainBound min3
  by_cases hn : (n : ℝ) ≤ min (Real.sqrt S) (pruningBound n G)
  · simpa only [min_eq_left hn] using hread
  rw [min_eq_right (le_of_not_ge hn)]
  by_cases hs : Real.sqrt (S : ℝ) ≤ pruningBound n G
  · simpa only [min_eq_left hs] using hsize
  · simpa only [min_eq_right (le_of_not_ge hs)] using hprune

end Qatlib.Papers.ReadManyQry11.MainResults
