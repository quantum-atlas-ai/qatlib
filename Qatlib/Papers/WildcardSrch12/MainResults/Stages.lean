/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WildcardSrch12.MainResults.Model.GramOverlap

@[expose] public section


/-! Preserved closed mathematical components; no credit for deferred source algorithms. -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators


namespace Qatlib.Papers.WildcardSrch12.MainResults.SearchWithWildcards

open Qatlib.Papers.WildcardSrch12.MainResults

/-- The paper's stage recurrence `n_{i-1} = ⌈n_i − √n_i⌉` (§2, p. 4). -/
def stageNext (m : ℕ) : ℕ := ⌈(m : ℝ) - Real.sqrt (m : ℝ)⌉₊


/-- The stage sizes are nonincreasing (§2, p. 4); strict decrease and a stage-count
bound require separate estimates. -/
theorem stageNext_le_self (m : ℕ) : stageNext m ≤ m := by
  unfold stageNext
  rw [Nat.ceil_le]
  have h : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  linarith


/-- Query accounting of Theorem 1 (§2, p. 4): a Stage-0 cost of at most `√n` queries
plus `l ≤ √n` later stages, each costing `c` expected queries, totals at most
`(1 + c)·√n`.  With `c = O(log n)` this is the paper's `O(√n log n)`. -/
theorem stage_query_accounting {n0 l : ℕ} {n : ℕ} {c : ℝ}
    (h0 : (n0 : ℝ) ≤ Real.sqrt (n : ℝ)) (hl : (l : ℝ) ≤ Real.sqrt (n : ℝ))
    (hc : 0 ≤ c) :
    (n0 : ℝ) + (l : ℝ) * c ≤ (1 + c) * Real.sqrt (n : ℝ) := by
  have h1 : (l : ℝ) * c ≤ Real.sqrt (n : ℝ) * c := by
    exact mul_le_mul_of_nonneg_right hl hc
  nlinarith


end Qatlib.Papers.WildcardSrch12.MainResults.SearchWithWildcards
