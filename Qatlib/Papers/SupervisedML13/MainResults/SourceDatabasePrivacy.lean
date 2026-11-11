/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c007 — database privacy with `O(log(MN))` queries

Fixed arXiv:1307.0411v2, p. 2 (Introduction) and p. 6 (Discussion):
cluster assignment requires only `O(log(MN))` calls to the quantum database,
while uncovering the actual data requires `O(MN)` calls, so the user accesses
an exponentially small fraction of the database.

The Lean statements record (i) the logarithmic shape of the assignment query
count, and (ii) the query-count separation from full database readout in the
large-data regime `M, N ≥ 4`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- A logarithmic bound used for the privacy comparison: for `1 ≤ x`,
`log₂ x ≤ 2 (x - 1)`.

Proof: `log₂ x = log x / log 2`, `log 2 > 0.69 > 1/2`, so
`1 / log 2 < 2` and hence `log₂ x < 2 log x ≤ 2 (x - 1)` by
`Real.log_le_sub_one_of_pos`. -/
theorem logb_two_le_two_mul_sub_one {x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 x ≤ 2 * (x - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlog2pos : 0 < Real.log 2 := lt_trans (by norm_num) hlog2
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hinv : (Real.log 2)⁻¹ < 2 := by
    have := (inv_lt_inv₀ hlog2pos (show (0 : ℝ) < 1 / 2 by norm_num)).2 hlog2
    simpa using this
  rw [Real.logb, div_eq_mul_inv]
  calc Real.log x * (Real.log 2)⁻¹ ≤ Real.log x * 2 :=
        mul_le_mul_of_nonneg_left (le_of_lt hinv) hlogx
    _ = 2 * Real.log x := by ring
    _ ≤ 2 * (x - 1) := by
        have h := Real.log_le_sub_one_of_pos hx0
        linarith

/-- **c007** (paper p. 2, p. 6).  For positive `M`, `N` the assignment query
count `log₂ M + log₂ N + 2` equals `log₂(M·N) + 2`, the paper's
`O(log(MN))`.

Source: arXiv:1307.0411v2 p. 2 "only `O(log(MN))` calls to the quantum
data-base are required to perform cluster assignment". -/
theorem assignment_database_queries_logb (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    assignmentDatabaseQueries M N
      = Real.logb 2 ((M : ℝ) * (N : ℝ)) + 2 := by
  unfold assignmentDatabaseQueries
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
  rw [Real.logb_mul hM0 hN0]

/-- **c007** (paper p. 2, p. 6).  In the large-data regime `M, N ≥ 4`, the
`O(log(MN))` assignment query count is at most the `O(MN)` query count needed
to uncover the whole database: the user touches only a fraction of the data.

Source: arXiv:1307.0411v2 p. 2 "... while `O(MN)` are required to uncover the
actual data.  The data-base user can still obtain information about the
desired patterns, while the data-base owner is assured that the user has only
accessed an exponentially small fraction of the data base."

Proof: `logb_two_le_two_mul_sub_one` gives
`log₂ M + log₂ N + 2 ≤ 2M + 2N - 2 ≤ M·N`, the last step because
`M, N ≥ 4` implies `(M-2)(N-2) ≥ 4`. -/
theorem database_privacy_gap (M N : ℕ) (hM : 4 ≤ M) (hN : 4 ≤ N) :
    assignmentDatabaseQueries M N ≤ fullDatabaseQueries M N := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hbM := logb_two_le_two_mul_sub_one hM1
  have hbN := logb_two_le_two_mul_sub_one hN1
  have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hprod : (4 : ℝ) ≤ ((M : ℝ) - 2) * ((N : ℝ) - 2) := by
    have h1 : (2 : ℝ) ≤ (M : ℝ) - 2 := by linarith
    have h2 : (2 : ℝ) ≤ (N : ℝ) - 2 := by linarith
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ ((M : ℝ) - 2) * ((N : ℝ) - 2) :=
          mul_le_mul h1 h2 (by norm_num) (by linarith)
  unfold assignmentDatabaseQueries fullDatabaseQueries
  nlinarith [hbM, hbN, hprod]

end Qatlib.Papers.SupervisedML13.MainResults
