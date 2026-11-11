/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithmic query-rate identities

Records the single-level specialization of ordered-insertion iteration and the logarithmic rate
associated with size 52 in [FarhiEtAl1999]. `iterated_insertion_one` transports an existing
circuit through the identities `M ^ 1 = M` and `1 * k = k`; `query_growth_52` supplies the rate
identity for arbitrary natural exponents.

## Main statements

* `query_growth_52`: rewrites `3 * h` using the base-two logarithm of `52 ^ h`.

## References

* [Farhi et al., 1999][FarhiEtAl1999]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

/-- An exact insertion algorithm for size `M` also solves size `M ^ 1` within `1 * k` queries
[FarhiEtAl1999]. -/
theorem iterated_insertion_one (M k : ℕ) (hk : ExactQueryInsertion M k) :
    ExactQueryInsertion (M ^ 1) (1 * k) := by
  simpa using hk

/-- The query count `3 * h` equals `(3 / log₂ 52) * log₂ (52 ^ h)` [FarhiEtAl1999]. -/
theorem query_growth_52 (h : ℕ) :
    ((3 * h : ℕ) : ℝ) =
      (3 / Real.logb 2 52) * Real.logb 2 ((52 : ℝ) ^ h) := by
  have hlog : Real.logb 2 (52 : ℝ) ≠ 0 := by
    have h1 : Real.log 52 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    have h2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    rw [Real.logb]
    exact div_ne_zero h1 h2
  push_cast
  rw [Real.logb_pow]
  field_simp

/-- Given an exact three-query insertion algorithm for size 52, chooses its query count and
records the logarithmic rate identity at exponent one. -/
theorem iterated_insertion_rate_one (h52 : ExactQueryInsertion 52 3) :
    ∃ k' : ℕ, k' = 3 ∧ ExactQueryInsertion (52 ^ 1) k' ∧
      (k' : ℝ) = (3 / Real.logb 2 52) * Real.logb 2 ((52 : ℝ) ^ 1) := by
  refine ⟨3, rfl, iterated_insertion_one 52 3 h52, ?_⟩
  exact query_growth_52 1

end Qatlib.Papers.OrderedInsert99.MainResults
