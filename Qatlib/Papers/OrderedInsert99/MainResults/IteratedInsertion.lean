/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

theorem iterated_insertion_one (M k : ℕ) (hk : ExactQueryInsertion M k) :
    ExactQueryInsertion (M ^ 1) (1 * k) := by
  simpa using hk

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

theorem iterated_insertion_rate_one (h52 : ExactQueryInsertion 52 3) :
    ∃ k' : ℕ, k' = 3 ∧ ExactQueryInsertion (52 ^ 1) k' ∧
      (k' : ℝ) = (3 / Real.logb 2 52) * Real.logb 2 ((52 : ℝ) ^ 1) := by
  refine ⟨3, rfl, iterated_insertion_one 52 3 h52, ?_⟩
  exact query_growth_52 1

end Qatlib.Papers.OrderedInsert99.MainResults
