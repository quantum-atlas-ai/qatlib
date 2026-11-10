/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.QueryBounds.FlowLowerBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.QueryBounds

open Qatlib.Papers.QMatchingFlow05.SearchTools

def BipartiteMatchLower (bipQuery : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ bipQuery n

def BipartiteEmbedsInGeneral (bipQuery genQuery : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, bipQuery n ≤ genQuery n

theorem bipartiteLower_transfers (bipQuery genQuery : ℕ → ℝ)
    (hlow : BipartiteMatchLower bipQuery)
    (hemb : BipartiteEmbedsInGeneral bipQuery genQuery) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ genQuery n := by
  obtain ⟨c, hc, hb⟩ := hlow
  exact ⟨c, hc, fun n => le_trans (hb n) (hemb n)⟩

theorem matching_lower_le_flow_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  simpa [Real.rpow_two] using! h

theorem flowLower_dominates_matchingLower (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) :
    c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ c * (n : ℝ) ^ 2 :=
  mul_le_mul_of_nonneg_left (matching_lower_le_flow_lower n hn) hc.le

end Qatlib.Papers.QMatchingFlow05.QueryBounds

end
