/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.QueryBounds.FlowLowerBound

/-!
# Transfer of matching query lower bounds

This module formalizes scalar lower-bound transfer principles for the matching and flow bounds
discussed in [AmbainisSpalek2006]. The predicate `BipartiteMatchLower` expresses a
positive-constant `n ^ (3 / 2)` lower bound, and `BipartiteEmbedsInGeneral` expresses pointwise
domination of one query budget by another.

The main transfer theorem combines these two hypotheses. Additional inequalities compare the `n
^ (3 / 2)` and `n²` expressions for `n ≥ 1`.

## Main statements

* `bipartiteLower_transfers`: pointwise domination transfers the given bipartite lower bound.
* `flowLower_dominates_matchingLower`: comparison of the two scaled power expressions.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.QueryBounds

open Qatlib.Papers.QMatchingFlow05.SearchTools

/-- The proposition that `bipQuery n` is at least a positive constant times `n ^ (3 / 2)` for
every natural `n`. See [AmbainisSpalek2006]. -/
def BipartiteMatchLower (bipQuery : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ bipQuery n

/-- The pointwise inequality `bipQuery n ≤ genQuery n` for all natural `n`. -/
def BipartiteEmbedsInGeneral (bipQuery genQuery : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, bipQuery n ≤ genQuery n

/-- A positive-constant `n ^ (3 / 2)` lower bound transfers from `bipQuery` to `genQuery` under
pointwise domination. See [AmbainisSpalek2006]. -/
theorem bipartiteLower_transfers (bipQuery genQuery : ℕ → ℝ)
    (hlow : BipartiteMatchLower bipQuery)
    (hemb : BipartiteEmbedsInGeneral bipQuery genQuery) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ genQuery n := by
  obtain ⟨c, hc, hb⟩ := hlow
  exact ⟨c, hc, fun n => le_trans (hb n) (hemb n)⟩

/-- For natural `n ≥ 1`, one has `n ^ (3 / 2) ≤ n ^ 2`. See [AmbainisSpalek2006]. -/
theorem matching_lower_le_flow_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  simpa [Real.rpow_two] using! h

/-- For positive `c` and natural `n ≥ 1`, one has `c * n ^ (3 / 2) ≤ c * n ^ 2`. See
[AmbainisSpalek2006]. -/
theorem flowLower_dominates_matchingLower (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) :
    c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ c * (n : ℝ) ^ 2 :=
  mul_le_mul_of_nonneg_left (matching_lower_le_flow_lower n hn) hc.le

end Qatlib.Papers.QMatchingFlow05.QueryBounds

end
