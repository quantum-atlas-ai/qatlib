/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3

/-!
# Scalar cost of an inner reflection

This module defines `innerReflectionCost`, the amplification cost expression used for the inner
reflection in the nested-walk analysis of [JefferyKothariMagniez2013]. It transfers the MNRS
amplification estimate to this expression under the stated depth, positivity, update-cost, and
checking-cost assumptions.

## Main statements

* `inner_reflection_cost_le`: the reflection cost is bounded by 99 times the inner MNRS cost
  expression.
* `inner_reflection_cost_bigO`: the same estimate with an existential positive uniform constant.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Real

namespace Qatlib.Papers.NestedQWalk12.CostModels.InnerReflection

/-- The scalar reflection cost 2 * 3^tMax * (c₁ * (log 72 + 3) + c₂). -/
def innerReflectionCost (tMax : ℕ) (c₁ c₂ : ℝ) : ℝ :=
  2 * (3 : ℝ) ^ tMax * (c₁ * (Real.log 72 + 3) + c₂)

/-- Under the stated positivity, amplification-depth, and branch-cost assumptions,
`innerReflectionCost` is at most 99 times (1/sqrt(ε')) * (U'/sqrt(δ') + C'). -/
theorem inner_reflection_cost_le (ε' δ' U' C' c₁ c₂ : ℝ) (tMax : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hδ' : 0 < δ') (hC' : 0 ≤ C')
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmax : (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε') ≤ 3 * π / 4)
    (hcU : c₁ ≤ 2 * U' / Real.sqrt δ') (hcc : c₂ ≤ C') :
    innerReflectionCost tMax c₁ c₂ ≤
      99 * ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')) := by
  unfold innerReflectionCost
  simpa only [mul_assoc] using
    Qatlib.Concepts.WalkSearch.MnrsAmplify.mnrs_order_form_cost
      ε' c₁ c₂ U' C' δ' tMax hε' hε'1 hc₁ hc₂ hmax hδ' hC' hcU hcc

/-- A positive uniform constant bounds `innerReflectionCost` by the inner MNRS expression under
the stated depth and cost assumptions, giving the scalar estimate associated with [Jeffery
et al., Lemma 3.1][JefferyKothariMagniez2013]. -/
theorem inner_reflection_cost_bigO :
    ∃ c : ℝ, 0 < c ∧ ∀ (ε' δ' U' C' c₁ c₂ : ℝ) (tMax : ℕ),
      0 < ε' → ε' ≤ 1 → 0 < δ' → 0 ≤ C' → 0 ≤ c₁ → 0 ≤ c₂ →
      (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε') ≤ 3 * π / 4 →
      c₁ ≤ 2 * U' / Real.sqrt δ' → c₂ ≤ C' →
      innerReflectionCost tMax c₁ c₂ ≤
        c * ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')) := by
  refine ⟨99, by norm_num, ?_⟩
  intro ε' δ' U' C' c₁ c₂ tMax hε' hε'1 hδ' hC' hc₁ hc₂ hmax hcU hcc
  exact inner_reflection_cost_le ε' δ' U' C' c₁ c₂ tMax
    hε' hε'1 hδ' hC' hc₁ hc₂ hmax hcU hcc

end Qatlib.Papers.NestedQWalk12.CostModels.InnerReflection
