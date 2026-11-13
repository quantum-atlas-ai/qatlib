/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3

/-!
# Two-level nested-walk cost bounds

This module defines the single-level expression `mnrsCost` and its two-level composition
`twoLevelCost`, including a setup cost. It bounds the explicit amplification expression
`innerReflectionCost` by this nested scalar cost under the depth and cost assumptions used in
Theorem 3.2 of [JefferyKothariMagniez2013].

Nonnegativity and monotonicity lemmas support the composition of the inner and outer estimates.
`theorem32_two_level_cost` gives the resulting factor 99².

## Main statements

* `mInner_nonneg`: nonnegativity of the MNRS cost expression.
* `mnrsCost_mono_C`: monotonicity in the checking cost.
* `theorem32_two_level_cost`: setup plus the outer reflection cost is at most 99² times
  `twoLevelCost`.

## References

* [Jeffery et al., 2013][JefferyKothariMagniez2013]
-/

set_option autoImplicit false
noncomputable section

open scoped Real

namespace Qatlib.Papers.NestedQWalk12.CostModels.TwoLevelNesting

/-- The scalar MNRS cost (1/sqrt(ε)) * (U/sqrt(δ) + C). -/
def mnrsCost (ε δ U C : ℝ) : ℝ :=
  (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C)

/-- The setup cost S plus the outer MNRS cost with the inner MNRS expression as its checking
cost. -/
def twoLevelCost (S ε δ U ε' δ' U' C' : ℝ) : ℝ :=
  S + mnrsCost ε δ U (mnrsCost ε' δ' U' C')

/-- The scalar amplification cost 2 * 3^tMax * (c₁ * (log 72 + 3) + c₂). -/
def innerReflectionCost (tMax : ℕ) (c₁ c₂ : ℝ) : ℝ :=
  2 * (3 : ℝ) ^ tMax * (c₁ * (Real.log 72 + 3) + c₂)

/-- The MNRS scalar cost is nonnegative for positive ε and δ and nonnegative update and checking
costs. -/
theorem mInner_nonneg {ε δ U C : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hU : 0 ≤ U) (hC : 0 ≤ C) : 0 ≤ mnrsCost ε δ U C := by
  have hε' : (0 : ℝ) ≤ 1 / Real.sqrt ε := by positivity
  have hδ' : (0 : ℝ) ≤ 1 / Real.sqrt δ := by positivity
  unfold mnrsCost
  positivity

/-- The scalar inner-reflection cost is nonnegative when both branch costs are nonnegative. -/
theorem innerReflectionCost_nonneg (tMax : ℕ) {c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) : 0 ≤ innerReflectionCost tMax c₁ c₂ := by
  have hlog : (0 : ℝ) ≤ Real.log 72 + 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 72); linarith
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ tMax := by positivity
  unfold innerReflectionCost
  positivity

/-- Under the stated positive-parameter and nonnegative-update assumptions, increasing the
checking cost cannot decrease `mnrsCost`. -/
theorem mnrsCost_mono_C {ε δ U C D : ℝ} (hε : 0 < ε) (_hδ : 0 < δ)
    (_hU : 0 ≤ U) (hCD : C ≤ D) : mnrsCost ε δ U C ≤ mnrsCost ε δ U D := by
  have hε' : (0 : ℝ) ≤ 1 / Real.sqrt ε := by positivity
  unfold mnrsCost
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hCD) hε'

/-- Under the stated positivity, depth, and inner/outer cost assumptions, setup plus the outer
reflection cost is at most 99² times `twoLevelCost`. This gives the scalar composition
estimate associated with [Jeffery et al., Theorem 3.2][JefferyKothariMagniez2013]. -/
theorem theorem32_two_level_cost
    (S ε δ U ε' δ' U' C' c₁ c₂ c₁' c₂' : ℝ) (tMax tMax' : ℕ)
    (hS : 0 ≤ S) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hU : 0 ≤ U)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hδ' : 0 < δ') (hU' : 0 ≤ U') (hC' : 0 ≤ C')
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hmax : (3 : ℝ) ^ tMax * Real.arcsin (Real.sqrt ε) ≤ 3 * π / 4)
    (hcU : c₁ ≤ 2 * U / Real.sqrt δ)
    (hc₂inner : c₂ ≤ innerReflectionCost tMax' c₁' c₂')
    (hc₁' : 0 ≤ c₁') (hc₂' : 0 ≤ c₂')
    (hmax' : (3 : ℝ) ^ tMax' * Real.arcsin (Real.sqrt ε') ≤ 3 * π / 4)
    (hcU' : c₁' ≤ 2 * U' / Real.sqrt δ') (hcc' : c₂' ≤ C') :
    S + innerReflectionCost tMax c₁ c₂ ≤
      (99 : ℝ) ^ 2 * twoLevelCost S ε δ U ε' δ' U' C' := by

  have hInner : innerReflectionCost tMax' c₁' c₂' ≤ 99 * mnrsCost ε' δ' U' C' := by
    unfold innerReflectionCost mnrsCost
    simpa only [mul_assoc] using
      Qatlib.Concepts.WalkSearch.MnrsAmplify.mnrs_order_form_cost
        ε' c₁' c₂' U' C' δ' tMax' hε' hε'1 hc₁' hc₂' hmax' hδ' hC' hcU' hcc'

  have hOuter : innerReflectionCost tMax c₁ c₂ ≤
      99 * mnrsCost ε δ U (innerReflectionCost tMax' c₁' c₂') := by
    simpa only [innerReflectionCost, mnrsCost, mul_assoc] using
      Qatlib.Concepts.WalkSearch.MnrsAmplify.mnrs_order_form_cost
        ε c₁ c₂ U (innerReflectionCost tMax' c₁' c₂') δ tMax
        hε hε1 hc₁ hc₂ hmax hδ
        (innerReflectionCost_nonneg tMax' hc₁' hc₂') hcU hc₂inner
  have hInnNonneg : 0 ≤ innerReflectionCost tMax' c₁' c₂' :=
    innerReflectionCost_nonneg tMax' hc₁' hc₂'
  have hM' : 0 ≤ mnrsCost ε' δ' U' C' := mInner_nonneg hε' hδ' hU' hC'

  have hmono : mnrsCost ε δ U (innerReflectionCost tMax' c₁' c₂') ≤
      mnrsCost ε δ U (99 * mnrsCost ε' δ' U' C') :=
    mnrsCost_mono_C hε hδ hU hInner

  have hscale : mnrsCost ε δ U (99 * mnrsCost ε' δ' U' C') ≤
      99 * mnrsCost ε δ U (mnrsCost ε' δ' U' C') := by
    have hε0 : (0 : ℝ) ≤ 1 / Real.sqrt ε := by positivity
    have hδ0 : (0 : ℝ) ≤ 1 / Real.sqrt δ := by positivity
    have hb : 0 ≤ (1 / Real.sqrt δ) * U := mul_nonneg hδ0 hU
    have hM'' : (0 : ℝ) ≤ (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C') := by
      simpa only [mnrsCost] using hM'
    have hineq : (1 / Real.sqrt δ) * U + 99 * ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C'))
        ≤ 99 * ((1 / Real.sqrt δ) * U + (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')) := by
      nlinarith [hb, hM'']
    unfold mnrsCost
    calc
      (1 / Real.sqrt ε) *
          ((1 / Real.sqrt δ) * U + 99 * ((1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C')))
          ≤ (1 / Real.sqrt ε) *
              (99 * ((1 / Real.sqrt δ) * U + (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C'))) :=
            mul_le_mul_of_nonneg_left hineq hε0
      _ = 99 * ((1 / Real.sqrt ε) *
              ((1 / Real.sqrt δ) * U + (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + C'))) := by
            ring

  have hmain : innerReflectionCost tMax c₁ c₂ ≤
      (99 : ℝ) ^ 2 * mnrsCost ε δ U (mnrsCost ε' δ' U' C') := by
    calc
      innerReflectionCost tMax c₁ c₂
          ≤ 99 * mnrsCost ε δ U (innerReflectionCost tMax' c₁' c₂') := hOuter
      _ ≤ 99 * mnrsCost ε δ U (99 * mnrsCost ε' δ' U' C') :=
            mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ 99 * (99 * mnrsCost ε δ U (mnrsCost ε' δ' U' C')) :=
            mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = (99 : ℝ) ^ 2 * mnrsCost ε δ U (mnrsCost ε' δ' U' C') := by ring
  have hMouter : 0 ≤ mnrsCost ε δ U (mnrsCost ε' δ' U' C') :=
    mInner_nonneg hε hδ hU hM'
  have hfinal : S + innerReflectionCost tMax c₁ c₂ ≤
      (99 : ℝ) ^ 2 * (S + mnrsCost ε δ U (mnrsCost ε' δ' U' C')) := by
    nlinarith [hmain, hS, hMouter]
  simpa only [twoLevelCost] using hfinal

end Qatlib.Papers.NestedQWalk12.CostModels.TwoLevelNesting
