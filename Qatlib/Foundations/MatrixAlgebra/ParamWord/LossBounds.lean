/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.WordBounds
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Bounds for quadratic expectation losses

`expectation` is the real quadratic expression `⟪S x, T (S x)⟫`, with `expectationD` its
product-rule derivative expression. Differentiability of `S` yields `expectation_hasFDerivAt`
without a symmetry hypothesis on `T`.

For `‖T‖ ≤ 1` and states of norm at most one, the loss has absolute value at most one. Bounds
`C` on state derivatives and state Lipschitz variation, together with derivative Lipschitz bound
`L`, give the loss derivative bound `2C` and Lipschitz bound `2C² + 2L`; see [TranEtAl2026] for
the circuit-loss setting.

## Main statements

* `expectation_hasFDerivAt`: Product-rule derivative of the quadratic expectation.
* `expectationD_norm`: Derivative norm bound `2C`.
* `expectationD_lipschitz_bound`: Derivative Lipschitz bound `2C² + 2L`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.ParamWord
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real quadratic expectation `inner ℝ (S x) (T (S x))`. -/
def expectation (T : H→L[ℝ]H) (S : E→H) (x : E) : ℝ := inner ℝ (S x) (T (S x))

/-- The continuous real-linear expression sending `v` to `⟪S x, T (DS x v)⟫_ℝ + ⟪T (S x), DS x
v⟫_ℝ`. -/
def expectationD (T : H→L[ℝ]H) (S : E→H) (DS : E→E→L[ℝ]H) (x : E) : E→L[ℝ]ℝ :=
  (innerSL ℝ (S x)).comp (T.comp (DS x))+(innerSL ℝ (T (S x))).comp (DS x)

/-- If `DS x` is the Fréchet derivative of `S` at every `x`, then `expectationD T S DS x` is the
derivative of the quadratic expectation at `x`. -/
theorem expectation_hasFDerivAt (T : H→L[ℝ]H) (S : E→H) (DS : E→E→L[ℝ]H)
    (hS : ∀x,HasFDerivAt S (DS x) x) (x : E) :
    HasFDerivAt (expectation T S) (expectationD T S DS x) x := by
  have h := (hS x).inner ℝ (T.hasFDerivAt.comp x (hS x))
  convert! h using 1
  ext v
  simp [expectationD,fderivInnerCLM_apply,real_inner_comm]

/-- A continuous real-linear map with operator norm at most one does not increase vector norms. -/
theorem observable_apply_le (T : H→L[ℝ]H) (hT : ‖T‖≤1) (v : H) : ‖T v‖≤‖v‖ :=
  (T.le_opNorm v).trans (by nlinarith [norm_nonneg v])

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

/-- If `T` and all states `S x` have norm at most one, the quadratic expectation has absolute
value at most one. -/
theorem expectation_abs_le (T : H→L[ℝ]H) (S : E→H)
    (hT : ‖T‖≤1) (hS : ∀x,‖S x‖≤1) (x : E) : |expectation T S x|≤1 := by
  have ht := (observable_apply_le T hT (S x)).trans (hS x)
  have hn := norm_inner_le_norm (𝕜:=ℝ) (S x) (T (S x))
  exact hn.trans ((mul_le_mul (hS x) ht (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-- If `T` and the states have norm at most one and `DS` has norm bounded by a nonnegative `C`,
the expectation derivative expression has norm at most `2C`. -/
theorem expectationD_norm (T : H→L[ℝ]H) (S : E→H) (DS : E→E→L[ℝ]H)
    (hT : ‖T‖≤1) (hS : ∀x,‖S x‖≤1) (C : ℝ) (hC : 0≤C)
    (hD : ∀x,‖DS x‖≤C) (x : E) : ‖expectationD T S DS x‖≤2*C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hdv : ‖DS x v‖≤C*‖v‖ :=
    (DS x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg v))
  have htd := (observable_apply_le T hT (DS x v)).trans hdv
  have hts := (observable_apply_le T hT (S x)).trans (hS x)
  change ‖inner ℝ (S x) (T (DS x v))+inner ℝ (T (S x)) (DS x v)‖≤_
  calc
    _ ≤ ‖S x‖*‖T (DS x v)‖+‖T (S x)‖*‖DS x v‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ 1*(C*‖v‖)+1*(C*‖v‖) :=
      add_le_add (mul_le_mul (hS x) htd (norm_nonneg _) zero_le_one)
        (mul_le_mul hts hdv (norm_nonneg _) zero_le_one)
    _ = _ := by ring

/-- If `T` and the states have norm at most one, `DS` has norm bound `C`, and `S` and `DS` have
Lipschitz bounds `C` and `L`, then the expectation derivative expression has Lipschitz bound
`2C² + 2L`, for nonnegative `C` and `L`. -/
theorem expectationD_lipschitz_bound (T : H→L[ℝ]H) (S : E→H) (DS : E→E→L[ℝ]H)
    (hT : ‖T‖≤1) (hS : ∀x,‖S x‖≤1) (C L : ℝ) (hC : 0≤C) (hL : 0≤L)
    (hD : ∀x,‖DS x‖≤C)
    (hLipS : ∀x y,‖S x-S y‖≤C*‖x-y‖)
    (hLipD : ∀x y,‖DS x-DS y‖≤L*‖x-y‖) (x y : E) :
    ‖expectationD T S DS x-expectationD T S DS y‖≤(2*C^2+2*L)*‖x-y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hnv : 0≤‖v‖ := norm_nonneg _
  have hdv : ‖DS x v‖≤C*‖v‖ :=
    (DS x).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hD x) hnv)
  have hey : ‖DS y v‖≤C*‖v‖ :=
    (DS y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hD y) hnv)
  have hexy : ‖DS x v-DS y v‖≤(L*‖x-y‖)*‖v‖ :=
    (DS x-DS y).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right (hLipD x y) hnv)
  have hsd := hLipS x y
  have htDx := (observable_apply_le T hT (DS x v)).trans hdv
  have htDy := (observable_apply_le T hT (DS x v-DS y v)).trans hexy
  have htSx := (observable_apply_le T hT (S x)).trans (hS x)
  have htSdiff := (observable_apply_le T hT (S x-S y)).trans hsd
  have he : (expectationD T S DS x-expectationD T S DS y) v=
      inner ℝ (S x-S y) (T (DS x v))+
      inner ℝ (S y) (T (DS x v-DS y v))+
      inner ℝ (DS x v-DS y v) (T (S x))+
      inner ℝ (DS y v) (T (S x-S y)) := by
    simp only [expectationD,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,map_sub,inner_sub_left,inner_sub_right]
    rw [real_inner_comm (T (S x)) (DS x v),real_inner_comm (T (S y)) (DS y v)]
    ring
  rw [he]
  have hn (a b c d : ℝ) : ‖a+b+c+d‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
    nlinarith [norm_add_le a b,norm_add_le (a+b) c,norm_add_le (a+b+c) d]
  calc
    _ ≤ ‖inner ℝ (S x-S y) (T (DS x v))‖+
        ‖inner ℝ (S y) (T (DS x v-DS y v))‖+
        ‖inner ℝ (DS x v-DS y v) (T (S x))‖+
        ‖inner ℝ (DS y v) (T (S x-S y))‖ := hn _ _ _ _
    _ ≤ ‖S x-S y‖*‖T (DS x v)‖+‖S y‖*‖T (DS x v-DS y v)‖+
        ‖DS x v-DS y v‖*‖T (S x)‖+‖DS y v‖*‖T (S x-S y)‖ :=
      add_le_add (add_le_add (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
        (norm_inner_le_norm _ _)) (norm_inner_le_norm _ _)
    _ ≤ (C*‖x-y‖)*(C*‖v‖)+1*((L*‖x-y‖)*‖v‖)+
        ((L*‖x-y‖)*‖v‖)*1+(C*‖v‖)*(C*‖x-y‖) :=
      add_le_add (add_le_add
        (add_le_add (mul_le_mul hsd htDx (norm_nonneg _) (by positivity))
          (mul_le_mul (hS y) htDy (norm_nonneg _) zero_le_one))
        (mul_le_mul hexy htSx (norm_nonneg _) (by positivity)))
        (mul_le_mul hey htSdiff (norm_nonneg _) (by positivity))
    _ = _ := by ring
end Qatlib.Foundations.MatrixAlgebra.ParamWord
