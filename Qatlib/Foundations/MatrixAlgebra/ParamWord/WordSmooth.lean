/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ParamWord.WordBounds

/-!
# Lipschitz derivatives of parameterized products

For differentiable factors of norm at most one whose derivatives also have norm at most one,
`paramWordD_lipschitz_bound` propagates unit Lipschitz bounds on the factors and derivatives to
a squared-word-length bound on the word derivative.

`paramWord_native_fderiv_lipschitz` states this estimate using the Fréchet derivative `fderiv`.
This is the abstract product estimate used for the circuit-loss smoothness setting of
[TranEtAl2026].

## Main statements

* `paramWordD_lipschitz_bound`: Lipschitz constant bounded by the squared word length.
* `paramWord_native_fderiv_lipschitz`: The same estimate for `fderiv`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped RightActions
namespace Qatlib.Foundations.MatrixAlgebra.ParamWord
variable {E A J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

/-- If differentiable factors and their derivatives have norm at most one and are each
1-Lipschitz, the word derivative expression is globally Lipschitz with constant equal to the
squared word length. -/
theorem paramWordD_lipschitz_bound (F : J→E→A) (DF : J→E→E→L[ℝ]A)
    (hF : ∀j x,‖F j x‖≤1) (hD : ∀j x,‖DF j x‖≤1)
    (hd : ∀j x,HasFDerivAt (F j) (DF j x) x)
    (hLipF : ∀j x y,‖F j x-F j y‖≤‖x-y‖)
    (hLipD : ∀j x y,‖DF j x-DF j y‖≤‖x-y‖)
    (js : List J) (x y : E) :
    ‖paramWordD F DF js x-paramWordD F DF js y‖≤(js.length:ℝ)^2*‖x-y‖ := by
  induction js with
  | nil => simp [paramWordD]
  | cons j js ih =>
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hnv : 0≤‖v‖ := norm_nonneg v
    have hdist : 0≤‖x-y‖ := norm_nonneg _
    have ht := (paramWord_lipschitz F DF hF hD hd js).norm_sub_le x y
    have htd : ‖paramWordD F DF js x v-paramWordD F DF js y v‖≤
        ((js.length:ℝ)^2*‖x-y‖)*‖v‖ :=
      ((paramWordD F DF js x-paramWordD F DF js y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ih hnv)
    have hsd : ‖DF j x v-DF j y v‖≤‖x-y‖*‖v‖ :=
      ((DF j x-DF j y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hLipD j x y) hnv)
    have hsy : ‖DF j y v‖≤‖v‖ :=
      (DF j y).le_opNorm v |>.trans (by nlinarith [hD j y])
    have he : (paramWordD F DF (j::js) x-paramWordD F DF (j::js) y) v=
        (F j x-F j y)*paramWordD F DF js x v+
        F j y*(paramWordD F DF js x v-paramWordD F DF js y v)+
        (DF j x v-DF j y v)*paramWord F js x+
        DF j y v*(paramWord F js x-paramWord F js y) := by
      change (F j x*paramWordD F DF js x v+DF j x v*paramWord F js x)-
        (F j y*paramWordD F DF js y v+DF j y v*paramWord F js y)=_
      noncomm_ring
    rw [he]
    have hn (a b c d : A) : ‖a+b+c+d‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
      nlinarith [norm_add_le a b,norm_add_le (a+b) c,norm_add_le (a+b+c) d]
    calc
      _ ≤ ‖(F j x-F j y)*paramWordD F DF js x v‖+
          ‖F j y*(paramWordD F DF js x v-paramWordD F DF js y v)‖+
          ‖(DF j x v-DF j y v)*paramWord F js x‖+
          ‖DF j y v*(paramWord F js x-paramWord F js y)‖ := hn _ _ _ _
      _ ≤ ‖F j x-F j y‖*‖paramWordD F DF js x v‖+
          ‖F j y‖*‖paramWordD F DF js x v-paramWordD F DF js y v‖+
          ‖DF j x v-DF j y v‖*‖paramWord F js x‖+
          ‖DF j y v‖*‖paramWord F js x-paramWord F js y‖ := by
            exact add_le_add
                (add_le_add (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) (norm_mul_le _ _))
                (norm_mul_le _ _)
      _ ≤ ‖x-y‖*(js.length*‖v‖)+1*(((js.length:ℝ)^2*‖x-y‖)*‖v‖)+
          (‖x-y‖*‖v‖)*1+‖v‖*(js.length*‖x-y‖) := by
            exact add_le_add (add_le_add
              (add_le_add
                (mul_le_mul (hLipF j x y) (paramWordD_apply_bound F DF hF hD js x v)
                  (norm_nonneg _) hdist)
                (mul_le_mul (hF j y) htd (norm_nonneg _) zero_le_one))
              (mul_le_mul hsd (paramWord_norm F hF js x) (norm_nonneg _)
                (mul_nonneg hdist hnv)))
              (mul_le_mul hsy ht (norm_nonneg _) hnv)
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one];ring

/-- If differentiable factors and their derivatives have norm at most one and are each
1-Lipschitz, the Fréchet derivative of their ordered product is globally Lipschitz with
constant equal to the squared word length. -/
theorem paramWord_native_fderiv_lipschitz (F : J→E→A) (DF : J→E→E→L[ℝ]A)
    (hF : ∀j x,‖F j x‖≤1) (hD : ∀j x,‖DF j x‖≤1)
    (hd : ∀j x,HasFDerivAt (F j) (DF j x) x)
    (hLipF : ∀j x y,‖F j x-F j y‖≤‖x-y‖)
    (hLipD : ∀j x y,‖DF j x-DF j y‖≤‖x-y‖)
    (js : List J) (x y : E) :
    ‖fderiv ℝ (paramWord F js) x-fderiv ℝ (paramWord F js) y‖≤(js.length:ℝ)^2*‖x-y‖ := by
  rw [(paramWord_hasFDerivAt F DF hd js x).fderiv,(paramWord_hasFDerivAt F DF hd js y).fderiv]
  exact paramWordD_lipschitz_bound F DF hF hD hd hLipF hLipD js x y
end Qatlib.Foundations.MatrixAlgebra.ParamWord
