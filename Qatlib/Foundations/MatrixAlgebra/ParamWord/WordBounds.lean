/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped RightActions
namespace Qatlib.Foundations.MatrixAlgebra.ParamWord
variable {E A J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]

def paramWord (F : J→E→A) : List J→E→A
  | [],_ => 1
  | j::js,x => F j x*paramWord F js x

def paramWordD (F : J→E→A) (DF : J→E→E→L[ℝ]A) : List J→E→E→L[ℝ]A
  | [],_ => 0
  | j::js,x => F j x • paramWordD F DF js x + DF j x <• paramWord F js x

omit [NormOneClass A] in

theorem paramWord_hasFDerivAt (F : J→E→A) (DF : J→E→E→L[ℝ]A)
    (hF : ∀j x,HasFDerivAt (F j) (DF j x) x) (js : List J) (x : E) :
    HasFDerivAt (paramWord F js) (paramWordD F DF js x) x := by
  induction js with
  | nil => exact hasFDerivAt_const (1:A) x
  | cons j js ih => exact (hF j x).mul' ih

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAlgebra ℝ A] in

theorem paramWord_norm (F : J→E→A) (hF : ∀j x,‖F j x‖≤1) (js : List J) (x : E) :
    ‖paramWord F js x‖≤1 := by
  induction js with
  | nil => simp [paramWord]
  | cons j js ih =>
    exact (norm_mul_le _ _).trans
        ((mul_le_mul (hF j x) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem paramWordD_apply_bound (F : J→E→A) (DF : J→E→E→L[ℝ]A)
    (hF : ∀j x,‖F j x‖≤1) (hD : ∀j x,‖DF j x‖≤1)
    (js : List J) (x v : E) : ‖paramWordD F DF js x v‖≤js.length*‖v‖ := by
  induction js with
  | nil => simp [paramWordD]
  | cons j js ih =>
    have ha : ‖DF j x v‖≤‖v‖ := (DF j x).le_opNorm v |>.trans (by nlinarith [hD j x,norm_nonneg v])
    change ‖F j x*paramWordD F DF js x v+DF j x v*paramWord F js x‖≤_
    calc
      _ ≤ ‖F j x‖*‖paramWordD F DF js x v‖+‖DF j x v‖*‖paramWord F js x‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1*(js.length*‖v‖)+‖v‖*1 :=
        add_le_add (mul_le_mul (hF j x) ih (norm_nonneg _) zero_le_one)
          (mul_le_mul ha (paramWord_norm F hF js x) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one];ring

theorem paramWordD_norm (F : J→E→A) (DF : J→E→E→L[ℝ]A)
    (hF : ∀j x,‖F j x‖≤1) (hD : ∀j x,‖DF j x‖≤1)
    (js : List J) (x : E) : ‖paramWordD F DF js x‖≤js.length :=
  ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _) (paramWordD_apply_bound F DF hF hD js x)

theorem paramWord_lipschitz (F : J→E→A) (DF : J→E→E→L[ℝ]A)
    (hF : ∀j x,‖F j x‖≤1) (hD : ∀j x,‖DF j x‖≤1)
    (hd : ∀j x,HasFDerivAt (F j) (DF j x) x) (js : List J) :
    LipschitzWith (js.length:NNReal) (paramWord F js) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
      (fun x => (paramWord_hasFDerivAt F DF hd js x).differentiableAt)
  intro x
  rw [(paramWord_hasFDerivAt F DF hd js x).fderiv]
  exact paramWordD_norm F DF hF hD js x

end Qatlib.Foundations.MatrixAlgebra.ParamWord
