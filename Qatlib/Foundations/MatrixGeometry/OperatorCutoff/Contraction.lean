/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.OperatorCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem car_norm_split (A : E →L[ℂ] E)
    (hcar : A * A.adjoint + A.adjoint * A = 1) (x : E) :
    ‖A x‖^2 + ‖A.adjoint x‖^2 = ‖x‖^2 := by
  have hvec := congrArg (fun T : E →L[ℂ] E => T x) hcar
  have hi := congrArg (fun y => (inner ℂ x y).re) hvec
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply, inner_add_right, Complex.add_re] at hi
  have hA := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right A x
  have hB := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right A.adjoint x
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hA hB
  change ‖A x‖ ^ 2 = (inner ℂ x (A.adjoint (A x))).re at hA
  change ‖A.adjoint x‖ ^ 2 = (inner ℂ x (A (A.adjoint x))).re at hB
  rw [← hA, ← hB] at hi
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 := by
    change RCLike.re (inner ℂ x x) = ‖x‖ ^ 2
    exact inner_self_eq_norm_sq x
  rw [hself] at hi
  linarith

theorem car_apply_norm (A : E →L[ℂ] E)
    (hcar : A * A.adjoint + A.adjoint * A = 1) (x : E) : ‖A x‖ ≤ ‖x‖ := by
  have hs := car_norm_split A hcar x
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖A.adjoint x‖])

theorem car_opNorm (A : E →L[ℂ] E)
    (hcar : A * A.adjoint + A.adjoint * A = 1) : ‖A‖ ≤ 1 := by
  apply A.opNorm_le_bound (by norm_num)
  intro x
  simpa using car_apply_norm A hcar x

omit [CompleteSpace E] in

theorem word_opNorm (L : List (E →L[ℂ] E)) (hL : ∀ A ∈ L, ‖A‖ ≤ 1) : ‖L.prod‖ ≤ 1 := by
  induction L with
  | nil => simpa using! (ContinuousLinearMap.norm_id_le : ‖(1 : E →L[ℂ] E)‖ ≤ 1)
  | cons A L ih =>
    rw [List.prod_cons]
    calc ‖A * L.prod‖ ≤ ‖A‖ * ‖L.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hL A (by simp)) (ih (by intro B hB; exact hL B (by simp [hB])))
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
end Qatlib.Foundations.MatrixGeometry.OperatorCutoff
