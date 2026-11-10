/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.CoordinateFibre
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

def coordinateAction (i : I) : EuclideanSpace ℂ (InjectiveTuple I L) →ₗ[ℂ] EuclideanSpace ℂ (InjectiveTuple I L) :=
  Matrix.toEuclideanLin (coordinateGram (L := L) i)
omit [Fintype L] in

theorem coordinateGram_adjoint (i : I) : (coordinateGram (L := L) i)ᴴ=coordinateGram (L := L) i := by
  ext u v
  by_cases h : eraseTuple i u=eraseTuple i v <;> simp [coordinateGram,Matrix.conjTranspose_apply,h,eq_comm]

theorem coordinateAction_adjoint (i : I) : (coordinateAction (L := L) i).adjoint=coordinateAction (L := L) i := by
  rw [coordinateAction,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,coordinateGram_adjoint]

theorem coordinateAction_squared (i : I) (v : EuclideanSpace ℂ (InjectiveTuple I L)) :
    coordinateAction (L := L) i (coordinateAction (L := L) i v)=
      ((Fintype.card L-Fintype.card (Off I i) : ℕ) : ℂ) • coordinateAction (L := L) i v := by
  change WithLp.toLp 2 (coordinateGram i*ᵥ (coordinateGram i*ᵥ WithLp.ofLp v))=_
  rw [Matrix.mulVec_mulVec,coordinateGram_squared,Matrix.smul_mulVec]
  rfl

theorem coordinate_energy (i : I) (v : EuclideanSpace ℂ (InjectiveTuple I L)) :
    ‖coordinateAction (L := L) i v‖^2=
      ((Fintype.card L-Fintype.card (Off I i) : ℕ) : ℝ)*(inner ℂ v (coordinateAction (L := L) i v)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),← LinearMap.adjoint_inner_right,coordinateAction_adjoint,coordinateAction_squared]
  rw [inner_smul_right]
  change (((Fintype.card L-Fintype.card (Off I i) : ℕ) : ℂ)*inner ℂ v (coordinateAction i v)).re=_
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
