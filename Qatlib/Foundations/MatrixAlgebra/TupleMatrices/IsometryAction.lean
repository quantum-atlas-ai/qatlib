/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TupleMatrices.FiniteProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical
namespace Qatlib.Foundations.MatrixAlgebra.TupleMatrices
variable {A B : Type*} [Fintype A] [Fintype B]

theorem adjoint_comp_apply (C : Matrix B A ℂ) (hC : Cᴴ*C=1) (v : EuclideanSpace ℂ A) :
    (Matrix.toEuclideanLin C).adjoint (Matrix.toEuclideanLin C v)=v := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change WithLp.toLp 2 (Cᴴ*ᵥ (C*ᵥ WithLp.ofLp v))=v
  rw [Matrix.mulVec_mulVec,hC,Matrix.one_mulVec,WithLp.toLp_ofLp]

def rectangularAction (C : Matrix B A ℂ) (hC : Cᴴ*C=1) : EuclideanSpace ℂ A →ₗᵢ[ℂ] EuclideanSpace ℂ B :=
  (Matrix.toEuclideanLin C).isometryOfInner (fun u v => by
    rw [← LinearMap.adjoint_inner_right,adjoint_comp_apply C hC])

theorem rectangularAction_apply (C : Matrix B A ℂ) (hC : Cᴴ*C=1) (v : EuclideanSpace ℂ A) :
    rectangularAction C hC v=WithLp.toLp 2 (C*ᵥ WithLp.ofLp v) := rfl
end Qatlib.Foundations.MatrixAlgebra.TupleMatrices
