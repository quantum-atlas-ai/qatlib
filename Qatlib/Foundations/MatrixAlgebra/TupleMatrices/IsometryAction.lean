/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.TupleMatrices.FiniteProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert-space actions of rectangular isometries

The module turns a rectangular complex matrix satisfying `Cᴴ * C = 1` into the linear isometry
`rectangularAction` between finite Euclidean spaces. It also identifies this action with
ordinary matrix-vector multiplication under the `WithLp` coordinate conversion.

The construction keeps the Euclidean Hilbert norm explicit for matrix carriers, as needed in the
operator-norm setting of [MagniezZur2026].

## Main statements

* `adjoint_comp_apply`: the adjoint action reverses the matrix action.
* `rectangularAction`: a matrix isometry packaged as a complex linear isometry.
* `rectangularAction_apply`: the isometry agrees with coordinate matrix-vector multiplication.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical
namespace Qatlib.Foundations.MatrixAlgebra.TupleMatrices
variable {A B : Type*} [Fintype A] [Fintype B]

/-- If `Cᴴ * C = 1`, applying the adjoint of the Euclidean linear map after the map itself
returns the input vector. -/
theorem adjoint_comp_apply (C : Matrix B A ℂ) (hC : Cᴴ*C=1) (v : EuclideanSpace ℂ A) :
    (Matrix.toEuclideanLin C).adjoint (Matrix.toEuclideanLin C v)=v := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change WithLp.toLp 2 (Cᴴ*ᵥ (C*ᵥ WithLp.ofLp v))=v
  rw [Matrix.mulVec_mulVec,hC,Matrix.one_mulVec,WithLp.toLp_ofLp]

/-- The complex linear isometry induced by a rectangular matrix satisfying `Cᴴ * C = 1`, with
the Euclidean Hilbert norms used in [MagniezZur2026]. -/
def rectangularAction (C : Matrix B A ℂ) (hC : Cᴴ*C=1) : EuclideanSpace ℂ A →ₗᵢ[ℂ] EuclideanSpace ℂ B :=
  (Matrix.toEuclideanLin C).isometryOfInner (fun u v => by
    rw [← LinearMap.adjoint_inner_right,adjoint_comp_apply C hC])

/-- The rectangular linear isometry acts by matrix-vector multiplication after converting to
coordinates, followed by conversion back to Euclidean space. -/
theorem rectangularAction_apply (C : Matrix B A ℂ) (hC : Cᴴ*C=1) (v : EuclideanSpace ℂ A) :
    rectangularAction C hC v=WithLp.toLp 2 (C*ᵥ WithLp.ofLp v) := rfl
end Qatlib.Foundations.MatrixAlgebra.TupleMatrices
