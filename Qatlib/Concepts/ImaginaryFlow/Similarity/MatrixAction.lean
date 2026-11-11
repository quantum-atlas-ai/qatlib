/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix actions on complex Euclidean space

This module relates matrix multiplication and conjugate transpose to `Matrix.toEuclideanLin`. It
proves compatibility with multiplication, the identity matrix, and the adjoint inner-product
relation, using the finite-dimensional operator conventions of [Bhatia1997].

## Main statements

* `matrix_action_mul`: matrix multiplication acts by composition.
* `matrix_action_one`: the identity matrix fixes every vector.
* `inner_matrix_adjoint`: the conjugate-transpose inner-product identity.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ImaginaryFlow.Similarity
open Matrix

/-- The Euclidean linear action of a matrix product is the composition of the two matrix
actions. -/
theorem matrix_action_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    Matrix.toEuclideanLin (A*B) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  apply WithLp.ofLp_injective
  change (A*B) *ᵥ x.ofLp = A *ᵥ (B *ᵥ x.ofLp)
  rw [Matrix.mulVec_mulVec]

/-- The identity matrix acts as the identity on complex Euclidean space. -/
theorem matrix_action_one {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) : Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℂ) x = x := by
  apply WithLp.ofLp_injective
  change (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ x.ofLp = x.ofLp
  exact Matrix.one_mulVec _

/-- Moving a matrix action from the first inner-product argument to the second replaces the
matrix by its conjugate transpose. -/
theorem inner_matrix_adjoint {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (Matrix.toEuclideanLin A x) y =
      inner ℂ x (Matrix.toEuclideanLin A.conjTranspose y) := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_right _ _ _).symm

end Qatlib.Concepts.ImaginaryFlow.Similarity
