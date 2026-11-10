/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ImaginaryFlow.Similarity
open Matrix

theorem matrix_action_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    Matrix.toEuclideanLin (A*B) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  apply WithLp.ofLp_injective
  change (A*B) *ᵥ x.ofLp = A *ᵥ (B *ᵥ x.ofLp)
  rw [Matrix.mulVec_mulVec]

theorem matrix_action_one {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) : Matrix.toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℂ) x = x := by
  apply WithLp.ofLp_injective
  change (1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ x.ofLp = x.ofLp
  exact Matrix.one_mulVec _

theorem inner_matrix_adjoint {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (Matrix.toEuclideanLin A x) y =
      inner ℂ x (Matrix.toEuclideanLin A.conjTranspose y) := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_inner_right _ _ _).symm

end Qatlib.Concepts.ImaginaryFlow.Similarity
