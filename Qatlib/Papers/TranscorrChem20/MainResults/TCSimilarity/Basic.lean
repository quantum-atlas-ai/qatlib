/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.Similarity.LinearConjugacy
import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.MatrixEvolution

/-!
# Exact transcorrelated similarity and eigenvectors

This module packages multiplication by `exp g` as the linear equivalence `expEquiv`. It connects
the concrete matrix `tc H g` to abstract similarity, transports right eigenvectors and
eigenvalues, and transforms left eigenfunctionals by composition. See [McArdleTew2020].

## Main statements

* `actual_tcTransform`: Identification with the abstract transcorrelated transform.
* `actual_eigenvalue_iff`: Equivalence of eigenvalue predicates.
* `actual_left_eigenfunctional`: Transport of left eigenfunctionals.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
open Qatlib.Concepts.ImaginaryFlow.Similarity

namespace Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity

/-- The complex linear equivalence acting by `exp g`, with inverse acting by `exp (-g)`. -/
def expEquiv {d : ℕ} (g : Op d) : State d ≃ₗ[ℂ] State d :=
  { Matrix.toEuclideanLin (NormedSpace.exp g) with
    invFun := Matrix.toEuclideanLin (NormedSpace.exp (-g))
    left_inv := by
      intro x
      apply WithLp.ofLp_injective
      change NormedSpace.exp (-g) *ᵥ (NormedSpace.exp g *ᵥ x.ofLp) = x.ofLp
      rw [Matrix.mulVec_mulVec, (actual_exp_inverse g).1, Matrix.one_mulVec]
    right_inv := by
      intro x
      apply WithLp.ofLp_injective
      change NormedSpace.exp g *ᵥ (NormedSpace.exp (-g) *ᵥ x.ofLp) = x.ofLp
      rw [Matrix.mulVec_mulVec, (actual_exp_inverse g).2, Matrix.one_mulVec] }

/-- The abstract transform by `expEquiv g` of the linear operator of `H` is the linear operator
of `tc H g`. -/
theorem actual_tcTransform {d : ℕ} (H g : Op d) :
    tcTransform (expEquiv g) (Matrix.toEuclideanLin H) = Matrix.toEuclideanLin (tc H g) := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective
  change NormedSpace.exp (-g) *ᵥ (H *ᵥ (NormedSpace.exp g *ᵥ x.ofLp)) =
    (NormedSpace.exp (-g) * H * NormedSpace.exp g) *ᵥ x.ofLp
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- A state is an eigenvector of `tc H g` exactly when its image under `expEquiv g` is an
eigenvector of `H` with the same eigenvalue. -/
theorem actual_eigenvector_iff {d : ℕ} (H g : Op d) (μ : ℂ) (φ : State d) :
    Module.End.HasEigenvector (Matrix.toEuclideanLin (tc H g)) μ φ ↔
      Module.End.HasEigenvector (Matrix.toEuclideanLin H) μ (expEquiv g φ) := by
  rw [← actual_tcTransform H g]
  exact tcTransform_hasEigenvector_iff _ _ μ φ

/-- The original and transcorrelated linear operators have the same eigenvalues. See
[McArdleTew2020]. -/
theorem actual_eigenvalue_iff {d : ℕ} (H g : Op d) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (tc H g)) μ ↔
      Module.End.HasEigenvalue (Matrix.toEuclideanLin H) μ := by
  rw [← actual_tcTransform H g]
  exact tcTransform_hasEigenvalue_iff _ _ μ

/-- Composing a left eigenfunctional of `H` with `expEquiv g` produces a left eigenfunctional of
`tc H g` with the same eigenvalue. -/
theorem actual_left_eigenfunctional {d : ℕ} (H g : Op d) {μ : ℂ}
    {w : Module.Dual ℂ (State d)} (hw : (Matrix.toEuclideanLin H).dualMap w = μ • w) :
    (Matrix.toEuclideanLin (tc H g)).dualMap (w.comp (expEquiv g).toLinearMap) =
      μ • w.comp (expEquiv g).toLinearMap := by
  rw [← actual_tcTransform H g]
  exact tcTransform_dualMap_hasEigenvector _ _ hw

end Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity
