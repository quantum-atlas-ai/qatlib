/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.Similarity.LinearConjugacy
import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.MatrixEvolution
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime
open Qatlib.Concepts.ImaginaryFlow.Similarity

namespace Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity

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

theorem actual_tcTransform {d : ℕ} (H g : Op d) :
    tcTransform (expEquiv g) (Matrix.toEuclideanLin H) = Matrix.toEuclideanLin (tc H g) := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective
  change NormedSpace.exp (-g) *ᵥ (H *ᵥ (NormedSpace.exp g *ᵥ x.ofLp)) =
    (NormedSpace.exp (-g) * H * NormedSpace.exp g) *ᵥ x.ofLp
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem actual_eigenvector_iff {d : ℕ} (H g : Op d) (μ : ℂ) (φ : State d) :
    Module.End.HasEigenvector (Matrix.toEuclideanLin (tc H g)) μ φ ↔
      Module.End.HasEigenvector (Matrix.toEuclideanLin H) μ (expEquiv g φ) := by
  rw [← actual_tcTransform H g]
  exact tcTransform_hasEigenvector_iff _ _ μ φ

theorem actual_eigenvalue_iff {d : ℕ} (H g : Op d) (μ : ℂ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin (tc H g)) μ ↔
      Module.End.HasEigenvalue (Matrix.toEuclideanLin H) μ := by
  rw [← actual_tcTransform H g]
  exact tcTransform_hasEigenvalue_iff _ _ μ

theorem actual_left_eigenfunctional {d : ℕ} (H g : Op d) {μ : ℂ}
    {w : Module.Dual ℂ (State d)} (hw : (Matrix.toEuclideanLin H).dualMap w = μ • w) :
    (Matrix.toEuclideanLin (tc H g)).dualMap (w.comp (expEquiv g).toLinearMap) =
      μ • w.comp (expEquiv g).toLinearMap := by
  rw [← actual_tcTransform H g]
  exact tcTransform_dualMap_hasEigenvector _ _ hw

end Qatlib.Papers.TranscorrChem20.MainResults.TCSimilarity
