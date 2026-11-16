/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSubspaceProjectionTransport

@[expose] public section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Qatlib.Concepts.GibbsSource.SpectralGeom.ResidualTransport
open scoped BigOperators

/-! Canonical columns for a cut of the complete actual source eigenbasis.
The finite spectral-index count constructs an equal-rank exact basis internally,
so the final residual-to-projector estimate has no supplied true-basis witness. -/

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
namespace ResidualTransport

variable {D : ℕ}

/-- Source vector sum smul for the stated finite source data. -/
theorem source_vector_sum_smul {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (X : ι → Operator D) :
    sourceEuclideanVector (∑ i ∈ S, c i • X i) =
      ∑ i ∈ S, c i • sourceEuclideanVector (X i) := by
  ext a
  simp [sourceEuclideanVector, sourceVector, Matrix.sum_apply, Matrix.smul_apply]

noncomputable def sourceCutSpace
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin D × Fin D)) := by
  classical
  exact Submodule.span ℂ
    (S.image (fun i => (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis i) : Set _)

noncomputable def sourceCutBasis
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    OrthonormalBasis S ℂ (sourceCutSpace L hL S) := by
  classical
  exact OrthonormalBasis.span (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis.orthonormal S

noncomputable def sourceCutColumns
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (sourceCutSpace L hL S).subtypeL.comp
    ((sourceCutBasis L hL S).repr.symm : EuclideanSpace ℂ S →L[ℂ] sourceCutSpace L hL S)

/-- Source Cut Columns norm for the stated finite source data. -/
theorem sourceCutColumns_norm
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (z : EuclideanSpace ℂ S) :
    ‖sourceCutColumns L hL S z‖=‖z‖ := by
  change ‖(sourceCutBasis L hL S).repr.symm z‖=‖z‖
  exact LinearIsometryEquiv.norm_map _ _

/-- Source Cut Columns projection for the stated finite source data. -/
theorem sourceCutColumns_projection
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    trialProjection (sourceCutColumns L hL S)=sourceMap (sourceSpectralCut L hL S) := by
  classical
  have hs (x : EuclideanSpace ℂ (Fin D × Fin D)) :
      sourceMap (sourceSpectralCut L hL S) x =
        ∑ i : S, inner ℂ
          ((sourceSuperMatrix_isHermitian L hL).eigenvectorBasis i) x •
          (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis i := by
    obtain ⟨X, rfl⟩ := source_vector_surjective x
    rw [sourceMap_apply]
    change sourceEuclideanVector
      (∑ i ∈ S, hsInner (sourceEigenoperator L hL i) X • sourceEigenoperator L hL i)=_
    rw [source_vector_sum_smul]
    simp_rw [← sourceEuclideanVector_inner, sourceEuclideanVector_eigenoperator]
    exact (Finset.sum_coe_sort S _).symm
  unfold trialProjection sourceCutColumns
  rw [ContinuousLinearMap.adjoint_comp (sourceCutSpace L hL S).subtypeL
    ((sourceCutBasis L hL S).repr.symm : EuclideanSpace ℂ S →L[ℂ] sourceCutSpace L hL S),
    (sourceCutSpace L hL S).adjoint_subtypeL,
    (sourceCutBasis L hL S).repr.symm.adjoint_eq_symm]
  ext x : 1
  change (((sourceCutBasis L hL S).repr.symm
    ((sourceCutBasis L hL S).repr ((sourceCutSpace L hL S).orthogonalProjectionOnto x)) :
      sourceCutSpace L hL S) : EuclideanSpace ℂ (Fin D × Fin D))=_
  rw [LinearIsometryEquiv.symm_apply_apply,
    (sourceCutBasis L hL S).orthogonalProjectionOnto_apply_eq_sum, hs]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show ((sourceCutBasis L hL S i) : EuclideanSpace ℂ (Fin D × Fin D)) =
      (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis i from
    OrthonormalBasis.span_apply
      (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis.orthonormal S i]

noncomputable def sourceCutColumnsOfCard
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) {q : ℕ} (hcard : S.card=q) :
    EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (sourceCutColumns L hL S).comp
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Finset.equivFinOfCardEq hcard).symm) :
      EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ S)

/-- Source Cut Columns Of Card norm for the stated finite source data. -/
theorem sourceCutColumnsOfCard_norm
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) {q : ℕ} (hcard : S.card=q)
    (z : EuclideanSpace ℂ (Fin q)) :
    ‖sourceCutColumnsOfCard L hL S hcard z‖=‖z‖ := by
  rw [sourceCutColumnsOfCard, ContinuousLinearMap.comp_apply, sourceCutColumns_norm]
  exact LinearIsometryEquiv.norm_map _ _

/-- Source Cut Columns Of Card projection for the stated finite source data. -/
theorem sourceCutColumnsOfCard_projection
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) {q : ℕ} (hcard : S.card=q) :
    trialProjection (sourceCutColumnsOfCard L hL S hcard) =
      sourceMap (sourceSpectralCut L hL S) := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Finset.equivFinOfCardEq hcard).symm
  change trialProjection ((sourceCutColumns L hL S).comp
    (e : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ S))=_
  unfold trialProjection
  rw [ContinuousLinearMap.adjoint_comp (sourceCutColumns L hL S)
    (e : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ S), e.adjoint_eq_symm]
  ext x : 1
  change sourceCutColumns L hL S
    (e (e.symm ((sourceCutColumns L hL S).adjoint x)))=_
  rw [e.apply_symm_apply]
  exact congrArg (fun T : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
    EuclideanSpace ℂ (Fin D × Fin D) => T x) (sourceCutColumns_projection L hL S)

/-- Actual low-rank count supplies the exact spectral basis internally. -/
theorem source_low_trialProjection_sub_norm_le_of_card
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • G)
    {q : ℕ} {cutoff μ lam η : ℝ}
    (hcard : (sourcePositiveLowModes L hL cutoff).card=q)
    (U : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D))
    (hU : ∀ z, ‖U z‖ = ‖z‖)
    (hcut : cutoff < μ) (hgap : lam < μ)
    (hsep : ∀ i, 0 < sourceEigenvalues L hL i →
      cutoff < sourceEigenvalues L hL i → μ ≤ sourceEigenvalues L hL i)
    (hcenter : ∀ z, inner ℂ (sourceEuclideanVector G) (U z) = 0)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖trialResidual (sourceMap L) U‖ ≤ η) :
    ‖trialProjection U-sourceMap (sourcePositiveLowProjection L hL cutoff)‖
      ≤ η / (μ-lam) :=
  source_low_trialProjection_sub_norm_le L hL hpos G hker U
    (sourceCutColumnsOfCard L hL (sourcePositiveLowModes L hL cutoff) hcard)
    hU (sourceCutColumnsOfCard_norm L hL (sourcePositiveLowModes L hL cutoff) hcard)
    hcut hgap
    (sourceCutColumnsOfCard_projection L hL (sourcePositiveLowModes L hL cutoff) hcard)
    hsep hcenter hcap hres

end ResidualTransport
end Qatlib.Concepts.GibbsSource.SpectralGeom
