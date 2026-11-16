/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSpectralTraceLeakage
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section


/-! A dimension-free residual separation estimate for a complete trial block.
The norming singular vector is obtained internally from a compact sphere, and
the Gram eigenvector equation follows from its actual extremum. -/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
namespace ResidualTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An actual maximizing singular vector, with no supplied eigenvector witness. -/
theorem exists_norming_singular_vector [Nontrivial E] (B : E →L[ℂ] F) :
    ∃ z : E, ‖z‖ = 1 ∧ ‖B z‖ = ‖B‖ ∧
      B.adjoint (B z) = ((‖B‖ ^ 2 : ℝ) : ℂ) • z := by
  let := InnerProductSpace.rclikeToReal ℂ E
  let := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨u, hu⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  have hs : (Metric.sphere (0 : E) 1).Nonempty := ⟨u, by simpa using hu⟩
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hs
    B.continuous.norm.continuousOn
  have hzn : ‖z‖ = 1 := by simpa using hz
  have hBn : ‖B z‖ = ‖B‖ := by
    apply le_antisymm
    · simpa only [hzn, mul_one] using B.le_opNorm z
    · exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
        (fun x hx => hmax (by simpa using hx))
  let G : E →L[ℂ] E := B.adjoint.comp B
  have hG : IsSelfAdjoint G := B.isPositive_adjoint_comp_self.isSelfAdjoint
  have hsq (x : E) : G.reApplyInnerSelf x = ‖B x‖ ^ 2 := by
    exact (B.apply_norm_sq_eq_inner_adjoint_left x).symm
  have hmaxG : IsMaxOn G.reApplyInnerSelf (Metric.sphere (0 : E) ‖z‖) z := by
    intro x hx
    change G.reApplyInnerSelf x ≤ G.reApplyInnerSelf z
    rw [hsq, hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmax (by simpa [hzn] using hx)) 2
  have he := hG.eq_smul_self_of_isLocalExtrOn (Or.inr hmaxG.isLocalMaxOn)
  have hq : G.rayleighQuotient z = ‖B‖ ^ 2 := by
    rw [ContinuousLinearMap.rayleighQuotient, hsq, hzn, hBn]
    norm_num
  refine ⟨z, hzn, hBn, ?_⟩
  simpa only [hq, G, ContinuousLinearMap.comp_apply] using! he

/-- The one-sided Sylvester estimate only needs the lower quadratic-form bound
on the image of the actual rectangular block B. The entire residual is used. -/
theorem norm_le_residual_div_of_range_coercive
    (A : F →L[ℂ] F) (B : E →L[ℂ] F) (T : E →L[ℂ] E)
    {μ lam : ℝ} (hgap : lam < μ)
    (hA : ∀ z, μ * ‖B z‖ ^ 2 ≤ (inner ℂ (B z) (A (B z))).re)
    (hT : ∀ z, (inner ℂ z (T z)).re ≤ lam * ‖z‖ ^ 2) :
    ‖B‖ ≤ ‖A.comp B - B.comp T‖ / (μ - lam) := by
  by_cases hB : B = 0
  · simp [hB]
  have : Nontrivial E := by
    by_contra! h
    have : Subsingleton E := h
    exact hB (Subsingleton.elim _ _)
  obtain ⟨z, hzn, hBn, heig⟩ := exists_norming_singular_vector B
  have hs : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hfirst := hA z
  rw [hBn] at hfirst
  have hsecond := hT z
  rw [hzn] at hsecond
  norm_num only [one_pow, mul_one] at hsecond
  have hid :
      (inner ℂ (B z) ((A.comp B - B.comp T) z)).re =
        (inner ℂ (B z) (A (B z))).re -
          ‖B‖ ^ 2 * (inner ℂ z (T z)).re := by
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      inner_sub_right, Complex.sub_re]
    rw [← B.adjoint_inner_left (T z) (B z), heig, inner_smul_left]
    simp [pow_two]
  have hupper :
      (inner ℂ (B z) ((A.comp B - B.comp T) z)).re ≤
        ‖B‖ * ‖A.comp B - B.comp T‖ := by
    calc
      _ ≤ ‖inner ℂ (B z) ((A.comp B - B.comp T) z)‖ := Complex.re_le_norm _
      _ ≤ ‖B z‖ * ‖(A.comp B - B.comp T) z‖ := norm_inner_le_norm _ _
      _ ≤ ‖B z‖ * (‖A.comp B - B.comp T‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left ((A.comp B - B.comp T).le_opNorm z) (norm_nonneg _)
      _ = _ := by rw [hBn, hzn, mul_one]
  have hmul := mul_le_mul_of_nonneg_left hsecond (sq_nonneg ‖B‖)
  have hmain : ‖B‖ * ((μ - lam) * ‖B‖) ≤
      ‖B‖ * ‖A.comp B - B.comp T‖ := by
    rw [hid] at hupper
    nlinarith
  have hcancel := (mul_le_mul_iff_right₀ hs).mp hmain
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  nlinarith

/-- The usual separated Sylvester bound, in the actual operator norm. -/
theorem norm_le_residual_div
    (A : F →L[ℂ] F) (B : E →L[ℂ] F) (T : E →L[ℂ] E)
    {μ lam : ℝ} (hgap : lam < μ)
    (hA : ∀ y, μ * ‖y‖ ^ 2 ≤ (inner ℂ y (A y)).re)
    (hT : ∀ z, (inner ℂ z (T z)).re ≤ lam * ‖z‖ ^ 2) :
    ‖B‖ ≤ ‖A.comp B - B.comp T‖ / (μ - lam) :=
  norm_le_residual_div_of_range_coercive A B T hgap (fun z => hA (B z)) hT

/-- A self-adjoint idempotent is a contraction in the actual Hilbert norm. -/
theorem projection_norm_le
    (Q : F →L[ℂ] F) (hQ : IsSelfAdjoint Q)
    (hQQ : ∀ y, Q (Q y) = Q y) (y : F) : ‖Q y‖ ≤ ‖y‖ := by
  have he : inner ℂ (Q y) (Q y) = inner ℂ (Q y) y := by
    have h := (hQ.isSymmetric (Q y) y).symm
    change inner ℂ (Q y) (Q y) = inner ℂ (Q (Q y)) y at h
    simpa only [hQQ] using h
  have hs : ‖Q y‖ ^ 2 ≤ ‖Q y‖ * ‖y‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), he]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  by_contra! h
  have hq := norm_nonneg (Q y)
  have hy := norm_nonneg y
  nlinarith

/-- Compress the complete trial residual by a genuine orthogonal projector.
Only the retained range of Q needs the omitted-spectrum floor. -/
theorem projected_block_norm_le_residual_div
    (K Q : F →L[ℂ] F) (U : E →L[ℂ] F) (T : E →L[ℂ] E)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ y, Q (Q y) = Q y)
    (hcomm : ∀ y, K (Q y) = Q (K y))
    {μ lam : ℝ} (hgap : lam < μ)
    (hfloor : ∀ y, Q y = y → μ * ‖y‖ ^ 2 ≤ (inner ℂ y (K y)).re)
    (hcap : ∀ z, (inner ℂ z (T z)).re ≤ lam * ‖z‖ ^ 2) :
    ‖Q.comp U‖ ≤ ‖K.comp U - U.comp T‖ / (μ - lam) := by
  have hbase := norm_le_residual_div_of_range_coercive K (Q.comp U) T hgap
    (fun z => hfloor (Q (U z)) (hQQ (U z))) hcap
  have hid :
      K.comp (Q.comp U) - (Q.comp U).comp T =
        Q.comp (K.comp U - U.comp T) := by
    ext z
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    rw [hcomm]
  rw [hid] at hbase
  have hres : ‖Q.comp (K.comp U - U.comp T)‖ ≤ ‖K.comp U - U.comp T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    exact (projection_norm_le Q hQ hQQ _).trans ((K.comp U - U.comp T).le_opNorm z)
  exact hbase.trans (div_le_div_of_nonneg_right hres (sub_pos.mpr hgap).le)

/-- A certified norm bound for the complete residual gives the directed
outside trial-block bound, with no dimension factor. For an isometric U this
is the directed subspace angle. -/
theorem projected_block_norm_le
    (K Q : F →L[ℂ] F) (U : E →L[ℂ] F) (T : E →L[ℂ] E)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ y, Q (Q y) = Q y)
    (hcomm : ∀ y, K (Q y) = Q (K y))
    {μ lam η : ℝ} (hgap : lam < μ)
    (hfloor : ∀ y, Q y = y → μ * ‖y‖ ^ 2 ≤ (inner ℂ y (K y)).re)
    (hcap : ∀ z, (inner ℂ z (T z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖K.comp U - U.comp T‖ ≤ η) :
    ‖Q.comp U‖ ≤ η / (μ - lam) :=
  (projected_block_norm_le_residual_div K Q U T hQ hQQ hcomm hgap hfloor hcap).trans
    (div_le_div_of_nonneg_right hres (sub_pos.mpr hgap).le)

/-- The quadratic compression of all trial columns. For an isometric U this is
the Ritz compression; it is not a collection of independent scalar quotients. -/
noncomputable def trialCompression (K : F →L[ℂ] F) (U : E →L[ℂ] F) :
    E →L[ℂ] E := U.adjoint.comp (K.comp U)

/-- Residual of the complete trial block for its actual compression. -/
noncomputable def trialResidual (K : F →L[ℂ] F) (U : E →L[ℂ] F) :
    E →L[ℂ] F := K.comp U - U.comp (trialCompression K U)

/-- The rectangular bridge specialized to the actual trial compression. -/
theorem trial_outside_norm_le
    (K Q : F →L[ℂ] F) (U : E →L[ℂ] F)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ y, Q (Q y) = Q y)
    (hcomm : ∀ y, K (Q y) = Q (K y))
    {μ lam η : ℝ} (hgap : lam < μ)
    (hfloor : ∀ y, Q y = y → μ * ‖y‖ ^ 2 ≤ (inner ℂ y (K y)).re)
    (hcap : ∀ z, (inner ℂ z (trialCompression K U z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖trialResidual K U‖ ≤ η) :
    ‖Q.comp U‖ ≤ η / (μ - lam) :=
  projected_block_norm_le K Q U (trialCompression K U) hQ hQQ hcomm hgap hfloor hcap hres

/-- Orthogonal trial projection when the complete column map is isometric. -/
noncomputable def trialProjection (U : E →L[ℂ] F) : F →L[ℂ] F :=
  U.comp U.adjoint

omit [FiniteDimensional ℂ E] in
/-- Trial Projection self Adjoint for the stated finite source data. -/
theorem trialProjection_selfAdjoint (U : E →L[ℂ] F) :
    IsSelfAdjoint (trialProjection U) := by
  simpa only [trialProjection, ContinuousLinearMap.adjoint_adjoint] using
    U.adjoint.isPositive_adjoint_comp_self.isSelfAdjoint

omit [FiniteDimensional ℂ E] in
/-- Trial Projection idempotent for the stated finite source data. -/
theorem trialProjection_idempotent (U : E →L[ℂ] F)
    (hU : ∀ z, ‖U z‖ = ‖z‖) (x : F) :
    trialProjection U (trialProjection U x) = trialProjection U x := by
  have hu := U.norm_map_iff_adjoint_comp_self.mp hU
  have hv : U.adjoint (U (U.adjoint x)) = U.adjoint x := by
    have h := congrArg (fun T : E →L[ℂ] E => T (U.adjoint x)) hu
    simpa using h
  change U (U.adjoint (U (U.adjoint x))) = U (U.adjoint x)
  rw [hv]

omit [FiniteDimensional ℂ E] in
/-- Isometric trial coordinates preserve the directed projection norm exactly.
Thus the preceding block estimate becomes a genuine subspace estimate. -/
theorem norm_composed_trialProjection_eq
    (Q : F →L[ℂ] F) (U : E →L[ℂ] F) (hU : ∀ z, ‖U z‖ = ‖z‖) :
    ‖Q.comp (trialProjection U)‖ = ‖Q.comp U‖ := by
  have hu : ‖U‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (by norm_num)
      (fun z hz => by rw [hU, hz])
  have ha : ‖U.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hu
  have hid : (Q.comp (trialProjection U)).comp U = Q.comp U := by
    have he := U.norm_map_iff_adjoint_comp_self.mp hU
    ext z
    have hz : U.adjoint (U z) = z := by
      have h := congrArg (fun T : E →L[ℂ] E => T z) he
      simpa using h
    change Q (U (U.adjoint (U z))) = Q (U z)
    rw [hz]
  apply le_antisymm
  · change ‖Q.comp (U.comp U.adjoint)‖ ≤ ‖Q.comp U‖
    rw [← ContinuousLinearMap.comp_assoc]
    exact ((Q.comp U).opNorm_comp_le U.adjoint).trans
      (by simpa using mul_le_mul_of_nonneg_left ha (norm_nonneg (Q.comp U)))
  · rw [← hid]
    exact ((Q.comp (trialProjection U)).opNorm_comp_le U).trans
      (by simpa using mul_le_mul_of_nonneg_left hu (norm_nonneg (Q.comp (trialProjection U))))

section ActualSource
variable {D : ℕ}

/-- Continuous action of the complete source matrix on its genuine D²-dimensional
complex Hilbert space. The matrix-entry sup norm is not used. -/
noncomputable def sourceMap (L : Operator D →ₗ[ℂ] Operator D) :
    EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  Matrix.toEuclideanCLM (n := Fin D × Fin D) (𝕜 := ℂ) (sourceSuperMatrix L)

/-- Source Map apply for the stated finite source data. -/
theorem sourceMap_apply (L : Operator D →ₗ[ℂ] Operator D) (X : Operator D) :
    sourceMap L (sourceEuclideanVector X) = sourceEuclideanVector (L X) := by
  change WithLp.toLp 2 (sourceSuperMatrix L *ᵥ sourceVector X) =
    WithLp.toLp 2 (sourceVector (L X))
  rw [sourceSuperMatrix_mulVec]

/-- Source vector surjective for the stated finite source data. -/
theorem source_vector_surjective :
    Function.Surjective (sourceEuclideanVector (D := D)) := by
  intro x
  refine ⟨sourceUnvector (WithLp.ofLp x), ?_⟩
  simp [sourceEuclideanVector]

/-- Source vector injective for the stated finite source data. -/
theorem source_vector_injective :
    Function.Injective (sourceEuclideanVector (D := D)) := by
  intro X Y h
  exact congrArg (fun x => sourceUnvector (WithLp.ofLp x)) h

/-- Source vector norm sq for the stated finite source data. -/
theorem source_vector_norm_sq (X : Operator D) :
    ‖sourceEuclideanVector X‖ ^ 2 = (hsInner X X).re := by
  rw [← sourceEuclideanVector_inner]
  exact norm_sq_eq_re_inner (𝕜 := ℂ) _

/-- Source Map self Adjoint for the stated finite source data. -/
theorem sourceMap_selfAdjoint
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    IsSelfAdjoint (sourceMap L) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  obtain ⟨X, rfl⟩ := source_vector_surjective x
  obtain ⟨Y, rfl⟩ := source_vector_surjective y
  change inner ℂ (sourceMap L (sourceEuclideanVector X)) (sourceEuclideanVector Y) =
    inner ℂ (sourceEuclideanVector X) (sourceMap L (sourceEuclideanVector Y))
  simp only [sourceMap_apply, sourceEuclideanVector_inner]
  exact hL X Y

/-- Spectral Cut commutes for the stated finite source data. -/
theorem spectralCut_commutes
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (X : Operator D) :
    L (sourceSpectralCut L hL S X) = sourceSpectralCut L hL S (L X) := by
  classical
  change L (∑ i ∈ S, hsInner (sourceEigenoperator L hL i) X •
      sourceEigenoperator L hL i) =
    ∑ i ∈ S, hsInner (sourceEigenoperator L hL i) (L X) • sourceEigenoperator L hL i
  simp only [map_sum, map_smul, sourceEigenoperator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hL, sourceEigenoperator_apply, hsInner_smul_left]
  simp only [star_ofReal, smul_smul]
  rw [mul_comm]

/-- Spectral Cut coercive for the stated finite source data. -/
theorem spectralCut_coercive
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) {μ : ℝ}
    (hfloor : ∀ i ∈ S, μ ≤ sourceEigenvalues L hL i)
    (X : Operator D) (hX : sourceSpectralCut L hL S X = X) :
    μ * (hsInner X X).re ≤ (hsInner X (L X)).re := by
  classical
  have hc (i : Fin D × Fin D) (hi : i ∉ S) :
      hsInner (sourceEigenoperator L hL i) X = 0 := by
    rw [← hX, sourceSpectralCut_coefficient, ite_eq_right hi]
  rw [source_hsNormSq_eq_sum_coefficients L hL, source_energy_eq_sum_eigenvalues L hL,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hmem : i ∈ S
  · exact mul_le_mul_of_nonneg_right (hfloor i hmem) (Complex.normSq_nonneg _)
  · simp [hc i hmem]

/-- Actual high spectral modes, retaining multiplicities of the complete source.
No trial eigenvalue ordering or chosen approximate eigenvectors enter this set. -/
noncomputable def highModes
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (μ : ℝ) :
    Finset (Fin D × Fin D) := by
  classical
  exact Finset.univ.filter (fun i => μ ≤ sourceEigenvalues L hL i)

/-- The actual spectral cut at the omitted-spectrum threshold. -/
noncomputable def highProjection
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (μ : ℝ) :
    Operator D →ₗ[ℂ] Operator D := sourceSpectralCut L hL (highModes L hL μ)

/-- A whole-block residual controls the actual high spectral component. All
projection properties and the range floor follow from the true eigenbasis. -/
theorem source_high_trial_norm_le
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (U : E →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D))
    {μ lam η : ℝ} (hgap : lam < μ)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖trialResidual (sourceMap L) U‖ ≤ η) :
    ‖(sourceMap (highProjection L hL μ)).comp U‖ ≤ η / (μ - lam) := by
  classical
  let Q := highProjection L hL μ
  have hQ : SourceSelfAdjoint Q := sourceSpectralCut_selfAdjoint L hL _
  have hQQ (x : EuclideanSpace ℂ (Fin D × Fin D)) :
      sourceMap Q (sourceMap Q x) = sourceMap Q x := by
    obtain ⟨X, rfl⟩ := source_vector_surjective x
    simp only [sourceMap_apply]
    exact congrArg sourceEuclideanVector (sourceSpectralCut_idempotent L hL _ X)
  have hcomm (x : EuclideanSpace ℂ (Fin D × Fin D)) :
      sourceMap L (sourceMap Q x) = sourceMap Q (sourceMap L x) := by
    obtain ⟨X, rfl⟩ := source_vector_surjective x
    simp only [sourceMap_apply]
    exact congrArg sourceEuclideanVector (spectralCut_commutes L hL _ X)
  have hfloor (x : EuclideanSpace ℂ (Fin D × Fin D)) (hx : sourceMap Q x = x) :
      μ * ‖x‖ ^ 2 ≤ (inner ℂ x (sourceMap L x)).re := by
    obtain ⟨X, rfl⟩ := source_vector_surjective x
    rw [sourceMap_apply] at hx
    have hfix : Q X = X := source_vector_injective hx
    rw [source_vector_norm_sq, sourceMap_apply, sourceEuclideanVector_inner]
    exact spectralCut_coercive L hL _ (fun i hi => (Finset.mem_filter.mp hi).2) X hfix
  exact trial_outside_norm_le (sourceMap L) (sourceMap Q) U
    (sourceMap_selfAdjoint Q hQ) hQQ hcomm hgap hfloor hcap hres

/-- On the true kernel complement, the high projection is exactly the
complement of the actual positive-low projection. The unique-kernel hypothesis
is indispensable and is not replaced by a count of positive eigenvalues. -/
theorem highProjection_eq_sub_low_of_centered
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • G)
    {cutoff μ : ℝ} (hcut : cutoff < μ)
    (hsep : ∀ i, 0 < sourceEigenvalues L hL i →
      cutoff < sourceEigenvalues L hL i → μ ≤ sourceEigenvalues L hL i)
    (X : Operator D) (horth : hsInner G X = 0) :
    highProjection L hL μ X = X - sourcePositiveLowProjection L hL cutoff X := by
  classical
  have hc (i : Fin D × Fin D) :
      hsInner (sourceEigenoperator L hL i) (highProjection L hL μ X) =
        hsInner (sourceEigenoperator L hL i)
          (X - sourcePositiveLowProjection L hL cutoff X) := by
    simp only [highProjection, sourcePositiveLowProjection, sourceSpectralCut_coefficient,
      hsInner_sub_right]
    by_cases hi0 : sourceEigenvalues L hL i = 0
    · have hz : L (sourceEigenoperator L hL i) = 0 := by
        rw [sourceEigenoperator_apply, hi0, Complex.ofReal_zero, zero_smul]
      obtain ⟨c, he⟩ := hker (sourceEigenoperator L hL i) hz
      have hzcoeff : hsInner (sourceEigenoperator L hL i) X = 0 := by
        rw [he, hsInner_smul_left, horth, mul_zero]
      simp [hzcoeff]
    have hi : 0 < sourceEigenvalues L hL i :=
      lt_of_le_of_ne (sourceEigenvalues_nonneg L hL hpos i) (Ne.symm hi0)
    by_cases hlow : sourceEigenvalues L hL i ≤ cutoff
    · have hlo : i ∈ sourcePositiveLowModes L hL cutoff := by
        simp only [sourcePositiveLowModes, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, hlow⟩
      have hhi : i ∉ highModes L hL μ := by
        simp only [highModes, Finset.mem_filter, Finset.mem_univ, true_and]
        linarith
      rw [ite_eq_right hhi, ite_eq_left hlo, sub_self]
    · have hlo : i ∉ sourcePositiveLowModes L hL cutoff := by
        simp only [sourcePositiveLowModes, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => hlow h.2
      have hhi : i ∈ highModes L hL μ := by
        simp only [highModes, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hsep i hi (lt_of_not_ge hlow)
      rw [ite_eq_left hhi, ite_eq_right hlo, sub_zero]
  calc
    highProjection L hL μ X =
        ∑ i, hsInner (sourceEigenoperator L hL i) (highProjection L hL μ X) •
          sourceEigenoperator L hL i := sourceEigenoperator_expansion L hL _
    _ = ∑ i, hsInner (sourceEigenoperator L hL i)
          (X - sourcePositiveLowProjection L hL cutoff X) •
            sourceEigenoperator L hL i := by simp_rw [hc]
    _ = X - sourcePositiveLowProjection L hL cutoff X :=
      (sourceEigenoperator_expansion L hL _).symm

/-- Directed whole-block transport into the actual positive-low subspace.
The source's unique kernel, true omitted spectrum, Gibbs orthogonality, and
complete trial residual remain separate, explicit hypotheses. -/
theorem source_low_trial_norm_le
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • G)
    (U : E →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D))
    {cutoff μ lam η : ℝ} (hcut : cutoff < μ) (hgap : lam < μ)
    (hsep : ∀ i, 0 < sourceEigenvalues L hL i →
      cutoff < sourceEigenvalues L hL i → μ ≤ sourceEigenvalues L hL i)
    (hcenter : ∀ z, inner ℂ (sourceEuclideanVector G) (U z) = 0)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖trialResidual (sourceMap L) U‖ ≤ η) :
    ‖((ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin D × Fin D))) -
        sourceMap (sourcePositiveLowProjection L hL cutoff)).comp U‖ ≤ η / (μ - lam) := by
  have hid :
      (sourceMap (highProjection L hL μ)).comp U =
        ((ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin D × Fin D))) -
          sourceMap (sourcePositiveLowProjection L hL cutoff)).comp U := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      ContinuousLinearMap.id_apply]
    obtain ⟨X, hX⟩ := source_vector_surjective (U z)
    have ho : hsInner G X = 0 := by
      rw [← sourceEuclideanVector_inner, hX]
      exact hcenter z
    rw [← hX, sourceMap_apply, sourceMap_apply,
      highProjection_eq_sub_low_of_centered L hL hpos G hker hcut hsep X ho]
    rfl
  rw [← hid]
  exact source_high_trial_norm_le L hL U hgap hcap hres

/-- For an isometric trial basis, the full residual controls the genuine
directed difference of its orthogonal projector from the actual low space. -/
theorem source_low_trialProjection_norm_le
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X = 0 → ∃ c : ℂ, X = c • G)
    (U : E →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D))
    (hU : ∀ z, ‖U z‖ = ‖z‖)
    {cutoff μ lam η : ℝ} (hcut : cutoff < μ) (hgap : lam < μ)
    (hsep : ∀ i, 0 < sourceEigenvalues L hL i →
      cutoff < sourceEigenvalues L hL i → μ ≤ sourceEigenvalues L hL i)
    (hcenter : ∀ z, inner ℂ (sourceEuclideanVector G) (U z) = 0)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re ≤ lam * ‖z‖ ^ 2)
    (hres : ‖trialResidual (sourceMap L) U‖ ≤ η) :
    ‖((ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin D × Fin D))) -
        sourceMap (sourcePositiveLowProjection L hL cutoff)).comp (trialProjection U)‖
      ≤ η / (μ - lam) := by
  rw [norm_composed_trialProjection_eq _ U hU]
  exact source_low_trial_norm_le L hL hpos G hker U hcut hgap hsep hcenter hcap hres


end ActualSource

end ResidualTransport
end Qatlib.Concepts.GibbsSource.SpectralGeom
