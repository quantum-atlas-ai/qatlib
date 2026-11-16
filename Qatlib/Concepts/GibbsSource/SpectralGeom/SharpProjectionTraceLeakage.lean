/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Qatlib.Concepts.GibbsSource.SpectralGeom.SharpProjectionLeakage
public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSpectralTraceLeakage

@[expose] public section


/-! Sharp leakage bounds for a whole finite family and its projection trace.
The Hilbert sum norm preserves correlations rather than replacing them by scalar alignment. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open scoped BigOperators

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
namespace SharpProjectionLeakage
open ResidualTransport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*} [Fintype ι]

/-- Apply the projection geometry to a whole family with its Hilbert sum norm.
This is a block estimate, so no scalar Jensen or eigenvalue alignment is assumed. -/
theorem projection_family_amplitude_le
    (P R : F →L[ℂ] F)
    (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    {eps : ℝ} (heps : 0≤eps) (heps1 : eps≤1) (hdist : ‖P-R‖≤eps)
    (v : ι → F) :
    Real.sqrt (1-eps^2)*Real.sqrt (∑ i, ‖P (v i)‖^2)-
      eps*Real.sqrt (∑ i, ‖v i-P (v i)‖^2)≤
      Real.sqrt (∑ i, ‖R (v i)‖^2) := by
  let pv : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun i => P (v i))
  let rp : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun i => R (P (v i)))
  let wv : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun i => v i-P (v i))
  let rwv : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun i => R (v i-P (v i)))
  let rv : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun i => R (v i))
  have hl : Real.sqrt (1-eps^2)*‖pv‖≤‖rp‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := projected_range_norm_ge P R hPP hR hRR heps heps1 hdist (v i)
    have hs := pow_le_pow_left₀
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) h 2
    simpa only [mul_pow] using hs
  have hu : ‖rwv‖≤eps*‖wv‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg heps (norm_nonneg _))).mp
    rw [mul_pow,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hzero : P (v i-P (v i))=0 := by rw [map_sub,hPP,sub_self]
    have hn : ‖R (v i-P (v i))‖≤eps*‖v i-P (v i)‖ := by
      calc
        _ = ‖(P-R) (v i-P (v i))‖ := by
          rw [_root_.sub_apply,hzero,zero_sub,norm_neg]
        _ ≤ ‖P-R‖*‖v i-P (v i)‖ := (P-R).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_right hdist (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    simpa only [mul_pow] using hs
  have heq : rp=rv-rwv := by
    ext i
    change R (P (v i))=R (v i)-R (v i-P (v i))
    rw [map_sub]
    abel
  have ht : ‖rp‖≤‖rv‖+‖rwv‖ := by rw [heq]; exact norm_sub_le _ _
  have h : Real.sqrt (1-eps^2)*‖pv‖-eps*‖wv‖≤‖rv‖ := by linarith
  simpa only [PiLp.norm_eq_of_L2] using h

/-- Projection family square le for the stated finite source data. -/
theorem projection_family_square_le
    (P R : F →L[ℂ] F)
    (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    {eps : ℝ} (heps : 0≤eps) (heps1 : eps≤1) (hdist : ‖P-R‖≤eps)
    (v : ι → F) :
    (max 0 (Real.sqrt (1-eps^2)*Real.sqrt (∑ i, ‖P (v i)‖^2)-
      eps*Real.sqrt (∑ i, ‖v i-P (v i)‖^2)))^2≤∑ i, ‖R (v i)‖^2 := by
  have h := projection_family_amplitude_le P R hPP hR hRR heps heps1 hdist v
  have hm := max_le (Real.sqrt_nonneg _) h
  have hs := pow_le_pow_left₀ (le_max_left _ _) hm 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg (fun i hi => sq_nonneg _))] at hs

/-- Complement family square le for the stated finite source data. -/
theorem complement_family_square_le
    (P R : F →L[ℂ] F)
    (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    {eps : ℝ} (heps : 0≤eps) (heps1 : eps≤1) (hdist : ‖P-R‖≤eps)
    (v : ι → F) :
    (max 0 (Real.sqrt (1-eps^2)*Real.sqrt (∑ i, ‖v i-P (v i)‖^2)-
      eps*Real.sqrt (∑ i, ‖P (v i)‖^2)))^2≤∑ i, ‖v i-R (v i)‖^2 := by
  have hd : ‖(ContinuousLinearMap.id ℂ F-P)-(ContinuousLinearMap.id ℂ F-R)‖≤eps := by
    have he : (ContinuousLinearMap.id ℂ F-P)-(ContinuousLinearMap.id ℂ F-R)=R-P := by abel
    rw [he,norm_sub_rev]
    exact hdist
  have h := projection_family_square_le (ContinuousLinearMap.id ℂ F-P)
    (ContinuousLinearMap.id ℂ F-R) (complement_idempotent P hPP)
    (complement_selfAdjoint R hR) (complement_idempotent R hRR) heps heps1 hd v
  have he (x : F) : x-(x-P x)=P x := by abel
  simpa only [_root_.sub_apply,ContinuousLinearMap.id_apply,he] using h


variable {D : ℕ}

/-- Hilbert sum norm of the projected band columns equals the true source trace. -/
theorem source_projection_family_mass
    (P Q : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hPP : ∀ X, P (P X)=P X)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X) :
    (∑ i, ‖sourceEuclideanVector (P (Q (sourceEigenoperator Q hQ i)))‖^2)=
      sourceTrace (Q.comp P) := by
  simp only [source_vector_norm_sq]
  calc
    _ = ∑ i, (hsInner (sourceEigenoperator Q hQ i)
        ((Q.comp (P.comp Q)) (sourceEigenoperator Q hQ i))).re := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (source_projection_compression_energy Q P hQ hP hPP _).symm
    _ = sourceTrace (Q.comp (P.comp Q)) :=
      (sourceTrace_eq_sum_eigenoperators Q _ hQ).symm
    _ = _ := sourceTrace_projection_compression Q P hQQ

/-- Source band family mass for the stated finite source data. -/
theorem source_band_family_mass
    (Q : Operator D →ₗ[ℂ] Operator D)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X) :
    (∑ i, ‖sourceEuclideanVector (Q (sourceEigenoperator Q hQ i))‖^2)=sourceTrace Q := by
  have h := source_projection_family_mass Q Q hQ hQQ hQ hQQ
  have he : Q.comp Q=Q := by ext X : 1; exact hQQ X
  simpa only [hQQ,he] using h

/-- Source projection family complement mass for the stated finite source data. -/
theorem source_projection_family_complement_mass
    (P Q : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hPP : ∀ X, P (P X)=P X)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X) :
    (∑ i, ‖sourceEuclideanVector (Q (sourceEigenoperator Q hQ i))-
      sourceEuclideanVector (P (Q (sourceEigenoperator Q hQ i)))‖^2)=
      sourceTrace Q-sourceTrace (Q.comp P) := by
  simp only [← source_vector_sub,source_vector_norm_sq,
    source_projection_pythagoras P hP hPP,Finset.sum_sub_distrib]
  rw [← source_band_family_mass Q hQ hQQ,
    ← source_projection_family_mass P Q hP hPP hQ hQQ]
  simp only [source_vector_norm_sq]

/-- Band-side Hilbert-sum transport uses the band's trace, including an empty
band. No differentiability or Jensen premise is required. -/
theorem source_trace_complement_sharp_transport
    (P R Q : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hPP : ∀ X, P (P X)=P X)
    (hR : SourceSelfAdjoint R) (hRR : ∀ X, R (R X)=R X)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    {eps : ℝ} (heps : 0≤eps) (heps1 : eps≤1)
    (hdist : ‖sourceMap P-sourceMap R‖≤eps) :
    (max 0 (Real.sqrt (1-eps^2)*
        Real.sqrt (sourceTrace Q-sourceTrace (Q.comp P))-
      eps*Real.sqrt (sourceTrace (Q.comp P))))^2≤
      sourceTrace Q-sourceTrace (Q.comp R) := by
  have h := complement_family_square_le (sourceMap P) (sourceMap R)
    (sourceMap_idempotent P hPP) (sourceMap_selfAdjoint R hR)
    (sourceMap_idempotent R hRR) heps heps1 hdist
    (fun i => sourceEuclideanVector (Q (sourceEigenoperator Q hQ i)))
  simp only [sourceMap_apply] at h
  rwa [source_projection_family_complement_mass P Q hP hPP hQ hQQ,
    source_projection_family_mass P Q hP hPP hQ hQQ,
    source_projection_family_complement_mass R Q hR hRR hQ hQQ] at h

/-- Sharp trace transport of a lower trial trace certificate. Equal ranks are
stated as actual source traces. The band trace, not the low-space rank, scales
the two square roots in this bound. The raw formula also covers zero band rank. -/
theorem source_trace_sharp_leakage
    (P R Q : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hPP : ∀ X, P (P X)=P X)
    (hR : SourceSelfAdjoint R) (hRR : ∀ X, R (R X)=R X)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    {eps tau : ℝ} (heps : 0≤eps) (heps1 : eps≤1)
    (hdist : ‖sourceMap P-sourceMap R‖≤eps)
    (hrank : sourceTrace P=sourceTrace R)
    (htrial : tau≤sourceTrace P-sourceTrace (P.comp Q)) :
    max 0 (sourceTrace R-sourceTrace Q+
      (max 0 (Real.sqrt (1-eps^2)*
          Real.sqrt (sourceTrace Q-sourceTrace R+tau)-
        eps*Real.sqrt (sourceTrace R-tau)))^2)≤
      sourceTrace R-sourceTrace (R.comp Q) := by
  have hm : sourceTrace (Q.comp P)≤sourceTrace R-tau := by
    rw [hrank,sourceTrace_comp_comm P Q] at htrial
    linarith
  have hsa : Real.sqrt (sourceTrace Q-sourceTrace R+tau)≤
      Real.sqrt (sourceTrace Q-sourceTrace (Q.comp P)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsb := Real.sqrt_le_sqrt hm
  have ha := mul_le_mul_of_nonneg_left hsa (Real.sqrt_nonneg (1-eps^2))
  have hb := mul_le_mul_of_nonneg_left hsb heps
  have hc : Real.sqrt (1-eps^2)*Real.sqrt (sourceTrace Q-sourceTrace R+tau)-
        eps*Real.sqrt (sourceTrace R-tau)≤
      Real.sqrt (1-eps^2)*Real.sqrt (sourceTrace Q-sourceTrace (Q.comp P))-
        eps*Real.sqrt (sourceTrace (Q.comp P)) := by linarith
  have hs := (sq_le_sq₀ (le_max_left _ _) (le_max_left _ _)).mpr
    (max_le_max (le_refl 0) hc)
  have hh := source_trace_complement_sharp_transport P R Q hP hPP hR hRR hQ hQQ
    heps heps1 hdist
  rw [sourceTrace_comp_comm Q R] at hh
  apply max_le
  · rw [← source_projection_family_complement_mass Q R hQ hQQ hR hRR]
    exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
  · linarith


/-- Exact linear coordinate equivalence; no matrix entry sup norm is used to
estimate geometry. The geometry remains in Euclidean Hilbert coordinates. -/
noncomputable def sourceEuclideanEquiv :
    Operator D ≃ₗ[ℂ] EuclideanSpace ℂ (Fin D×Fin D) where
  toFun := sourceEuclideanVector
  invFun x := sourceUnvector (WithLp.ofLp x)
  left_inv X := rfl
  right_inv x := by ext i; cases i; rfl
  map_add' X Y := by ext i; rfl
  map_smul' c X := by ext i; rfl

noncomputable def sourceOfMap
    (A : EuclideanSpace ℂ (Fin D×Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D)) :
    Operator D →ₗ[ℂ] Operator D :=
  sourceEuclideanEquiv.symm.toLinearMap.comp
    (A.toLinearMap.comp sourceEuclideanEquiv.toLinearMap)

/-- Source Of Map vector for the stated finite source data. -/
theorem sourceOfMap_vector
    (A : EuclideanSpace ℂ (Fin D×Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (X : Operator D) :
    sourceEuclideanVector (sourceOfMap A X)=A (sourceEuclideanVector X) := by
  change sourceEuclideanEquiv (sourceEuclideanEquiv.symm (A (sourceEuclideanEquiv X)))=_
  exact sourceEuclideanEquiv.apply_symm_apply _

/-- Source Map source Of Map for the stated finite source data. -/
theorem sourceMap_sourceOfMap
    (A : EuclideanSpace ℂ (Fin D×Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D)) :
    sourceMap (sourceOfMap A)=A := by
  ext x : 1
  obtain ⟨X,rfl⟩ := source_vector_surjective x
  rw [sourceMap_apply,sourceOfMap_vector]

/-- Source Of Map self Adjoint for the stated finite source data. -/
theorem sourceOfMap_selfAdjoint
    (A : EuclideanSpace ℂ (Fin D×Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (hA : IsSelfAdjoint A) :
    SourceSelfAdjoint (sourceOfMap A) := by
  intro X Y
  have h := hA.isSymmetric (sourceEuclideanVector X) (sourceEuclideanVector Y)
  change inner ℂ (A (sourceEuclideanVector X)) (sourceEuclideanVector Y)=
    inner ℂ (sourceEuclideanVector X) (A (sourceEuclideanVector Y)) at h
  simpa only [← sourceOfMap_vector,sourceEuclideanVector_inner] using h

/-- Source Of Map idempotent for the stated finite source data. -/
theorem sourceOfMap_idempotent
    (A : EuclideanSpace ℂ (Fin D×Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (hAA : ∀ x, A (A x)=A x) (X : Operator D) :
    sourceOfMap A (sourceOfMap A X)=sourceOfMap A X := by
  apply source_vector_injective
  simp only [sourceOfMap_vector,hAA]

/-- Source Trace source Of Map for the stated finite source data. -/
theorem sourceTrace_sourceOfMap
    (A : EuclideanSpace ℂ (Fin D×Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D)) :
    sourceTrace (sourceOfMap A)=
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin D×Fin D)) A.toLinearMap).re := by
  let L : Operator D →ₗ[ℂ] Operator D := LinearMap.id
  have hL : SourceSelfAdjoint L := by intro X Y; rfl
  rw [sourceTrace_eq_sum_eigenoperators L _ hL,
    LinearMap.trace_eq_sum_inner A.toLinearMap (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sourceEuclideanVector_inner,sourceOfMap_vector,sourceEuclideanVector_eigenoperator]
  rfl

/-- The trial projection's true source trace is its coordinate dimension,
including dimension zero. -/
theorem sourceTrace_trialProjection {q : ℕ}
    (U : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (hU : ∀ z, ‖U z‖=‖z‖) :
    sourceTrace (sourceOfMap (trialProjection U))=(q:ℝ) := by
  rw [sourceTrace_sourceOfMap]
  have hu : U.adjoint.comp U=ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q)) :=
    U.norm_map_iff_adjoint_comp_self.mp hU
  have hul : U.adjoint.toLinearMap.comp U.toLinearMap=LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap hu
  change (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin D×Fin D))
    (U.toLinearMap.comp U.adjoint.toLinearMap)).re=(q:ℝ)
  rw [LinearMap.trace_comp_comm',hul,LinearMap.trace_id]
  simp



/-- Source Of Map source Map for the stated finite source data. -/
theorem sourceOfMap_sourceMap (L : Operator D →ₗ[ℂ] Operator D) :
    sourceOfMap (sourceMap L)=L := by
  ext X : 1
  apply source_vector_injective
  rw [sourceOfMap_vector,sourceMap_apply]

/-- Source Map comp for the stated finite source data. -/
theorem sourceMap_comp (A B : Operator D →ₗ[ℂ] Operator D) :
    sourceMap (A.comp B)=(sourceMap A).comp (sourceMap B) := by
  ext x : 1
  obtain ⟨X,rfl⟩ := source_vector_surjective x
  simp only [ContinuousLinearMap.comp_apply,sourceMap_apply,LinearMap.comp_apply]

/-- Source Trace eq trace source Map for the stated finite source data. -/
theorem sourceTrace_eq_trace_sourceMap (L : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace L=
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin D×Fin D)) (sourceMap L).toLinearMap).re := by
  have h := sourceTrace_sourceOfMap (sourceMap L)
  rwa [sourceOfMap_sourceMap] at h

/-- The full-source overlap trace equals the small compressed band trace. -/
theorem sourceTrace_trialProjection_comp {q : ℕ}
    (U : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (Q : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace ((sourceOfMap (trialProjection U)).comp Q)=
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin q))
        (trialCompression (sourceMap Q) U).toLinearMap).re := by
  rw [sourceTrace_eq_trace_sourceMap,sourceMap_comp,sourceMap_sourceOfMap]
  change (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin D×Fin D))
    (U.toLinearMap.comp (U.adjoint.toLinearMap.comp (sourceMap Q).toLinearMap))).re=_
  rw [LinearMap.trace_comp_comm']
  rfl

/-- Coordinate trace certificates for I-U†QU are the actual trial leakage
trace used by the full-source theorem, with no added trace premise. -/
theorem source_trial_leakage_trace {q : ℕ}
    (U : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (Q : Operator D →ₗ[ℂ] Operator D) :
    (q:ℝ)-sourceTrace ((sourceOfMap (trialProjection U)).comp Q)=
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin q))
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q))-
          trialCompression (sourceMap Q) U).toLinearMap).re := by
  rw [sourceTrace_trialProjection_comp]
  change (q:ℝ)-_=
    (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin q))
      (LinearMap.id-(trialCompression (sourceMap Q) U).toLinearMap)).re
  rw [map_sub,Complex.sub_re,LinearMap.trace_id]
  simp

/-- A compression quadratic-form certificate is exactly the trial vector
leakage premise; the complex Hilbert norm is preserved throughout. -/
theorem trial_leakage_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] F) (Q : F →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ x, Q (Q x)=Q x) (z : E) :
    (inner ℂ z ((ContinuousLinearMap.id ℂ E-trialCompression Q U) z)).re=
      ‖U z-Q (U z)‖^2 := by
  change (inner ℂ z (z-U.adjoint (Q (U z)))).re=_
  have hnz : (inner ℂ z z).re=‖z‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  have hnq : (inner ℂ (Q (U z)) (Q (U z))).re=‖Q (U z)‖^2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (Q (U z))).symm
  rw [inner_sub_right,Complex.sub_re,hnz,U.adjoint_inner_right]
  have h := hQ.isSymmetric (U z) (Q (U z))
  change inner ℂ (Q (U z)) (Q (U z))=
    inner ℂ (U z) (Q (Q (U z))) at h
  rw [hQQ] at h
  rw [← h,hnq]
  have hp := projection_norm_sq_split Q hQ hQQ (U z)
  rw [hU] at hp
  linarith

/-- Sharp band-side trace transport for the actual full source low space.
The trial source projection and its rank are constructed from U; the true
projector, equal rank and distance are supplied by the actual spectral cut
and the residual theorem. There is no assumed angle or true-basis witness. -/
theorem source_low_trace_sharp_leakage_of_card
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0≤(hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X=0 → ∃ c : ℂ, X=c•G)
    {q : ℕ} {cutoff μ lam η eps tau : ℝ}
    (hcard : (sourcePositiveLowModes L hL cutoff).card=q)
    (U : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (hU : ∀ z, ‖U z‖=‖z‖)
    (hcut : cutoff<μ) (hgap : lam<μ)
    (hsep : ∀ i, 0<sourceEigenvalues L hL i →
      cutoff<sourceEigenvalues L hL i → μ≤sourceEigenvalues L hL i)
    (hcenter : ∀ z, inner ℂ (sourceEuclideanVector G) (U z)=0)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re≤lam*‖z‖^2)
    (hres : ‖trialResidual (sourceMap L) U‖≤η)
    (heps : 0≤eps) (heps1 : eps≤1) (hbudget : η/(μ-lam)≤eps)
    (Q : Operator D →ₗ[ℂ] Operator D) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X)
    (htrial : tau≤(q:ℝ)-sourceTrace ((sourceOfMap (trialProjection U)).comp Q)) :
    max 0 ((q:ℝ)-sourceTrace Q+
      (max 0 (Real.sqrt (1-eps^2)*Real.sqrt (sourceTrace Q-(q:ℝ)+tau)-
        eps*Real.sqrt ((q:ℝ)-tau)))^2)≤
      (q:ℝ)-sourceTrace ((sourcePositiveLowProjection L hL cutoff).comp Q) := by
  let P := sourceOfMap (trialProjection U)
  let R := sourcePositiveLowProjection L hL cutoff
  have hP : SourceSelfAdjoint P :=
    sourceOfMap_selfAdjoint _ (trialProjection_selfAdjoint U)
  have hPP : ∀ X, P (P X)=P X :=
    sourceOfMap_idempotent _ (trialProjection_idempotent U hU)
  have hR : SourceSelfAdjoint R := sourceSpectralCut_selfAdjoint L hL _
  have hRR : ∀ X, R (R X)=R X := sourceSpectralCut_idempotent L hL _
  have htraceP : sourceTrace P=(q:ℝ) := sourceTrace_trialProjection U hU
  have htraceR : sourceTrace R=(q:ℝ) := by
    change sourceTrace (sourceSpectralCut L hL (sourcePositiveLowModes L hL cutoff))=_
    rw [sourceTrace_spectralCut,hcard]
  have hd : ‖sourceMap P-sourceMap R‖≤eps := by
    rw [show sourceMap P=trialProjection U from sourceMap_sourceOfMap _]
    exact (source_low_trialProjection_sub_norm_le_of_card L hL hpos G hker
      hcard U hU hcut hgap hsep hcenter hcap hres).trans hbudget
  have ht : tau≤sourceTrace P-sourceTrace (P.comp Q) := by rw [htraceP]; exact htrial
  have h := source_trace_sharp_leakage P R Q hP hPP hR hRR hQ hQQ heps heps1 hd
    (htraceP.trans htraceR.symm) ht
  simpa only [htraceR] using h

/-- The physical band contributes its true two-leg rank |S|² to the trace
transport. This remains defined when the physical band is empty. -/
theorem source_low_energy_band_trace_sharp_leakage_of_card
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0≤(hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X=0 → ∃ c : ℂ, X=c•G)
    {q : ℕ} {cutoff μ lam η eps tau : ℝ}
    (hcard : (sourcePositiveLowModes L hL cutoff).card=q)
    (U : EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin D×Fin D))
    (hU : ∀ z, ‖U z‖=‖z‖)
    (hcut : cutoff<μ) (hgap : lam<μ)
    (hsep : ∀ i, 0<sourceEigenvalues L hL i →
      cutoff<sourceEigenvalues L hL i → μ≤sourceEigenvalues L hL i)
    (hcenter : ∀ z, inner ℂ (sourceEuclideanVector G) (U z)=0)
    (hcap : ∀ z, (inner ℂ z (trialCompression (sourceMap L) U z)).re≤lam*‖z‖^2)
    (hres : ‖trialResidual (sourceMap L) U‖≤η)
    (heps : 0≤eps) (heps1 : eps≤1) (hbudget : η/(μ-lam)≤eps)
    (H : Operator D) (hH : H.IsHermitian) (S : Finset (Fin D))
    (htrial : tau≤(q:ℝ)-sourceTrace ((sourceOfMap (trialProjection U)).comp
      (sourceCompression (hermEnergyBand H hH S)))) :
    max 0 ((q:ℝ)-(S.card:ℝ)^2+
      (max 0 (Real.sqrt (1-eps^2)*Real.sqrt ((S.card:ℝ)^2-(q:ℝ)+tau)-
        eps*Real.sqrt ((q:ℝ)-tau)))^2)≤
      (q:ℝ)-sourceTrace ((sourcePositiveLowProjection L hL cutoff).comp
        (sourceCompression (hermEnergyBand H hH S))) := by
  have h := source_low_trace_sharp_leakage_of_card L hL hpos G hker hcard U hU
    hcut hgap hsep hcenter hcap hres heps heps1 hbudget
    (sourceCompression (hermEnergyBand H hH S))
    (sourceCompression_selfAdjoint _ (hermEnergyBand_isHermitian H hH S))
    (sourceCompression_idempotent _ (hermEnergyBand_idempotent H hH S)) htrial
  simpa only [sourceTrace_energyBand] using h

end SharpProjectionLeakage
end Qatlib.Concepts.GibbsSource.SpectralGeom
