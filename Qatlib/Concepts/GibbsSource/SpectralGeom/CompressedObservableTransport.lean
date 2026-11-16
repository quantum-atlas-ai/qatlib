/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.RankSensitiveTraceTransport

@[expose] public section


/-! Sharp transport of Rayleigh quotients and compressed observable spectra. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- Compressed hs Inner self real for the stated finite source data. -/
private theorem compressed_hsInner_self_real (X : Operator D) :
    hsInner X X=((hsInner X X).re:ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hsInner_self_re X

/-- Compressed norm Sq smul for the stated finite source data. -/
private theorem compressed_normSq_smul (c : ℂ) (X : Operator D) :
    (hsInner (c • X) (c • X)).re=Complex.normSq c*(hsInner X X).re := by
  rw [hsInner_smul_left, hsInner_smul_right, ← mul_assoc,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ofReal_mul_re]

/-- The actual orthogonal projection onto a nonzero source line. -/
noncomputable def sourceLineProjection (X : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  ((((hsInner X X).re)⁻¹:ℝ):ℂ) • sourceRankOne X

/-- Source Line Projection apply for the stated finite source data. -/
theorem sourceLineProjection_apply (X Y : Operator D) :
    sourceLineProjection X Y=(hsInner X Y / ((hsInner X X).re:ℂ)) • X := by
  change (((((hsInner X X).re)⁻¹ : ℝ) : ℂ)) • (hsInner X Y • X) = _
  rw [smul_smul, Complex.ofReal_inv]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

/-- Source Line Projection self Adjoint for the stated finite source data. -/
theorem sourceLineProjection_selfAdjoint (X : Operator D) :
    SourceSelfAdjoint (sourceLineProjection X) := by
  intro Y Z
  simp only [sourceLineProjection, LinearMap.smul_apply, hsInner_smul_left,
    hsInner_smul_right, star_ofReal]
  rw [sourceRankOne_selfAdjoint X]

/-- Source Line Projection self for the stated finite source data. -/
theorem sourceLineProjection_self (X : Operator D) (hX : X≠0) :
    sourceLineProjection X X=X := by
  have hn : ((hsInner X X).re:ℂ)≠0 := by
    exact_mod_cast (hsInner_self_pos hX).ne'
  rw [sourceLineProjection_apply, compressed_hsInner_self_real, Complex.ofReal_re, div_self hn, one_smul]

/-- Source Line Projection idempotent for the stated finite source data. -/
theorem sourceLineProjection_idempotent (X : Operator D) (hX : X≠0)
    (Y : Operator D) :
    sourceLineProjection X (sourceLineProjection X Y)=sourceLineProjection X Y := by
  conv_lhs => arg 2; rw [sourceLineProjection_apply]
  rw [map_smul, sourceLineProjection_self X hX, sourceLineProjection_apply]

/-- Source Line Projection finrank for the stated finite source data. -/
theorem sourceLineProjection_finrank (X : Operator D) (hX : X≠0) :
    Module.finrank ℂ (LinearMap.range (sourceLineProjection X))=1 := by
  have ht := sourceTrace_eq_finrank_range (sourceLineProjection X)
    (sourceLineProjection_idempotent X hX)
  rw [sourceLineProjection, sourceTrace_real_smul, sourceTrace_rankOne,
    inv_mul_cancel₀ (hsInner_self_pos hX).ne'] at ht
  exact_mod_cast ht.symm

/-- A line projection evaluates an observable at its normalized source vector. -/
theorem sourceTrace_comp_lineProjection
    (A : Operator D →ₗ[ℂ] Operator D) (X : Operator D) :
    sourceTrace (A.comp (sourceLineProjection X))=
      (hsInner X (A X)).re/(hsInner X X).re := by
  rw [sourceLineProjection, LinearMap.comp_smul, sourceTrace_real_smul,
    sourceTrace_comp_rankOne]
  ring

/-- A strict directed angle makes the projected vector nonzero. -/
theorem source_projection_ne_zero_of_angle
    (R : Operator D →ₗ[ℂ] Operator D) (X : Operator D) (hX : X≠0)
    {ε : ℝ} (hε : 0≤ε) (hε1 : ε<1)
    (hangle : (hsInner (X-R X) (X-R X)).re≤ε^2*(hsInner X X).re) :
    R X≠0 := by
  intro hzero
  rw [hzero, sub_zero] at hangle
  have hn := hsInner_self_pos hX
  have hs : ε^2<1 := by nlinarith
  nlinarith

/-- Orthogonal projection transports every normalized Rayleigh quotient with
the sharp interval-width times sine-angle constant. -/
theorem source_projection_rayleigh_transport
    (R A : Operator D →ₗ[ℂ] Operator D)
    (hR : SourceSelfAdjoint R) (hRR : ∀ X, R (R X)=R X)
    (X : Operator D) (hX : X≠0)
    {ε a b : ℝ} (hε : 0≤ε) (hε1 : ε<1) (hab : a≤b)
    (hangle : (hsInner (X-R X) (X-R X)).re≤ε^2*(hsInner X X).re)
    (hlower : ∀ Y, a*(hsInner Y Y).re≤(hsInner Y (A Y)).re)
    (hupper : ∀ Y, (hsInner Y (A Y)).re≤b*(hsInner Y Y).re) :
    |(hsInner X (A X)).re/(hsInner X X).re-
      (hsInner (R X) (A (R X))).re/(hsInner (R X) (R X)).re|≤(b-a)*ε := by
  have hRX := source_projection_ne_zero_of_angle R X hX hε hε1 hangle
  have hline : sourceLineProjection (R X) X=R X := by
    have hn : ((hsInner (R X) (R X)).re:ℂ)≠0 := by
      exact_mod_cast (hsInner_self_pos hRX).ne'
    rw [sourceLineProjection_apply, ← source_projection_pair R hR hRR,
      compressed_hsInner_self_real, Complex.ofReal_re, div_self hn, one_smul]
  have hforward (Y : Operator D) :
      (hsInner (sourceLineProjection X Y-
        sourceLineProjection (R X) (sourceLineProjection X Y))
        (sourceLineProjection X Y-
        sourceLineProjection (R X) (sourceLineProjection X Y))).re≤
      ε^2*(hsInner (sourceLineProjection X Y) (sourceLineProjection X Y)).re := by
    rw [sourceLineProjection_apply X Y, map_smul, hline, ← smul_sub,
      compressed_normSq_smul, compressed_normSq_smul]
    nlinarith only [mul_le_mul_of_nonneg_left hangle
      (Complex.normSq_nonneg (hsInner X Y / ((hsInner X X).re:ℂ)))]
  have hdim : Module.finrank ℂ (LinearMap.range (sourceLineProjection X))=
      Module.finrank ℂ (LinearMap.range (sourceLineProjection (R X))) := by
    rw [sourceLineProjection_finrank X hX, sourceLineProjection_finrank (R X) hRX]
  have hclose := source_equalRank_projection_difference
    (sourceLineProjection X) (sourceLineProjection (R X))
    (sourceLineProjection_selfAdjoint X) (sourceLineProjection_selfAdjoint (R X))
    (sourceLineProjection_idempotent X hX) (sourceLineProjection_idempotent (R X) hRX)
    hdim (sq_nonneg ε) (by nlinarith : ε^2<1) hforward
  have ht := source_equalRank_observable_trace_bound
    (sourceLineProjection X) (sourceLineProjection (R X)) A
    (sourceLineProjection_selfAdjoint X) (sourceLineProjection_selfAdjoint (R X))
    (sourceLineProjection_idempotent X hX) (sourceLineProjection_idempotent (R X) hRX)
    hdim hε hab hclose hlower hupper
  simpa only [sourceTrace_comp_lineProjection, sourceLineProjection_finrank X hX,
    Nat.cast_one, mul_one] using ht


/-- The observable compressed to the actual range, with an explicitly separated
scalar on the orthogonal complement. -/
noncomputable def sourceLiftedCompression
    (P A : Operator D →ₗ[ℂ] Operator D) (κ : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  P.comp (A.comp P)+(κ:ℂ) • (LinearMap.id-P)

/-- Source Lifted Compression apply for the stated finite source data. -/
theorem sourceLiftedCompression_apply
    (P A : Operator D →ₗ[ℂ] Operator D) (κ : ℝ) (X : Operator D) :
    sourceLiftedCompression P A κ X=P (A (P X))+(κ:ℂ) • (X-P X) := rfl

/-- Source Lifted Compression self Adjoint for the stated finite source data. -/
theorem sourceLiftedCompression_selfAdjoint
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A) (κ : ℝ) :
    SourceSelfAdjoint (sourceLiftedCompression P A κ) := by
  intro X Y
  simp only [sourceLiftedCompression_apply, hsInner, Matrix.conjTranspose_add,
    Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
  change hsInner (P (A (P X))) Y+hsInner ((κ:ℂ) • (X-P X)) Y=
    hsInner X (P (A (P Y)))+hsInner X ((κ:ℂ) • (Y-P Y))
  rw [hP, hA, hP, hsInner_smul_left, hsInner_smul_right, star_ofReal,
    hsInner_sub_left, hsInner_sub_right, hP]

/-- Source Lifted Compression energy on range for the stated finite source data. -/
theorem sourceLiftedCompression_energy_on_range
    (P A : Operator D →ₗ[ℂ] Operator D) (hP : SourceSelfAdjoint P)
    (κ : ℝ) (X : Operator D) (hPX : P X=X) :
    (hsInner X (sourceLiftedCompression P A κ X)).re=(hsInner X (A X)).re := by
  rw [sourceLiftedCompression_apply, hPX, sub_self, smul_zero, add_zero, ← hP, hPX]

/-- Every eigenvector below the complementary scalar lies in the actual range.
This keeps zero and repeated eigenvalues of the compression. -/
theorem sourceLiftedCompression_eigenvector_fixed
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hPP : ∀ X, P (P X)=P X)
    (κ lam : ℝ) (X : Operator D)
    (heigen : sourceLiftedCompression P A κ X=(lam:ℂ) • X)
    (hne : lam≠κ) : P X=X := by
  have hp := congrArg P heigen
  rw [sourceLiftedCompression_apply, map_add, map_smul, map_sub,
    hPP, hPP, sub_self, smul_zero, add_zero, map_smul] at hp
  rw [sourceLiftedCompression_apply, hp] at heigen
  have hz : (((κ-lam:ℝ):ℂ)) • (X-P X)=0 := by
    rw [Complex.ofReal_sub, sub_smul]
    have h : (κ:ℂ) • (X-P X)=(lam:ℂ) • (X-P X) := by
      simpa only [smul_sub] using eq_sub_of_add_eq' heigen
    exact sub_eq_zero.mpr h
  have hn : (((κ-lam:ℝ):ℂ))≠0 := by
    exact_mod_cast sub_ne_zero.mpr hne.symm
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hn)).symm

/-- All actual eigenmodes at or below a threshold, including zero modes. -/
noncomputable def sourceAtMostModes
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (t : ℝ) :
    Finset (Fin D × Fin D) :=
  Finset.univ.filter (fun i => sourceEigenvalues L hL i≤t)

/-- Source At Most Modes energy upper for the stated finite source data. -/
theorem sourceAtMostModes_energy_upper
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (t : ℝ)
    (X : Operator D)
    (hfix : sourceSpectralCut L hL (sourceAtMostModes L hL t) X=X) :
    (hsInner X (L X)).re≤t*(hsInner X X).re := by
  classical
  rw [source_energy_eq_sum_eigenvalues L hL,
    source_hsNormSq_eq_sum_coefficients L hL, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : sourceEigenvalues L hL i≤t
  · exact mul_le_mul_of_nonneg_right hi (Complex.normSq_nonneg _)
  · have hm : i∉sourceAtMostModes L hL t := by
      simpa only [sourceAtMostModes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hc := congrArg (fun Y => hsInner (sourceEigenoperator L hL i) Y) hfix
    change hsInner (sourceEigenoperator L hL i)
      (sourceSpectralCut L hL (sourceAtMostModes L hL t) X)=
      hsInner (sourceEigenoperator L hL i) X at hc
    rw [sourceSpectralCut_coefficient, ite_eq_right hm] at hc
    rw [← hc, Complex.normSq_zero, mul_zero, mul_zero]

/-- A nonzero vector outside the closed low cut has strictly larger Rayleigh
quotient, including at a degenerate threshold. -/
theorem sourceAtMostModes_kernel_energy_gt
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (t : ℝ)
    (X : Operator D) (hX : X≠0)
    (hzero : sourceSpectralCut L hL (sourceAtMostModes L hL t) X=0) :
    t*(hsInner X X).re<(hsInner X (L X)).re := by
  classical
  have hc (i : Fin D × Fin D) (hi : sourceEigenvalues L hL i≤t) :
      hsInner (sourceEigenoperator L hL i) X=0 := by
    have hm : i∈sourceAtMostModes L hL t := by
      simpa only [sourceAtMostModes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have h := congrArg (fun Y => hsInner (sourceEigenoperator L hL i) Y) hzero
    change hsInner (sourceEigenoperator L hL i)
      (sourceSpectralCut L hL (sourceAtMostModes L hL t) X)=
      hsInner (sourceEigenoperator L hL i) 0 at h
    rw [sourceSpectralCut_coefficient, ite_eq_left hm] at h
    simpa only [hsInner, mul_zero, Matrix.trace_zero] using h
  have hn := hsInner_self_pos hX
  rw [source_hsNormSq_eq_sum_coefficients L hL] at hn
  obtain ⟨i, hi, hp⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (hsInner (sourceEigenoperator L hL j) X))).mp hn
  have hit : t<sourceEigenvalues L hL i := by
    by_contra h
    rw [hc i (le_of_not_gt h), Complex.normSq_zero] at hp
    exact (lt_irrefl 0) hp
  rw [source_energy_eq_sum_eigenvalues L hL,
    source_hsNormSq_eq_sum_coefficients L hL, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : sourceEigenvalues L hL j≤t
    · rw [hc j hj, Complex.normSq_zero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (le_of_not_ge hj) (Complex.normSq_nonneg _)
  · exact ⟨i, hi, mul_lt_mul_of_pos_right hit hp⟩

/-- Source Lifted Compression low Cut fixed for the stated finite source data. -/
theorem sourceLiftedCompression_lowCut_fixed
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X) (κ t : ℝ) (ht : t<κ) (X : Operator D) :
    P (sourceSpectralCut (sourceLiftedCompression P A κ)
      (sourceLiftedCompression_selfAdjoint P A hP hA κ)
      (sourceAtMostModes (sourceLiftedCompression P A κ)
        (sourceLiftedCompression_selfAdjoint P A hP hA κ) t) X)=
    sourceSpectralCut (sourceLiftedCompression P A κ)
      (sourceLiftedCompression_selfAdjoint P A hP hA κ)
      (sourceAtMostModes (sourceLiftedCompression P A κ)
        (sourceLiftedCompression_selfAdjoint P A hP hA κ) t) X := by
  classical
  let L := sourceLiftedCompression P A κ
  let hL := sourceLiftedCompression_selfAdjoint P A hP hA κ
  change P (∑ i ∈ sourceAtMostModes L hL t,
      hsInner (sourceEigenoperator L hL i) X • sourceEigenoperator L hL i)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  congr 1
  apply sourceLiftedCompression_eigenvector_fixed P A hPP κ
    (sourceEigenvalues L hL i) _ (sourceEigenoperator_apply L hL i)
  have h := (Finset.mem_filter.mp hi).2
  exact ne_of_lt (h.trans_lt ht)


/-- The multiplicity-preserving low count of the actual lifted compression.
For thresholds below κ its eigenvectors are all in the projection range. -/
noncomputable def sourceCompressedCount
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A) (κ t : ℝ) : ℕ :=
  (sourceAtMostModes (sourceLiftedCompression P A κ)
    (sourceLiftedCompression_selfAdjoint P A hP hA κ) t).card

/-- Projecting an entire low Rayleigh subspace gives sharp spectral-count
transport between the two actual compressed observables. -/
theorem source_compressedObservable_count_transport
    (P R A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    {ε a b κ t : ℝ} (hε : 0≤ε) (hε1 : ε<1) (hab : a≤b)
    (ht : t+(b-a)*ε<κ)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤ε^2*(hsInner X X).re)
    (hlower : ∀ X, a*(hsInner X X).re≤(hsInner X (A X)).re)
    (hupper : ∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re) :
    sourceCompressedCount P A hP hA κ t≤
      sourceCompressedCount R A hR hA κ (t+(b-a)*ε) := by
  let LP := sourceLiftedCompression P A κ
  let LR := sourceLiftedCompression R A κ
  let hLP := sourceLiftedCompression_selfAdjoint P A hP hA κ
  let hLR := sourceLiftedCompression_selfAdjoint R A hR hA κ
  let SP := sourceAtMostModes LP hLP t
  let SR := sourceAtMostModes LR hLR (t+(b-a)*ε)
  let QP := sourceSpectralCut LP hLP SP
  let QR := sourceSpectralCut LR hLR SR
  have htκ : t<κ := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr hab) hε
    linarith only [ht, hnonneg]
  have hdim : Module.finrank ℂ (LinearMap.range QP)≤
      Module.finrank ℂ (LinearMap.range (QR.comp R)) := by
    apply source_projection_range_finrank_le _ QP (sourceSpectralCut_idempotent LP hLP SP)
    intro X hfix hzero
    by_contra hX
    have hPX : P X=X := by
      rw [← hfix]
      exact sourceLiftedCompression_lowCut_fixed P A hP hA hPP κ t htκ X
    have hangle := hclose X
    rw [hPX] at hangle
    have hRX := source_projection_ne_zero_of_angle R X hX hε hε1 hangle
    have htransport := source_projection_rayleigh_transport R A hR hRR X hX
      hε hε1 hab hangle hlower hupper
    have hup := sourceAtMostModes_energy_upper LP hLP t X hfix
    rw [sourceLiftedCompression_energy_on_range P A hP κ X hPX] at hup
    have hqX : (hsInner X (A X)).re/(hsInner X X).re≤t :=
      (div_le_iff₀ (hsInner_self_pos hX)).mpr hup
    have hqRX : (hsInner (R X) (A (R X))).re/(hsInner (R X) (R X)).re≤
        t+(b-a)*ε := by
      have hlo := (abs_le.mp htransport).1
      linarith only [hqX, hlo]
    have hupRX := (div_le_iff₀ (hsInner_self_pos hRX)).mp hqRX
    have hgt := sourceAtMostModes_kernel_energy_gt LR hLR (t+(b-a)*ε)
      (R X) hRX hzero
    rw [sourceLiftedCompression_energy_on_range R A hR κ (R X) (hRR X)] at hgt
    exact (not_lt_of_ge hupRX) hgt
  have hrange : Module.finrank ℂ (LinearMap.range (QR.comp R))≤
      Module.finrank ℂ (LinearMap.range QR) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range R QR)
  have h := hdim.trans hrange
  simpa only [sourceCompressedCount, QP, QR, sourceSpectralCut_finrank_range] using! h

/-- The low spectrum below an observable cap has precisely the actual
projection rank when the complementary scalar is separated above that cap. -/
theorem sourceCompressedCount_eq_rank_of_range_cap
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X)
    {κ b : ℝ} (hbκ : b<κ)
    (hupper : ∀ X, P X=X → (hsInner X (A X)).re≤b*(hsInner X X).re) :
    sourceCompressedCount P A hP hA κ b=Module.finrank ℂ (LinearMap.range P) := by
  let L := sourceLiftedCompression P A κ
  let hL := sourceLiftedCompression_selfAdjoint P A hP hA κ
  let S := sourceAtMostModes L hL b
  let Q := sourceSpectralCut L hL S
  have hle : Module.finrank ℂ (LinearMap.range Q)≤Module.finrank ℂ (LinearMap.range P) := by
    apply source_projection_range_finrank_le P Q (sourceSpectralCut_idempotent L hL S)
    intro X hfix hzero
    have hPX : P X=X := by
      rw [← hfix]
      exact sourceLiftedCompression_lowCut_fixed P A hP hA hPP κ b hbκ X
    exact hPX.symm.trans hzero
  have hge : Module.finrank ℂ (LinearMap.range P)≤Module.finrank ℂ (LinearMap.range Q) := by
    apply source_projection_range_finrank_le Q P hPP
    intro X hPX hzero
    by_contra hX
    have hgt := sourceAtMostModes_kernel_energy_gt L hL b X hX hzero
    rw [sourceLiftedCompression_energy_on_range P A hP κ X hPX] at hgt
    exact (not_lt_of_ge (hupper X hPX)) hgt
  have h := le_antisymm hle hge
  simpa only [sourceCompressedCount, Q, sourceSpectralCut_finrank_range] using! h


/-- Source Compressed Count eq rank for the stated finite source data. -/
theorem sourceCompressedCount_eq_rank
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X)
    {κ b : ℝ} (hbκ : b<κ)
    (hupper : ∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re) :
    sourceCompressedCount P A hP hA κ b=Module.finrank ℂ (LinearMap.range P) :=
  sourceCompressedCount_eq_rank_of_range_cap P A hP hA hPP hbκ (fun X _ => hupper X)


/-- The complete actual source spectrum in nondecreasing order, with multiplicity. -/
noncomputable def sourceOrderedEigenvalue
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (k : Fin (Fintype.card (Fin D × Fin D))) : ℝ :=
  (sourceSuperMatrix_isHermitian L hL).eigenvalues₀ k.rev

/-- Source Ordered Eigenvalue monotone for the stated finite source data. -/
theorem sourceOrderedEigenvalue_monotone
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) :
    Monotone (sourceOrderedEigenvalue L hL) := by
  intro i j hij
  exact (sourceSuperMatrix_isHermitian L hL).eigenvalues₀_antitone (Fin.rev_le_rev.mpr hij)

/-- Closed spectral counts characterize every ordered eigenvalue, retaining
the full multiplicity at equality. -/
theorem sourceOrderedEigenvalue_le_iff
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (k : Fin (Fintype.card (Fin D × Fin D))) (t : ℝ) :
    sourceOrderedEigenvalue L hL k≤t ↔ k.val<(sourceAtMostModes L hL t).card := by
  classical
  let e : Fin (Fintype.card (Fin D × Fin D)) ≃ (Fin D × Fin D) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have he (i : Fin (Fintype.card (Fin D × Fin D))) :
      sourceEigenvalues L hL (e i.rev)=sourceOrderedEigenvalue L hL i := by
    simp [sourceEigenvalues, Matrix.IsHermitian.eigenvalues, sourceOrderedEigenvalue, e]
  have hc : (Finset.univ.filter (fun i => sourceOrderedEigenvalue L hL i≤t)).card=
      (sourceAtMostModes L hL t).card := by
    apply Finset.card_bij (fun i _ => e i.rev)
    · intro i hi
      simpa only [sourceAtMostModes, Finset.mem_filter, Finset.mem_univ, true_and, he] using hi
    · intro i _ j _ hij
      exact Fin.rev_injective (e.injective hij)
    · intro j hj
      refine ⟨(e.symm j).rev, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have h := (Finset.mem_filter.mp hj).2
        rw [← he]
        simpa using h
      · simp
  rw [← hc]
  have hm := sourceOrderedEigenvalue_monotone L hL
  constructor
  · intro h
    have hs : Finset.Iic k⊆Finset.univ.filter (fun i => sourceOrderedEigenvalue L hL i≤t) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hm (Finset.mem_Iic.mp hi)).trans h⟩
    have hcard := Finset.card_le_card hs
    rw [Fin.card_Iic] at hcard
    omega
  · intro h
    by_contra hn
    have hs : Finset.univ.filter (fun i => sourceOrderedEigenvalue L hL i≤t)⊆Finset.Iio k := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hik
      have hki := hm (le_of_not_gt hik)
      have hit := (Finset.mem_filter.mp hi).2
      exact hn (hki.trans hit)
    have hcard := Finset.card_le_card hs
    rw [Fin.card_Iio] at hcard
    omega

/-- Below the complementary scalar, the first rank(P) ordered values are
exactly the spectrum of the actual compression. -/
theorem sourceLiftedCompression_ordered_le_cap
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X)
    {κ b : ℝ} (hbκ : b<κ)
    (hupper : ∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re)
    (k : Fin (Fintype.card (Fin D × Fin D)))
    (hk : k.val<Module.finrank ℂ (LinearMap.range P)) :
    sourceOrderedEigenvalue (sourceLiftedCompression P A κ)
      (sourceLiftedCompression_selfAdjoint P A hP hA κ) k≤b := by
  apply (sourceOrderedEigenvalue_le_iff _ _ k b).mpr
  change k.val<sourceCompressedCount P A hP hA κ b
  rw [sourceCompressedCount_eq_rank P A hP hA hPP hbκ hupper]
  exact hk

/-- Compressed norm Sq sub comm for the stated finite source data. -/
private theorem compressed_normSq_sub_comm (X Y : Operator D) :
    (hsInner (X-Y) (X-Y)).re=(hsInner (Y-X) (Y-X)).re := by
  rw [show X-Y=-(Y-X) by abel]
  change ((-(Y-X))ᴴ * -(Y-X)).trace.re=((Y-X)ᴴ * (Y-X)).trace.re
  rw [Matrix.conjTranspose_neg, neg_mul_neg]

/-- Every ordered eigenvalue of the two genuine rank-r compressions moves
by at most the observable width times the projection distance. -/
theorem source_compressedObservable_ordered_transport
    (P R A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=Module.finrank ℂ (LinearMap.range R))
    {ε a b κ : ℝ} (hε : 0≤ε) (hε1 : ε<1) (hab : a≤b)
    (hκ : b+(b-a)*ε<κ)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤ε^2*(hsInner X X).re)
    (hlower : ∀ X, a*(hsInner X X).re≤(hsInner X (A X)).re)
    (hupper : ∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re)
    (k : Fin (Fintype.card (Fin D × Fin D)))
    (hk : k.val<Module.finrank ℂ (LinearMap.range P)) :
    |sourceOrderedEigenvalue (sourceLiftedCompression P A κ)
        (sourceLiftedCompression_selfAdjoint P A hP hA κ) k-
      sourceOrderedEigenvalue (sourceLiftedCompression R A κ)
        (sourceLiftedCompression_selfAdjoint R A hR hA κ) k|≤(b-a)*ε := by
  let LP := sourceLiftedCompression P A κ
  let LR := sourceLiftedCompression R A κ
  let hLP := sourceLiftedCompression_selfAdjoint P A hP hA κ
  let hLR := sourceLiftedCompression_selfAdjoint R A hR hA κ
  let p := sourceOrderedEigenvalue LP hLP k
  let q := sourceOrderedEigenvalue LR hLR k
  have hbκ : b<κ := by
    have hn := mul_nonneg (sub_nonneg.mpr hab) hε
    linarith only [hκ, hn]
  have hp : p≤b := sourceLiftedCompression_ordered_le_cap P A hP hA hPP hbκ hupper k hk
  have hq : q≤b := sourceLiftedCompression_ordered_le_cap R A hR hA hRR hbκ hupper k
    (by simpa only [← hdim] using hk)
  have hpcount : k.val<sourceCompressedCount P A hP hA κ p :=
    (sourceOrderedEigenvalue_le_iff LP hLP k p).mp le_rfl
  have hqcount : k.val<sourceCompressedCount R A hR hA κ q :=
    (sourceOrderedEigenvalue_le_iff LR hLR k q).mp le_rfl
  have hforward := source_compressedObservable_count_transport P R A hP hR hA hPP hRR
    hε hε1 hab (by linarith only [hp, hκ] : p+(b-a)*ε<κ) hclose hlower hupper
  have hbackward := source_compressedObservable_count_transport R P A hR hP hA hRR hPP
    hε hε1 hab (by linarith only [hq, hκ] : q+(b-a)*ε<κ)
    (fun X => by rw [compressed_normSq_sub_comm]; exact hclose X) hlower hupper
  have hqp : q≤p+(b-a)*ε :=
    (sourceOrderedEigenvalue_le_iff LR hLR k _).mpr (hpcount.trans_le hforward)
  have hpq : p≤q+(b-a)*ε :=
    (sourceOrderedEigenvalue_le_iff LP hLP k _).mpr (hqcount.trans_le hbackward)
  change |p-q|≤(b-a)*ε
  rw [abs_le]
  constructor <;> linarith only [hqp, hpq]


/-- The sum of the k smallest actual eigenvalues, counting all multiplicities. -/
noncomputable def sourceLowerEigenvalueSum
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (k : ℕ) : ℝ :=
  ∑ i : Fin (Fintype.card (Fin D × Fin D)) with i.val<k,
    sourceOrderedEigenvalue L hL i

/-- Compressed prefix card for the stated finite source data. -/
private theorem compressed_prefix_card (N k : ℕ) (hk : k≤N) :
    (Finset.univ.filter (fun i : Fin N => i.val<k)).card=k := by
  classical
  have h : (Finset.univ.filter (fun i : Fin N => i.val<k)).card=
      (Finset.univ : Finset (Fin k)).card := by
    apply Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k))
    · intro i hi
      exact Finset.mem_univ _
    · intro i _ j _ hij
      exact Fin.ext (congrArg (fun x : Fin k => x.val) hij)
    · intro j _
      refine ⟨⟨j.val, j.isLt.trans_le hk⟩, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
      · rfl
  simpa using h

/-- Every lower partial sum has its own sharp k times width times angle budget. -/
theorem source_compressedObservable_lowerSum_transport
    (P R A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=Module.finrank ℂ (LinearMap.range R))
    {ε a b κ : ℝ} (hε : 0≤ε) (hε1 : ε<1) (hab : a≤b)
    (hκ : b+(b-a)*ε<κ)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤ε^2*(hsInner X X).re)
    (hlower : ∀ X, a*(hsInner X X).re≤(hsInner X (A X)).re)
    (hupper : ∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re)
    (k : ℕ) (hk : k≤Module.finrank ℂ (LinearMap.range P)) :
    |sourceLowerEigenvalueSum (sourceLiftedCompression P A κ)
        (sourceLiftedCompression_selfAdjoint P A hP hA κ) k-
      sourceLowerEigenvalueSum (sourceLiftedCompression R A κ)
        (sourceLiftedCompression_selfAdjoint R A hR hA κ) k|≤(k:ℝ)*(b-a)*ε := by
  have hdimP : Module.finrank ℂ (LinearMap.range P)≤Fintype.card (Fin D × Fin D) := by
    simpa [Operator, Module.finrank_matrix] using LinearMap.finrank_range_le P
  rw [sourceLowerEigenvalueSum, sourceLowerEigenvalueSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin (Fintype.card (Fin D × Fin D)) with i.val<k,
        |sourceOrderedEigenvalue (sourceLiftedCompression P A κ)
            (sourceLiftedCompression_selfAdjoint P A hP hA κ) i-
          sourceOrderedEigenvalue (sourceLiftedCompression R A κ)
            (sourceLiftedCompression_selfAdjoint R A hR hA κ) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Fintype.card (Fin D × Fin D)) with _i.val<k, (b-a)*ε := by
      apply Finset.sum_le_sum
      intro i hi
      exact source_compressedObservable_ordered_transport P R A hP hR hA hPP hRR hdim
        hε hε1 hab hκ hclose hlower hupper i ((Finset.mem_filter.mp hi).2.trans_le hk)
    _ = (k:ℝ)*(b-a)*ε := by
      rw [Finset.sum_const, nsmul_eq_mul, compressed_prefix_card _ k (hk.trans hdimP)]
      ring

/-- A fully quantified consumer of the actual compressed spectra. The three
components retain closed counts, every ordered value, and all lower sums. -/
def SourceCompressedObservableTransport
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R) (r : ℕ) (ε : ℝ) : Prop :=
  ∀ (A : Operator D →ₗ[ℂ] Operator D) (hA : SourceSelfAdjoint A)
    (a b κ : ℝ), a≤b → b+(b-a)*ε<κ →
    (∀ X, a*(hsInner X X).re≤(hsInner X (A X)).re) →
    (∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re) →
    (∀ t, t≤b →
      sourceCompressedCount P A hP hA κ t≤
        sourceCompressedCount R A hR hA κ (t+(b-a)*ε) ∧
      sourceCompressedCount R A hR hA κ t≤
        sourceCompressedCount P A hP hA κ (t+(b-a)*ε)) ∧
    (∀ k : Fin (Fintype.card (Fin D × Fin D)), k.val<r →
      |sourceOrderedEigenvalue (sourceLiftedCompression P A κ)
          (sourceLiftedCompression_selfAdjoint P A hP hA κ) k-
        sourceOrderedEigenvalue (sourceLiftedCompression R A κ)
          (sourceLiftedCompression_selfAdjoint R A hR hA κ) k|≤(b-a)*ε) ∧
    ∀ k : ℕ, k≤r →
      |sourceLowerEigenvalueSum (sourceLiftedCompression P A κ)
          (sourceLiftedCompression_selfAdjoint P A hP hA κ) k-
        sourceLowerEigenvalueSum (sourceLiftedCompression R A κ)
          (sourceLiftedCompression_selfAdjoint R A hR hA κ) k|≤(k:ℝ)*(b-a)*ε

/-- Source compressed Observable transport for the stated finite source data. -/
theorem source_compressedObservable_transport
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    {r : ℕ} (hPrank : Module.finrank ℂ (LinearMap.range P)=r)
    (hRrank : Module.finrank ℂ (LinearMap.range R)=r)
    {ε : ℝ} (hε : 0≤ε) (hε1 : ε<1)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤ε^2*(hsInner X X).re) :
    SourceCompressedObservableTransport P R hP hR r ε := by
  intro A hA a b κ hab hκ hlower hupper
  have hdim := hPrank.trans hRrank.symm
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have htκ : t+(b-a)*ε<κ := by linarith only [ht, hκ]
    constructor
    · exact source_compressedObservable_count_transport P R A hP hR hA hPP hRR
        hε hε1 hab htκ hclose hlower hupper
    · exact source_compressedObservable_count_transport R P A hR hP hA hRR hPP
        hε hε1 hab htκ
        (fun X => by rw [compressed_normSq_sub_comm]; exact hclose X) hlower hupper
  · intro k hk
    exact source_compressedObservable_ordered_transport P R A hP hR hA hPP hRR hdim
      hε hε1 hab hκ hclose hlower hupper k (by simpa only [hPrank] using hk)
  · intro k hk
    exact source_compressedObservable_lowerSum_transport P R A hP hR hA hPP hRR hdim
      hε hε1 hab hκ hclose hlower hupper k (by simpa only [hPrank] using hk)

/-- Centered residuals in arbitrary injective complex coordinates certify
the actual ordered compression, using the genuine source norm and Gram form. -/
theorem source_centeredResidual_compressedObservable_certificate
    (L P : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hP : SourceSelfAdjoint P) (hPP : ∀ X, P (P X)=P X)
    (G : Operator D) (hPG : P G=0)
    (hker : ∀ Z, L Z=0 → ∃ a : ℂ, Z=a • G)
    {r : ℕ} (F : (Fin r → ℂ) →ₗ[ℂ] Operator D) (hF : Function.Injective F)
    (hspan : LinearMap.range F=LinearMap.range P)
    (S : Finset (Fin D × Fin D)) (hcount : S.card=r)
    {c ρ d : ℝ} (hρ : 0≤ρ) (hd : 0<d) (hsmall : ρ<d)
    (hsep : ∀ i, i∉S → sourceEigenvalues L hL i≠0 →
      d^2≤(sourceEigenvalues L hL i-c)^2)
    (hres : ∀ v, (hsInner (L (F v)-(c:ℂ) • F v)
      (L (F v)-(c:ℂ) • F v)).re≤ρ^2*(hsInner (F v) (F v)).re) :
    SourceCompressedObservableTransport P (sourceSpectralCut L hL S)
      hP (sourceSpectralCut_selfAdjoint L hL S) r (ρ/d) := by
  have hPrank : Module.finrank ℂ (LinearMap.range P)=r := by
    rw [← hspan, LinearMap.finrank_range_of_inj hF]
    simp
  have hRrank : Module.finrank ℂ (LinearMap.range (sourceSpectralCut L hL S))=r := by
    rw [sourceSpectralCut_finrank_range, hcount]
  exact source_compressedObservable_transport P (sourceSpectralCut L hL S) hP
    (sourceSpectralCut_selfAdjoint L hL S) hPP (sourceSpectralCut_idempotent L hL S)
    hPrank hRrank (div_nonneg hρ hd.le) ((div_lt_one hd).mpr hsmall)
    (source_centeredResidual_projection_certificate
      L P hL hP hPP G hPG hker F hF hspan S hcount hρ hd hsmall hsep hres)


/-- A form floor controls each actual ordered source eigenvalue. -/
theorem sourceOrderedEigenvalue_ge_of_form_bound
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (a : ℝ) (hfloor : ∀ X, a*(hsInner X X).re≤(hsInner X (L X)).re)
    (k : Fin (Fintype.card (Fin D × Fin D))) :
    a≤sourceOrderedEigenvalue L hL k := by
  let e : Fin (Fintype.card (Fin D × Fin D)) ≃ (Fin D × Fin D) :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := hfloor (sourceEigenoperator L hL (e k.rev))
  rw [sourceEigenoperator_apply, hsInner_smul_right, ofReal_mul_re,
    sourceEigenoperator_normSq, mul_one, mul_one] at h
  simpa [sourceEigenvalues, Matrix.IsHermitian.eigenvalues, sourceOrderedEigenvalue, e] using h

/-- The lifted quadratic form splits into the genuine compressed form and
the orthogonal-complement norm. -/
theorem sourceLiftedCompression_energy
    (P A : Operator D →ₗ[ℂ] Operator D) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (κ : ℝ) (X : Operator D) :
    (hsInner X (sourceLiftedCompression P A κ X)).re=
      (hsInner (P X) (A (P X))).re+
      κ*((hsInner X X).re-(hsInner (P X) (P X)).re) := by
  have hadd (Y Z : Operator D) : hsInner X (Y+Z)=hsInner X Y+hsInner X Z := by
    simp [hsInner, Matrix.mul_add, Matrix.trace_add]
  have hpair : hsInner X (P X)=hsInner (P X) (P X) := by
    simpa only [hPP] using (hP X (P X)).symm
  rw [sourceLiftedCompression_apply, hadd, Complex.add_re, ← hP,
    hsInner_smul_right, ofReal_mul_re, hsInner_sub_right, Complex.sub_re, hpair]

/-- A constant compressed form has exactly that value at every one of its
rank-many ordered positions, even when the value is zero or negative. -/
theorem sourceLiftedCompression_ordered_eq_of_constant_range
    (P A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hA : SourceSelfAdjoint A)
    (hPP : ∀ X, P (P X)=P X)
    {κ q : ℝ} (hqκ : q<κ)
    (hconstant : ∀ X, P X=X → (hsInner X (A X)).re=q*(hsInner X X).re)
    (k : Fin (Fintype.card (Fin D × Fin D)))
    (hk : k.val<Module.finrank ℂ (LinearMap.range P)) :
    sourceOrderedEigenvalue (sourceLiftedCompression P A κ)
      (sourceLiftedCompression_selfAdjoint P A hP hA κ) k=q := by
  apply le_antisymm
  · apply (sourceOrderedEigenvalue_le_iff _ _ k q).mpr
    change k.val<sourceCompressedCount P A hP hA κ q
    rw [sourceCompressedCount_eq_rank_of_range_cap P A hP hA hPP hqκ
      (fun X hX => (hconstant X hX).le)]
    exact hk
  · apply sourceOrderedEigenvalue_ge_of_form_bound
    intro X
    rw [sourceLiftedCompression_energy P A hP hPP, hconstant (P X) (hPP X)]
    have hnorm := source_projection_norm_le P hP hPP X
    nlinarith only [mul_nonneg (sub_nonneg.mpr hqκ.le) (sub_nonneg.mpr hnorm)]

end Qatlib.Concepts.GibbsSource.SpectralGeom
