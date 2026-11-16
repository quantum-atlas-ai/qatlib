/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.EnergyBandLeakage
public import Qatlib.Concepts.GibbsSource.SpectralGeom.SourceGapCoercivity

@[expose] public section


/-! Actual positive low spectral projections and uniform energy-band leakage.
The complete Hermitian eigenbasis retains all complex source modes. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
variable {D : ℕ}

/-- Source hs Inner finset sum right for the stated finite source data. -/
theorem source_hsInner_finset_sum_right {ι : Type*}
    (s : Finset ι) (X : Operator D) (Y : ι → Operator D) :
    hsInner X (∑ i ∈ s, Y i) = ∑ i ∈ s, hsInner X (Y i) := by
  simp only [hsInner, Matrix.mul_sum, Matrix.trace_sum]

/-- Source hs Inner finset sum left for the stated finite source data. -/
theorem source_hsInner_finset_sum_left {ι : Type*}
    (s : Finset ι) (X : ι → Operator D) (Y : Operator D) :
    hsInner (∑ i ∈ s, X i) Y = ∑ i ∈ s, hsInner (X i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    simp only [hsInner, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add] at ih ⊢
    exact congrArg (fun z => Matrix.trace ((X i)ᴴ * Y) + z) ih

/-- Orthogonality of the genuine complete source eigenoperators. -/
theorem sourceEigenoperator_inner
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i j : Fin D × Fin D) :
    hsInner (sourceEigenoperator L hL i) (sourceEigenoperator L hL j) =
      if i=j then 1 else 0 := by
  rw [← sourceEuclideanVector_inner,
    sourceEuclideanVector_eigenoperator, sourceEuclideanVector_eigenoperator]
  exact orthonormal_iff_ite.mp
    (sourceSuperMatrix_isHermitian L hL).eigenvectorBasis.orthonormal i j

/-- Source Eigenoperator norm Sq for the stated finite source data. -/
theorem sourceEigenoperator_normSq
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (i : Fin D × Fin D) :
    (hsInner (sourceEigenoperator L hL i) (sourceEigenoperator L hL i)).re=1 := by
  simp [sourceEigenoperator_inner]

/-- Orthogonal projection onto specified modes of the actual source matrix. -/
noncomputable def sourceSpectralCut
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) : Operator D →ₗ[ℂ] Operator D where
  toFun X := ∑ i ∈ S, hsInner (sourceEigenoperator L hL i) X • sourceEigenoperator L hL i
  map_add' X Y := by
    simp only [hsInner, Matrix.mul_add, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [hsInner_smul_right, smul_smul, Finset.smul_sum]
    rfl

/-- Source Spectral Cut coefficient for the stated finite source data. -/
theorem sourceSpectralCut_coefficient
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (X : Operator D) (i : Fin D × Fin D) :
    hsInner (sourceEigenoperator L hL i) (sourceSpectralCut L hL S X) =
      if i ∈ S then hsInner (sourceEigenoperator L hL i) X else 0 := by
  classical
  change hsInner (sourceEigenoperator L hL i)
    (∑ j ∈ S, hsInner (sourceEigenoperator L hL j) X • sourceEigenoperator L hL j) = _
  simp [source_hsInner_finset_sum_right, hsInner_smul_right,
    sourceEigenoperator_inner]

/-- Source Spectral Cut self Adjoint for the stated finite source data. -/
theorem sourceSpectralCut_selfAdjoint
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    SourceSelfAdjoint (sourceSpectralCut L hL S) := by
  intro X Y
  change hsInner (∑ i ∈ S, hsInner (sourceEigenoperator L hL i) X •
      sourceEigenoperator L hL i) Y =
    hsInner X (∑ i ∈ S, hsInner (sourceEigenoperator L hL i) Y •
      sourceEigenoperator L hL i)
  simp only [source_hsInner_finset_sum_left, source_hsInner_finset_sum_right,
    hsInner_smul_left, hsInner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hsInner_conj_swap]
  ring

/-- Source Spectral Cut idempotent for the stated finite source data. -/
theorem sourceSpectralCut_idempotent
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (X : Operator D) :
    sourceSpectralCut L hL S (sourceSpectralCut L hL S X) =
      sourceSpectralCut L hL S X := by
  classical
  change (∑ i ∈ S, hsInner (sourceEigenoperator L hL i)
    (sourceSpectralCut L hL S X) • sourceEigenoperator L hL i) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [sourceSpectralCut_coefficient, ite_eq_left hi]

/-- Source Spectral Cut norm Sq for the stated finite source data. -/
theorem sourceSpectralCut_normSq
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (X : Operator D) :
    (hsInner (sourceSpectralCut L hL S X) (sourceSpectralCut L hL S X)).re =
      ∑ i ∈ S, Complex.normSq (hsInner (sourceEigenoperator L hL i) X) := by
  classical
  rw [source_hsNormSq_eq_sum_coefficients L hL]
  simp only [sourceSpectralCut_coefficient, apply_ite Complex.normSq, Complex.normSq_zero]
  rw [← Finset.sum_filter]
  simp

/-- The actual positive modes below the specified cutoff, with multiplicity. -/
noncomputable def sourcePositiveLowModes
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (lam : ℝ) :
    Finset (Fin D × Fin D) := by
  classical
  exact Finset.univ.filter (fun i => 0 < sourceEigenvalues L hL i ∧
    sourceEigenvalues L hL i ≤ lam)

/-- The actual positive low spectral projector of the full parent. -/
noncomputable def sourcePositiveLowProjection
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L) (lam : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  sourceSpectralCut L hL (sourcePositiveLowModes L hL lam)

/-- Source Positive Low Projection kernel orthogonal for the stated finite source data. -/
theorem sourcePositiveLowProjection_kernel_orthogonal
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (G : Operator D) (hG : L G=0) (lam : ℝ) (X : Operator D) :
    hsInner G (sourcePositiveLowProjection L hL lam X)=0 := by
  classical
  change hsInner G (∑ i ∈ sourcePositiveLowModes L hL lam,
    hsInner (sourceEigenoperator L hL i) X • sourceEigenoperator L hL i)=0
  rw [source_hsInner_finset_sum_right]
  apply Finset.sum_eq_zero
  intro i hi
  have hp : 0 < sourceEigenvalues L hL i :=
    (Finset.mem_filter.mp hi).2.1
  rw [hsInner_smul_right,
    hsInner_kernel_eigenvector_eq_zero L hL G _ hG
      (Complex.ofReal_ne_zero.mpr hp.ne') (sourceEigenoperator_apply L hL i),
    mul_zero]

/-- The global cap splits into the actual low-mode cap and its complement. -/
theorem sourcePositiveLowProjection_split_cap
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    {B lam : ℝ}
    (hcap : ∀ Z, (hsInner Z (L Z)).re ≤ B*(hsInner Z Z).re)
    (X : Operator D) :
    (hsInner X (L X)).re ≤ B*(hsInner X X).re -
      (B-lam)*(hsInner (sourcePositiveLowProjection L hL lam X)
        (sourcePositiveLowProjection L hL lam X)).re := by
  classical
  have hall (i : Fin D × Fin D) : sourceEigenvalues L hL i ≤ B := by
    have hi := hcap (sourceEigenoperator L hL i)
    rw [sourceEigenoperator_apply, hsInner_smul_right, ofReal_mul_re,
      sourceEigenoperator_normSq, mul_one, mul_one] at hi
    exact hi
  rw [source_energy_eq_sum_eigenvalues L hL, source_hsNormSq_eq_sum_coefficients L hL]
  unfold sourcePositiveLowProjection
  rw [sourceSpectralCut_normSq]
  simp only [sourcePositiveLowModes, Finset.sum_filter]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hlow : 0 < sourceEigenvalues L hL i ∧ sourceEigenvalues L hL i ≤ lam
  · rw [ite_eq_left hlow]
    have h := mul_le_mul_of_nonneg_right hlow.2
      (Complex.normSq_nonneg (hsInner (sourceEigenoperator L hL i) X))
    nlinarith only [h]
  · rw [ite_eq_right hlow, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right (hall i) (Complex.normSq_nonneg _)

/-- Source hs Inner cauchy sq for the stated finite source data. -/
theorem source_hsInner_cauchy_sq (X Y : Operator D) :
    Complex.normSq (hsInner X Y) ≤ (hsInner X X).re*(hsInner Y Y).re := by
  have hi := norm_inner_le_norm (𝕜 := ℂ) (sourceEuclideanVector X) (sourceEuclideanVector Y)
  have hn (Z : Operator D) : ‖sourceEuclideanVector Z‖^2 = (hsInner Z Z).re := by
    rw [PiLp.norm_sq_eq_of_L2, hsInner_self_re_sum]
    simp [sourceEuclideanVector, sourceVector, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]
  rw [sourceEuclideanVector_inner] at hi
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖hsInner X Y‖^2 ≤ (‖sourceEuclideanVector X‖*‖sourceEuclideanVector Y‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ = _ := by rw [mul_pow, hn, hn]

/-- A low spectral subspace has the same centered-band angle bound as an
individual eigenvector. The split cap records the whole subspace. -/
theorem source_subspace_projection_le
    (L R : Operator D →ₗ[ℂ] Operator D)
    (hR : SourceSelfAdjoint R) (X Y : Operator D) {B α lam : ℝ}
    (hX : (hsInner X X).re=1) (hRX : R X=X)
    (hXY : hsInner X Y=hsInner Y Y) (hαB : α≤B) (hlamα : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re ≤ B*(hsInner Z Z).re -
      (B-lam)*(hsInner (R Z) (R Z)).re)
    (hband : α*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (α-lam)/(B-lam) ≤ 1-(hsInner Y Y).re := by
  let t := (hsInner Y Y).re
  have ht : 0≤t := hsInner_self_nonneg Y
  have hB : 0<B-lam := by linarith
  have hYY : hsInner Y Y=(t:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hsInner_self_re Y
  have hcoeff : hsInner X (R Y)=(t:ℂ) := by rw [← hR, hRX, hXY, hYY]
  have hcs := source_hsInner_cauchy_sq X (R Y)
  rw [hcoeff, hX] at hcs
  simp only [Complex.normSq_ofReal, one_mul] at hcs
  have hc := hcap Y
  change α*t≤_ at hband
  change _≤B*t-(B-lam)*(hsInner (R Y) (R Y)).re at hc
  by_cases ht0 : t=0
  · change _≤1-t
    rw [ht0, sub_zero]
    exact (div_le_iff₀ hB).mpr (by linarith)
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hnorm : (B-lam)*t≤B-α := by
    apply (mul_le_mul_iff_left₀ htpos).mp
    have hm := mul_le_mul_of_nonneg_left hcs hB.le
    nlinarith
  exact (div_le_iff₀ hB).mpr (by change α-lam≤(1-t)*(B-lam); nlinarith)

/-- Uniform leakage for every coherent combination in the actual positive
low spectral space. The projection and its Gibbs mass are actual objects. -/
theorem source_positiveLowProjection_centered_leakage
    (L Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G X : Operator D) {B α lam : ℝ}
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hX : (hsInner X X).re=1)
    (hRX : sourcePositiveLowProjection L hL lam X=X)
    (hp : 0<(hsInner (Q G) (Q G)).re)
    (hαB : α≤B) (hlamα : lam<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    (hsInner (Q G) (Q G)).re*((α-lam)/(B-lam)) ≤
      (hsInner (X-Q X) (X-Q X)).re := by
  have horth : hsInner G X=0 := by
    rw [← hRX]
    exact sourcePositiveLowProjection_kernel_orthogonal L hL G hLG lam X
  obtain ⟨hf, ho, hxy, hpdist⟩ :=
    source_centered_projection Q hQ hQQ G X hG hX horth hp
  have he := source_subspace_projection_le L (sourcePositiveLowProjection L hL lam)
    (sourceSpectralCut_selfAdjoint L hL _) X _ hX hRX hxy hαB hlamα
    (sourcePositiveLowProjection_split_cap L hL hcap) (hband _ hf ho)
  exact (mul_le_mul_of_nonneg_left he hp.le).trans hpdist


end Qatlib.Concepts.GibbsSource.SpectralGeom
