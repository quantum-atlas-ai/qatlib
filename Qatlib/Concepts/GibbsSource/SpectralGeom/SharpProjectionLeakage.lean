/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSubspaceSpectralBasis

@[expose] public section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

/-! Sharp projection transport on the complete complex Hilbert space.
The lower amplitude is truncated at zero before squaring. -/

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
namespace SharpProjectionLeakage

open ResidualTransport

/-- The exact two-dimensional lower projection-probability envelope. -/
noncomputable def sharpLeakage (eps a : ℝ) : ℝ :=
  (max 0 (Real.sqrt (1-eps^2)*Real.sqrt a-eps*Real.sqrt (1-a)))^2

/-- Sharp Leakage nonneg for the stated finite source data. -/
theorem sharpLeakage_nonneg (eps a : ℝ) : 0 ≤ sharpLeakage eps a :=
  sq_nonneg _

/-- Sharp Leakage zero for the stated finite source data. -/
theorem sharpLeakage_zero {a : ℝ} (ha : 0 ≤ a) :
    sharpLeakage 0 a=a := by
  simp [sharpLeakage, Real.sqrt_nonneg, Real.sq_sqrt ha]

/-- Sharp Leakage one for the stated finite source data. -/
theorem sharpLeakage_one (a : ℝ) : sharpLeakage 1 a=0 := by
  simp [sharpLeakage, Real.sqrt_nonneg]

/-- Sharp Leakage eq zero of le sq for the stated finite source data. -/
theorem sharpLeakage_eq_zero_of_le_sq {eps a : ℝ}
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hle : a ≤ eps^2) :
    sharpLeakage eps a=0 := by
  have he : 0 ≤ 1-eps^2 := by nlinarith
  have hb : 0 ≤ 1-a := by linarith
  have hs : (Real.sqrt (1-eps^2)*Real.sqrt a)^2 ≤
      (eps*Real.sqrt (1-a))^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt he, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith
  have hc := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg heps (Real.sqrt_nonneg _))).mp hs
  simp only [sharpLeakage, max_eq_left (sub_nonpos.mpr hc), zero_pow (by norm_num : 2≠0)]

/-- Sharp Leakage mono for the stated finite source data. -/
theorem sharpLeakage_mono {eps a b : ℝ} (heps : 0 ≤ eps) (hab : a ≤ b) :
    sharpLeakage eps a ≤ sharpLeakage eps b := by
  have hfirst : Real.sqrt (1-eps^2)*Real.sqrt a ≤
      Real.sqrt (1-eps^2)*Real.sqrt b :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg _)
  have hsecond : eps*Real.sqrt (1-b) ≤ eps*Real.sqrt (1-a) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) heps
  apply (sq_le_sq₀ (le_max_left 0 _) (le_max_left 0 _)).mpr
  exact max_le_max le_rfl (by linarith)


/-- Rational lower bounds can certify the sharp expression without numerically
evaluating square roots. The final nonnegativity check preserves the clamp. -/
theorem square_budget_le_sharpLeakage {eps a A B : ℝ}
    (heps : 0≤eps) (heps1 : eps≤1) (hA : 0≤A) (hAsq : A^2≤a)
    (hB : 0≤B) (hBsq : 1-a≤B^2) (hbudget : 0≤(1-eps^2)*A-eps*B) :
    ((1-eps^2)*A-eps*B)^2≤sharpLeakage eps a := by
  have he : 0≤1-eps^2 := by nlinarith
  have he1 : 1-eps^2≤1 := by nlinarith [sq_nonneg eps]
  have hc : 1-eps^2≤Real.sqrt (1-eps^2) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hsa : A≤Real.sqrt a := Real.le_sqrt_of_sq_le hAsq
  have hsb : Real.sqrt (1-a)≤B := (Real.sqrt_le_left hB).mpr hBsq
  have hp := mul_le_mul hc hsa hA (Real.sqrt_nonneg (1-eps^2))
  have hn := mul_le_mul_of_nonneg_left hsb heps
  have hb : (1-eps^2)*A-eps*B≤
      Real.sqrt (1-eps^2)*Real.sqrt a-eps*Real.sqrt (1-a) := by linarith
  unfold sharpLeakage
  exact (sq_le_sq₀ hbudget (le_max_left _ _)).mpr (hb.trans (le_max_right _ _))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Pythagoras for an actual self-adjoint idempotent. -/
theorem projection_norm_sq_split
    (P : F →L[ℂ] F) (hP : IsSelfAdjoint P) (hPP : ∀ x, P (P x)=P x)
    (x : F) :
    ‖x‖^2=‖P x‖^2+‖x-P x‖^2 := by
  have hi : inner ℂ x (P x)=inner ℂ (P x) (P x) := by
    have h := hP.isSymmetric x (P x)
    change inner ℂ (P x) (P x)=inner ℂ x (P (P x)) at h
    rw [hPP] at h
    exact h.symm
  rw [norm_sub_sq (𝕜 := ℂ), hi, inner_self_eq_norm_sq (𝕜 := ℂ)]
  ring

/-- Complement self Adjoint for the stated finite source data. -/
theorem complement_selfAdjoint
    (P : F →L[ℂ] F) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (ContinuousLinearMap.id ℂ F-P) :=
  (IsSelfAdjoint.one (F →L[ℂ] F)).sub hP

omit [CompleteSpace F] in
/-- Complement idempotent for the stated finite source data. -/
theorem complement_idempotent (P : F →L[ℂ] F) (hPP : ∀ x, P (P x)=P x)
    (x : F) :
    (ContinuousLinearMap.id ℂ F-P) ((ContinuousLinearMap.id ℂ F-P) x)=
      (ContinuousLinearMap.id ℂ F-P) x := by
  simp only [_root_.sub_apply, ContinuousLinearMap.id_apply, map_sub, hPP]
  abel

/-- Orthogonal projection of a vector in the first range retains the cosine
factor dictated by the actual operator-norm distance. -/
theorem projected_range_norm_ge
    (P R : F →L[ℂ] F) (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    {eps : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hdist : ‖P-R‖ ≤ eps)
    (x : F) :
    Real.sqrt (1-eps^2)*‖P x‖ ≤ ‖R (P x)‖ := by
  have he : 0 ≤ 1-eps^2 := by nlinarith
  have hd : ‖P x-R (P x)‖ ≤ eps*‖P x‖ := by
    have h := ((P-R).le_opNorm (P x)).trans
      (mul_le_mul_of_nonneg_right hdist (norm_nonneg _))
    simpa only [_root_.sub_apply, hPP] using h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hp := projection_norm_sq_split R hR hRR (P x)
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt he]
  nlinarith

/-- Sharp lower amplitude from orthogonal decomposition and reverse triangle.
No singular-vector, principal-angle, or leakage conclusion is an input. -/
theorem projection_amplitude_le
    (P R : F →L[ℂ] F) (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    {eps : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hdist : ‖P-R‖ ≤ eps)
    (x : F) :
    Real.sqrt (1-eps^2)*‖P x‖-eps*‖x-P x‖ ≤ ‖R x‖ := by
  have hrange := projected_range_norm_ge P R hPP hR hRR heps heps1 hdist x
  have hzero : P (x-P x)=0 := by rw [map_sub, hPP, sub_self]
  have hout : ‖R (x-P x)‖ ≤ eps*‖x-P x‖ := by
    have h := ((P-R).le_opNorm (x-P x)).trans
      (mul_le_mul_of_nonneg_right hdist (norm_nonneg _))
    simpa only [_root_.sub_apply, hzero, zero_sub, norm_neg] using h
  have htri : ‖R (P x)‖ ≤ ‖R x‖+‖R (x-P x)‖ := by
    calc
      _ = ‖R x-R (x-P x)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖R x‖+‖R (x-P x)‖ := norm_sub_le _ _
  linarith

/-- Sharp probability transport for every complex unit vector, with the
necessary zero truncation in the low-overlap regime. -/
theorem sharpLeakage_le_projection_norm_sq
    (P R : F →L[ℂ] F) (hP : IsSelfAdjoint P) (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    {eps : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hdist : ‖P-R‖ ≤ eps)
    (x : F) (hx : ‖x‖=1) :
    sharpLeakage eps (‖P x‖^2) ≤ ‖R x‖^2 := by
  have hp := projection_norm_sq_split P hP hPP x
  rw [hx, one_pow] at hp
  have he : 1-‖P x‖^2=‖x-P x‖^2 := by linarith
  have ha := projection_amplitude_le P R hPP hR hRR heps heps1 hdist x
  rw [sharpLeakage, he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact (sq_le_sq₀ (le_max_left 0 _) (norm_nonneg _)).mpr (max_le (norm_nonneg _) ha)

/-- Sharp Amplitude le one for the stated finite source data. -/
theorem sharpAmplitude_le_one {eps a : ℝ} (heps : 0 ≤ eps) (ha1 : a ≤ 1) :
    max 0 (Real.sqrt (1-eps^2)*Real.sqrt a-eps*Real.sqrt (1-a)) ≤ 1 := by
  have hc : Real.sqrt (1-eps^2) ≤ 1 :=
    (Real.sqrt_le_left (by norm_num : (0:ℝ)≤1)).mpr (by nlinarith)
  have ha : Real.sqrt a ≤ 1 := (Real.sqrt_le_left (by norm_num : (0:ℝ)≤1)).mpr (by simpa using ha1)
  have hp : Real.sqrt (1-eps^2)*Real.sqrt a ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul hc ha (Real.sqrt_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact max_le (by norm_num) (by nlinarith [mul_nonneg heps (Real.sqrt_nonneg (1-a))])

/-- Sharp Leakage le one for the stated finite source data. -/
theorem sharpLeakage_le_one {eps a : ℝ} (heps : 0 ≤ eps) (ha1 : a ≤ 1) :
    sharpLeakage eps a ≤ 1 := by
  have h := pow_le_pow_left₀ (le_max_left 0 _) (sharpAmplitude_le_one heps ha1) 2
  simpa only [sharpLeakage, one_pow] using h

/-- A trial-space leakage floor controls the entire band/trial cross block. -/
theorem trial_band_norm_le
    (P Q : F →L[ℂ] F)
    (hP : IsSelfAdjoint P) (hPP : ∀ x, P (P x)=P x)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ x, Q (Q x)=Q x)
    {a : ℝ} (ha1 : a ≤ 1)
    (htrial : ∀ x, P x=x → a*‖x‖^2 ≤ ‖x-Q x‖^2) :
    ‖Q.comp P‖ ≤ Real.sqrt (1-a) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  change ‖Q (P x)‖ ≤ Real.sqrt (1-a)*‖x‖
  have hfloor := htrial (P x) (hPP x)
  have hsplit := projection_norm_sq_split Q hQ hQQ (P x)
  have hp := pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le P hP hPP x) 2
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ha1)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ha1)]
  nlinarith

/-- On the actual band range, the complementary true-low amplitude inherits
the sharp cosine/sine budget from the complete trial leakage floor. -/
theorem band_complement_amplitude_le
    (P R Q : F →L[ℂ] F)
    (hP : IsSelfAdjoint P) (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ x, Q (Q x)=Q x)
    {eps a : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdist : ‖P-R‖ ≤ eps)
    (htrial : ∀ x, P x=x → a*‖x‖^2 ≤ ‖x-Q x‖^2)
    (y : F) (hy : Q y=y) :
    max 0 (Real.sqrt (1-eps^2)*Real.sqrt a-eps*Real.sqrt (1-a))*‖y‖ ≤
      ‖y-R y‖ := by
  have hQP := trial_band_norm_le P Q hP hPP hQ hQQ ha1 htrial
  have hPQ : ‖P.comp Q‖ ≤ Real.sqrt (1-a) := by
    have h : ‖(Q.comp P).adjoint‖ ≤ Real.sqrt (1-a) := by
      simpa only [LinearIsometryEquiv.norm_map] using hQP
    simpa only [ContinuousLinearMap.adjoint_comp, hP.adjoint_eq, hQ.adjoint_eq] using h
  have hpy : ‖P y‖ ≤ Real.sqrt (1-a)*‖y‖ := by
    have h := ((P.comp Q).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right hPQ (norm_nonneg y))
    simpa only [ContinuousLinearMap.comp_apply, hy] using h
  have hout : Real.sqrt a*‖y‖ ≤ ‖y-P y‖ := by
    have hs := projection_norm_sq_split P hP hPP y
    have hp := pow_le_pow_left₀ (norm_nonneg _) hpy 2
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ha1)] at hp
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt ha]
    nlinarith
  have hdist' :
      ‖(ContinuousLinearMap.id ℂ F-P)-(ContinuousLinearMap.id ℂ F-R)‖ ≤ eps := by
    have hid : (ContinuousLinearMap.id ℂ F-P)-(ContinuousLinearMap.id ℂ F-R)=R-P := by abel
    rw [hid, norm_sub_rev]
    exact hdist
  have hsharp := projection_amplitude_le
    (ContinuousLinearMap.id ℂ F-P) (ContinuousLinearMap.id ℂ F-R)
    (complement_idempotent P hPP) (complement_selfAdjoint R hR)
    (complement_idempotent R hRR) heps heps1 hdist' y
  change Real.sqrt (1-eps^2)*‖y-P y‖-eps*‖y-(y-P y)‖ ≤ ‖y-R y‖ at hsharp
  have hid : y-(y-P y)=P y := by abel
  rw [hid] at hsharp
  have hbudget :
      (Real.sqrt (1-eps^2)*Real.sqrt a-eps*Real.sqrt (1-a))*‖y‖ ≤ ‖y-R y‖ := by
    have hfirst := mul_le_mul_of_nonneg_left hout (Real.sqrt_nonneg (1-eps^2))
    have hsecond := mul_le_mul_of_nonneg_left hpy heps
    nlinarith
  by_cases h : 0 ≤ Real.sqrt (1-eps^2)*Real.sqrt a-eps*Real.sqrt (1-a)
  · rw [max_eq_right h]
    exact hbudget
  · rw [max_eq_left (le_of_not_ge h), zero_mul]
    exact norm_nonneg _

/-- Uniform sharp leakage for every coherent unit vector in the true range.
Only the trial range is assumed to satisfy the supplied floor. -/
theorem uniform_sharp_leakage
    (P R Q : F →L[ℂ] F)
    (hP : IsSelfAdjoint P) (hPP : ∀ x, P (P x)=P x)
    (hR : IsSelfAdjoint R) (hRR : ∀ x, R (R x)=R x)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ x, Q (Q x)=Q x)
    {eps a : ℝ} (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdist : ‖P-R‖ ≤ eps)
    (htrial : ∀ x, P x=x → a*‖x‖^2 ≤ ‖x-Q x‖^2)
    (x : F) (hx : ‖x‖=1) (hRx : R x=x) :
    sharpLeakage eps a ≤ ‖x-Q x‖^2 := by
  have hnon : 0 ≤ 1-sharpLeakage eps a :=
    sub_nonneg.mpr (sharpLeakage_le_one heps ha1)
  have hRQ : ‖R.comp Q‖ ≤ Real.sqrt (1-sharpLeakage eps a) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro y
    have hamp := band_complement_amplitude_le P R Q hP hPP hR hRR hQ hQQ
      heps heps1 ha ha1 hdist htrial (Q y) (hQQ y)
    have hsq := pow_le_pow_left₀
      (mul_nonneg (le_max_left 0 _) (norm_nonneg (Q y))) hamp 2
    rw [mul_pow] at hsq
    change sharpLeakage eps a*‖Q y‖^2 ≤ ‖Q y-R (Q y)‖^2 at hsq
    have hs := projection_norm_sq_split R hR hRR (Q y)
    have hQn := pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le Q hQ hQQ y) 2
    have hm := mul_le_mul_of_nonneg_left hQn hnon
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hnon]
    change ‖R (Q y)‖^2 ≤ (1-sharpLeakage eps a)*‖y‖^2
    nlinarith
  have hQR : ‖Q.comp R‖ ≤ Real.sqrt (1-sharpLeakage eps a) := by
    have h : ‖(R.comp Q).adjoint‖ ≤ Real.sqrt (1-sharpLeakage eps a) := by
      simpa only [LinearIsometryEquiv.norm_map] using hRQ
    simpa only [ContinuousLinearMap.adjoint_comp, hQ.adjoint_eq, hR.adjoint_eq] using h
  have hxQ : ‖Q x‖ ≤ Real.sqrt (1-sharpLeakage eps a) := by
    have h := ((Q.comp R).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hQR (norm_nonneg x))
    simpa only [ContinuousLinearMap.comp_apply, hRx, hx, mul_one] using h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hxQ 2
  rw [Real.sq_sqrt hnon] at hsq
  have hs := projection_norm_sq_split Q hQ hQQ x
  rw [hx, one_pow] at hs
  nlinarith


/-- An isometric trial frame supplies the range floor in the projection theorem. -/
theorem uniform_sharp_leakage_of_trial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] F) (R Q : F →L[ℂ] F)
    (hU : ∀ z, ‖U z‖=‖z‖)
    (hR : IsSelfAdjoint R) (hRR : ∀ y, R (R y)=R y)
    (hQ : IsSelfAdjoint Q) (hQQ : ∀ y, Q (Q y)=Q y)
    {eps a : ℝ} (heps : 0≤eps) (heps1 : eps≤1) (ha : 0≤a) (ha1 : a≤1)
    (hdist : ‖trialProjection U-R‖≤eps)
    (htrial : ∀ z, a*‖z‖^2≤‖U z-Q (U z)‖^2)
    (x : F) (hx : ‖x‖=1) (hRx : R x=x) :
    sharpLeakage eps a≤‖x-Q x‖^2 := by
  apply uniform_sharp_leakage (trialProjection U) R Q
    (trialProjection_selfAdjoint U) (trialProjection_idempotent U hU)
    hR hRR hQ hQQ heps heps1 ha ha1 hdist _ x hx hRx
  intro y hy
  have hp : U (U.adjoint y)=y := hy
  have hn : ‖U.adjoint y‖=‖y‖ := by rw [← hU, hp]
  simpa only [hp, hn] using htrial (U.adjoint y)

variable {D : ℕ}

/-- Source vector sub for the stated finite source data. -/
theorem source_vector_sub (X Y : Operator D) :
    sourceEuclideanVector (X-Y)=sourceEuclideanVector X-sourceEuclideanVector Y := by
  ext i
  rfl

/-- Source Map idempotent for the stated finite source data. -/
theorem sourceMap_idempotent (Q : Operator D →ₗ[ℂ] Operator D)
    (hQQ : ∀ X, Q (Q X)=Q X) (x : EuclideanSpace ℂ (Fin D×Fin D)) :
    sourceMap Q (sourceMap Q x)=sourceMap Q x := by
  obtain ⟨X,rfl⟩ := source_vector_surjective x
  simp only [sourceMap_apply,hQQ]

/-- Residual, actual spectral separation, Gibbs centering and the actual low-rank
count imply sharp leakage of every unit vector in the full source low space.
The true spectral basis is constructed internally, and the norm is the complex
Hilbert--Schmidt norm transported to Euclidean coordinates. -/
theorem source_low_sharp_leakage_of_card
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0≤(hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X=0 → ∃ c : ℂ, X=c•G)
    {q : ℕ} {cutoff μ lam η eps a : ℝ}
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
    (ha : 0≤a) (ha1 : a≤1)
    (htrial : ∀ z, a*‖z‖^2≤‖U z-sourceMap Q (U z)‖^2)
    (X : Operator D) (hX : (hsInner X X).re=1)
    (hRX : sourcePositiveLowProjection L hL cutoff X=X) :
    sharpLeakage eps a≤(hsInner (X-Q X) (X-Q X)).re := by
  let R := sourcePositiveLowProjection L hL cutoff
  have hR : SourceSelfAdjoint R := sourceSpectralCut_selfAdjoint L hL _
  have hRR : ∀ Y, R (R Y)=R Y := sourceSpectralCut_idempotent L hL _
  have hd := (source_low_trialProjection_sub_norm_le_of_card L hL hpos G hker
    hcard U hU hcut hgap hsep hcenter hcap hres).trans hbudget
  have hx : ‖sourceEuclideanVector X‖=1 := by
    have hs := source_vector_norm_sq X
    have hn := norm_nonneg (sourceEuclideanVector X)
    rw [hX] at hs
    nlinarith
  have hfix : sourceMap R (sourceEuclideanVector X)=sourceEuclideanVector X := by
    rw [sourceMap_apply]
    exact congrArg sourceEuclideanVector hRX
  have h := uniform_sharp_leakage_of_trial U (sourceMap R) (sourceMap Q)
    hU (sourceMap_selfAdjoint R hR) (sourceMap_idempotent R hRR)
    (sourceMap_selfAdjoint Q hQ) (sourceMap_idempotent Q hQQ)
    heps heps1 ha ha1 hd htrial (sourceEuclideanVector X) hx hfix
  simpa only [sourceMap_apply,← source_vector_sub,source_vector_norm_sq] using h

/-- The band is the actual two-leg compression in physical energy coordinates;
no chosen low-space projection or replacement matrix enters this conclusion. -/
theorem source_low_energy_band_sharp_leakage_of_card
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0≤(hsInner X (L X)).re) (G : Operator D)
    (hker : ∀ X, L X=0 → ∃ c : ℂ, X=c•G)
    {q : ℕ} {cutoff μ lam η eps a : ℝ}
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
    (ha : 0≤a) (ha1 : a≤1)
    (htrial : ∀ z, a*‖z‖^2≤
      ‖U z-sourceMap (sourceCompression (hermEnergyBand H hH S)) (U z)‖^2)
    (X : Operator D) (hX : (hsInner X X).re=1)
    (hRX : sourcePositiveLowProjection L hL cutoff X=X) :
    sharpLeakage eps a≤
      (hsInner (X-hermEnergyBand H hH S*X*hermEnergyBand H hH S)
        (X-hermEnergyBand H hH S*X*hermEnergyBand H hH S)).re :=
  source_low_sharp_leakage_of_card L hL hpos G hker hcard U hU hcut hgap
    hsep hcenter hcap hres heps heps1 hbudget
    (sourceCompression (hermEnergyBand H hH S))
    (sourceCompression_selfAdjoint _ (hermEnergyBand_isHermitian H hH S))
    (sourceCompression_idempotent _ (hermEnergyBand_idempotent H hH S))
    ha ha1 htrial X hX hRX

end SharpProjectionLeakage
end Qatlib.Concepts.GibbsSource.SpectralGeom
