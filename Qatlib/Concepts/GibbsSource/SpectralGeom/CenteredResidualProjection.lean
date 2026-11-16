/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.BlockSpectralCertification

@[expose] public section


/-! Centered residual squares control actual spectral projections.
Finite-dimensional range duality supplies the reverse angle and the
full Hilbert--Schmidt projection difference. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- Centered hs Inner self real for the stated finite source data. -/
private theorem centered_hsInner_self_real (X : Operator D) :
    hsInner X X = ((hsInner X X).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hsInner_self_re X

/-- Parseval for the actual centered residual, with all spectral coefficients. -/
theorem source_centeredResidual_normSq
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (c : ℝ) (X : Operator D) :
    (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re =
      ∑ i, (sourceEigenvalues L hL i-c)^2 *
        Complex.normSq (hsInner (sourceEigenoperator L hL i) X) := by
  classical
  rw [source_hsNormSq_eq_sum_coefficients L hL]
  apply Finset.sum_congr rfl
  intro i _
  have hc : hsInner (sourceEigenoperator L hL i) (L X-(c:ℂ) • X) =
      ((sourceEigenvalues L hL i-c:ℝ):ℂ) *
        hsInner (sourceEigenoperator L hL i) X := by
    rw [hsInner_sub_right, hsInner_smul_right,
      ← hL (sourceEigenoperator L hL i) X, sourceEigenoperator_apply,
      hsInner_smul_left]
    simp only [star_ofReal, Complex.ofReal_sub]
    ring
  rw [hc, Complex.normSq_mul, Complex.normSq_ofReal]
  ring


/-- The residual norm is the quadratic form of the actual centered square. -/
theorem source_centeredResidual_square_form
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (c : ℝ) (X : Operator D) :
    (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re =
      (hsInner X (L (L X-(c:ℂ) • X)-
        (c:ℂ) • (L X-(c:ℂ) • X))).re := by
  have hcenter (Y Z : Operator D) :
      hsInner (L Y-(c:ℂ) • Y) Z=hsInner Y (L Z-(c:ℂ) • Z) := by
    rw [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left,
      hsInner_smul_right, star_ofReal, hL]
  exact congrArg Complex.re (hcenter X (L X-(c:ℂ) • X))

/-- Both sides of the exterior spectrum are measured from the center.
The actual kernel condition removes only the Gibbs coefficient. -/
theorem sourceSpectralCut_centeredResidual_square_bound
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) (G : Operator D)
    (hker : ∀ Z, L Z=0 → ∃ a : ℂ, Z=a • G)
    {c d : ℝ}
    (hsep : ∀ i, i ∉ S → sourceEigenvalues L hL i≠0 →
      d^2 ≤ (sourceEigenvalues L hL i-c)^2)
    (X : Operator D) (hGX : hsInner G X=0) :
    d^2*(hsInner (X-sourceSpectralCut L hL S X)
      (X-sourceSpectralCut L hL S X)).re ≤
      (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re := by
  classical
  rw [source_centeredResidual_normSq L hL,
    source_hsNormSq_eq_sum_coefficients L hL, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hsInner_sub_right, sourceSpectralCut_coefficient]
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi, sub_self, Complex.normSq_zero, mul_zero]
    exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  · rw [ite_eq_right hi, sub_zero]
    by_cases hz : sourceEigenvalues L hL i=0
    · have he : L (sourceEigenoperator L hL i)=0 := by
        rw [sourceEigenoperator_apply, hz, Complex.ofReal_zero, zero_smul]
      obtain ⟨a, ha⟩ := hker (sourceEigenoperator L hL i) he
      have hcoeff : hsInner (sourceEigenoperator L hL i) X=0 := by
        rw [ha, hsInner_smul_left, hGX, mul_zero]
      simp [hcoeff]
    · exact mul_le_mul_of_nonneg_right (hsep i hi hz) (Complex.normSq_nonneg _)

/-- Equal finite range dimensions turn a directed projection angle into
the reverse angle, through the actual projection restriction. -/
theorem source_equalRank_projection_reverse
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range R))
    {a : ℝ} (ha : a<1)
    (hforward : ∀ X,
      (hsInner (P X-R (P X)) (P X-R (P X))).re ≤
        a*(hsInner (P X) (P X)).re)
    (Y : Operator D) :
    (hsInner (R Y-P (R Y)) (R Y-P (R Y))).re ≤
      a*(hsInner (R Y) (R Y)).re := by
  let f : LinearMap.range P →ₗ[ℂ] LinearMap.range R :=
    R.rangeRestrict.comp (LinearMap.range P).subtype
  have hfix (Z : LinearMap.range P) : P (Z : Operator D)=(Z : Operator D) := by
    obtain ⟨W, hW⟩ := Z.property
    rw [← hW, hPP]
  have hinj : Function.Injective f := by
    intro U V hUV
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hRUV : R ((U : Operator D)-(V : Operator D))=0 := by
      have h := congrArg (fun Z : LinearMap.range R => (Z : Operator D)) hUV
      change R (U : Operator D)=R (V : Operator D) at h
      rw [map_sub, h, sub_self]
    have h := hforward ((U : Operator D)-(V : Operator D))
    simp only [map_sub, hfix U, hfix V, hRUV, sub_zero] at h
    by_contra hne
    have hp := hsInner_self_pos hne
    have hstrict := mul_lt_mul_of_pos_right ha hp
    linarith
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨U, hU⟩ := hsurj ⟨R Y, ⟨Y, rfl⟩⟩
  have hRU : R (U : Operator D)=R Y :=
    congrArg (fun Z : LinearMap.range R => (Z : Operator D)) hU
  let x := (U : Operator D)
  let y := R Y
  have hPx : P x=x := hfix U
  have hRx : R x=y := hRU
  have hlower : (1-a)*(hsInner x x).re ≤ (hsInner y y).re := by
    have h := hforward x
    rw [hPx, source_projection_pythagoras R hR hRR, hRx] at h
    linarith
  have hinner : hsInner x (P y)=((hsInner y y).re:ℂ) := by
    rw [← hP, hPx]
    change hsInner x (R Y)=_
    rw [← hR, hRx, ← source_projection_pair R hR hRR Y Y,
      centered_hsInner_self_real]
    simp only [Complex.ofReal_re]
  have hcs := source_hsInner_cauchy_sq x (P y)
  rw [hinner, Complex.normSq_ofReal] at hcs
  have hp : 0 ≤ (hsInner (P y) (P y)).re := hsInner_self_nonneg _
  have hm := mul_le_mul_of_nonneg_right hlower hp
  have hc := mul_le_mul_of_nonneg_left hcs (sub_pos.mpr ha).le
  have hlower' : (1-a)*(hsInner y y).re ≤ (hsInner (P y) (P y)).re := by
    by_cases hy : (hsInner y y).re=0
    · rw [hy, mul_zero]
      exact hp
    · have hpos : 0<(hsInner y y).re :=
        lt_of_le_of_ne (hsInner_self_nonneg y) (Ne.symm hy)
      apply (mul_le_mul_iff_left₀ hpos).mp
      nlinarith only [hm, hc]
  rw [source_projection_pythagoras P hP hPP]
  change (hsInner y y).re-(hsInner (P y) (P y)).re ≤ a*(hsInner y y).re
  linarith

/-- The complete two-projection difference retains the directed-angle constant. -/
theorem source_equalRank_projection_difference
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range R))
    {a : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hforward : ∀ X,
      (hsInner (P X-R (P X)) (P X-R (P X))).re ≤
        a*(hsInner (P X) (P X)).re)
    (X : Operator D) :
    (hsInner (P X-R X) (P X-R X)).re ≤ a*(hsInner X X).re := by
  let V : Operator D →ₗ[ℂ] Operator D := LinearMap.id-R
  have hVapply (Y : Operator D) : V Y=Y-R Y := rfl
  have hV : SourceSelfAdjoint V := by
    intro Y Z
    rw [hVapply, hVapply, hsInner_sub_left, hsInner_sub_right, hR]
  have hVV (Y : Operator D) : V (V Y)=V Y := by
    simp only [hVapply, map_sub, hRR]
    abel
  have hdual := source_projection_angle_dual P V hP hV hPP hVV ha0
    (by simpa only [hVapply] using hforward) X
  have hreverse := source_equalRank_projection_reverse P R hP hR hPP hRR hdim
    ha1 hforward X
  let A := P (X-R X)
  let B := R X-P (R X)
  have hPA : P A=A := hPP _
  have hPB : P B=0 := by simp [B, map_sub, hPP]
  have hAB : hsInner A B=0 := by rw [← hPA, hP, hPB]; simp [hsInner]
  have hBA : hsInner B A=0 := by rw [hsInner_conj_swap, hAB]; simp
  have hsplit : (hsInner (P X-R X) (P X-R X)).re =
      (hsInner A A).re+(hsInner B B).re := by
    have he : P X-R X=A-B := by dsimp [A, B]; rw [map_sub]; abel
    rw [he, hsInner_sub_left A B (A-B), hsInner_sub_right A A B,
      hsInner_sub_right B A B, hAB, hBA]
    simp
  change (hsInner A A).re ≤ a*(hsInner (X-R X) (X-R X)).re at hdual
  change (hsInner B B).re ≤ a*(hsInner (R X) (R X)).re at hreverse
  rw [source_projection_pythagoras R hR hRR] at hdual
  rw [hsplit]
  nlinarith only [hdual, hreverse]

/-- A centered residual inequality in arbitrary injective complex trial
coordinates certifies the actual equal-rank spectral projection. -/
theorem source_centeredResidual_projection_certificate
    (L P : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hP : SourceSelfAdjoint P) (hPP : ∀ X, P (P X)=P X)
    (G : Operator D) (hPG : P G=0)
    (hker : ∀ Z, L Z=0 → ∃ a : ℂ, Z=a • G)
    {r : ℕ} (F : (Fin r → ℂ) →ₗ[ℂ] Operator D) (hF : Function.Injective F)
    (hspan : LinearMap.range F=LinearMap.range P)
    (S : Finset (Fin D × Fin D)) (hcount : S.card=r)
    {c ρ d : ℝ} (hρ : 0≤ρ) (hd : 0<d) (hsmall : ρ<d)
    (hsep : ∀ i, i ∉ S → sourceEigenvalues L hL i≠0 →
      d^2 ≤ (sourceEigenvalues L hL i-c)^2)
    (hres : ∀ v, (hsInner (L (F v)-(c:ℂ) • F v)
      (L (F v)-(c:ℂ) • F v)).re ≤ ρ^2*(hsInner (F v) (F v)).re)
    (X : Operator D) :
    (hsInner (P X-sourceSpectralCut L hL S X)
      (P X-sourceSpectralCut L hL S X)).re ≤
        (ρ/d)^2*(hsInner X X).re := by
  have hdimP : Module.finrank ℂ (LinearMap.range P)=r := by
    rw [← hspan, LinearMap.finrank_range_of_inj hF]
    simp
  have hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range (sourceSpectralCut L hL S)) := by
    rw [hdimP, sourceSpectralCut_finrank_range, hcount]
  have hratio0 : 0≤ρ/d := div_nonneg hρ hd.le
  have hratio1 : ρ/d<1 := (div_lt_one hd).mpr hsmall
  apply source_equalRank_projection_difference P (sourceSpectralCut L hL S)
    hP (sourceSpectralCut_selfAdjoint L hL S) hPP
    (sourceSpectralCut_idempotent L hL S) hdim (sq_nonneg _)
    (by nlinarith only [hratio0, hratio1]) _ X
  intro Y
  have hm : P Y ∈ LinearMap.range F := hspan.symm ▸ ⟨Y, rfl⟩
  obtain ⟨v, hv⟩ := hm
  have horth : hsInner G (P Y)=0 := by rw [← hP, hPG]; simp [hsInner]
  have hsq := sourceSpectralCut_centeredResidual_square_bound
    L hL S G hker hsep (P Y) horth
  have hr := hres v
  rw [hv] at hr
  have he : (ρ/d)^2=ρ^2/d^2 := div_pow ρ d 2
  rw [he, div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith only [hsq, hr]

/-- An actual projection-difference bound controls every compressed trace.
The observable contributes its actual projection rank through its trace. -/
theorem source_projection_difference_trace_bound
    (P R Q : Operator D →ₗ[ℂ] Operator D)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ X, Q (Q X)=Q X)
    {ε : ℝ} (hε : 0≤ε)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re ≤
      ε^2*(hsInner X X).re) :
    |sourceTrace (Q.comp P)-sourceTrace (Q.comp R)| ≤ ε*sourceTrace Q := by
  let M := P-R
  have hform (X : Operator D) :
      |(hsInner X (M X)).re|≤ε*(hsInner X X).re := by
    have hc := source_hsInner_cauchy_sq X (M X)
    have hb := mul_le_mul_of_nonneg_left (hclose X) (hsInner_self_nonneg X)
    change (hsInner X X).re*(hsInner (M X) (M X)).re ≤
      (hsInner X X).re*(ε^2*(hsInner X X).re) at hb
    have ht : 0≤ε*(hsInner X X).re := mul_nonneg hε (hsInner_self_nonneg X)
    rw [Complex.normSq_apply] at hc
    have hs : ((hsInner X (M X)).re)^2 ≤ (ε*(hsInner X X).re)^2 := by
      nlinarith [sq_nonneg (hsInner X (M X)).im]
    rw [abs_le]
    constructor <;> nlinarith
  have hq (X : Operator D) :
      hsInner X (Q X)=hsInner (Q X) (Q X) := by rw [hQ, hQQ]
  have hupper := sourceTrace_le (Q.comp (M.comp Q)) ((ε:ℂ) • Q) (fun X => by
    change (hsInner X (Q (M (Q X)))).re ≤ (hsInner X ((ε:ℂ) • Q X)).re
    rw [← hQ, hsInner_smul_right, ofReal_mul_re, hq]
    exact (abs_le.mp (hform (Q X))).2)
  have hlower := sourceTrace_le (((-ε:ℝ):ℂ) • Q) (Q.comp (M.comp Q)) (fun X => by
    change (hsInner X (((-ε:ℝ):ℂ) • Q X)).re ≤ (hsInner X (Q (M (Q X)))).re
    rw [hsInner_smul_right, ofReal_mul_re, hq X, ← hQ X (M (Q X))]
    simpa only [neg_mul] using (abs_le.mp (hform (Q X))).1)
  rw [sourceTrace_projection_compression Q M hQQ,
    sourceTrace_real_smul, show Q.comp M=Q.comp P-Q.comp R from
      by ext X; simp [M], sourceTrace_sub] at hupper hlower
  rw [abs_le]
  exact ⟨by simpa only [neg_mul] using hlower, hupper⟩


end Qatlib.Concepts.GibbsSource.SpectralGeom
