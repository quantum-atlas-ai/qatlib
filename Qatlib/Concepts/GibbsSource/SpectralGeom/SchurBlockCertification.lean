/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.BlockSpectralCertification

@[expose] public section


/-! An anisotropic Schur certificate retains the complete residual Gram form.
The lower pencil is tested on the actual trial space, including arbitrary
full-rank nonorthogonal coordinates. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- Schur hs Inner add left for the stated finite source data. -/
private theorem schur_hsInner_add_left (A B C : Operator D) :
    hsInner (A+B) C=hsInner A C+hsInner B C := by
  simp [hsInner, add_mul, Matrix.trace_add]

/-- Schur hs Inner add right for the stated finite source data. -/
private theorem schur_hsInner_add_right (A B C : Operator D) :
    hsInner A (B+C)=hsInner A B+hsInner A C := by
  simp [hsInner, mul_add, Matrix.trace_add]

/-- Completing the actual residual square keeps all correlations between
trial directions. The identity holds before any spectral assumptions. -/
theorem source_schurResidual_square
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (μ γ : ℝ) (X : Operator D) :
    let U := P X
    let Z := X-P X
    let R := L (P X)-P (L (P X))
    (μ-γ)*((hsInner X (L X)).re-γ*(hsInner X X).re) =
      (μ-γ)*((hsInner U (L U)).re-γ*(hsInner U U).re)-
        (hsInner R R).re+
      (hsInner (((μ-γ:ℝ):ℂ) • Z+R) (((μ-γ:ℝ):ℂ) • Z+R)).re+
      (μ-γ)*((hsInner Z (L Z)).re-μ*(hsInner Z Z).re) := by
  let U := P X
  let Z := X-P X
  let R := L (P X)-P (L (P X))
  have hPZ : P Z=0 := by simp [Z, map_sub, hPP]
  have hcross : (hsInner Z R).re=(hsInner Z (L U)).re := by
    dsimp only [R, U]
    rw [hsInner_sub_right, ← hP, hPZ]
    simp [hsInner]
  have hsym : (hsInner U (L Z)).re=(hsInner Z (L U)).re := by
    rw [← hL, hsInner_conj_swap]
    simp
  have hsplit : (hsInner X (L X)).re=
      (hsInner U (L U)).re+(hsInner Z (L Z)).re+2*(hsInner Z R).re := by
    conv_lhs => rw [show X=U+Z by dsimp [U, Z]; abel]
    rw [map_add, schur_hsInner_add_left, schur_hsInner_add_right,
      schur_hsInner_add_right]
    simp only [Complex.add_re, hsym, hcross]
    ring
  have hnorm := source_projection_pythagoras P hP hPP X
  change (hsInner Z Z).re=(hsInner X X).re-(hsInner U U).re at hnorm
  have hnorm' : (hsInner X X).re=(hsInner U U).re+(hsInner Z Z).re := by
    linarith only [hnorm]
  have hswap : (hsInner R Z).re=(hsInner Z R).re := by
    rw [hsInner_conj_swap]
    rfl
  have hsquare :
      (hsInner (((μ-γ:ℝ):ℂ) • Z+R) (((μ-γ:ℝ):ℂ) • Z+R)).re =
        (μ-γ)^2*(hsInner Z Z).re+2*(μ-γ)*(hsInner Z R).re+(hsInner R R).re := by
    rw [schur_hsInner_add_left, schur_hsInner_add_right, schur_hsInner_add_right]
    simp only [hsInner_smul_left, hsInner_smul_right, Complex.star_def,
      Complex.conj_ofReal, Complex.add_re, ofReal_mul_re]
    rw [hswap]
    ring
  change (μ-γ)*((hsInner X (L X)).re-γ*(hsInner X X).re) =
    (μ-γ)*((hsInner U (L U)).re-γ*(hsInner U U).re)-
      (hsInner R R).re+
    (hsInner (((μ-γ:ℝ):ℂ) • Z+R) (((μ-γ:ℝ):ℂ) • Z+R)).re+
    (μ-γ)*((hsInner Z (L Z)).re-μ*(hsInner Z Z).re)
  rw [hsplit, hnorm', hsquare]
  ring

/-- The full lower Schur pencil gives a ground-orthogonal form floor using
the complete residual quadratic form. -/
theorem source_schurResidual_coercive
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D) (hPG : P G=0)
    {μ γ : ℝ} (hγμ : γ<μ)
    (hschur : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        (μ-γ)*((hsInner (P X) (L (P X))).re-γ*(hsInner (P X) (P X)).re))
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re)
    (X : Operator D) (hGX : hsInner G X=0) :
    γ*(hsInner X X).re ≤ (hsInner X (L X)).re := by
  let Z := X-P X
  let R := L (P X)-P (L (P X))
  have hPZ : P Z=0 := by simp [Z, map_sub, hPP]
  have hGZ : hsInner G Z=0 := by
    dsimp only [Z]
    rw [hsInner_sub_right, ← hP, hPG, hGX]
    simp [hsInner]
  have hc := hcomp Z hPZ hGZ
  have hs := hsInner_self_nonneg (((μ-γ:ℝ):ℂ) • Z+R)
  have hid := source_schurResidual_square L P hL hP hPP μ γ X
  dsimp only at hid
  have hnonneg : 0 ≤
      (μ-γ)*((hsInner X (L X)).re-γ*(hsInner X X).re) := by
    rw [hid]
    exact add_nonneg
      (add_nonneg (sub_nonneg.mpr (hschur X)) hs)
      (mul_nonneg (sub_pos.mpr hγμ).le (sub_nonneg.mpr hc))
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sub_pos.mpr hγμ)).mp hnonneg)


/-- Strict positivity of the lower pencil excludes the threshold from the
entire ground-orthogonal spectrum. -/
theorem source_schurResidual_strict_coercive
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D) (hPG : P G=0)
    {μ γ : ℝ} (hγμ : γ<μ)
    (hschur : ∀ X, P X≠0 →
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re <
        (μ-γ)*((hsInner (P X) (L (P X))).re-γ*(hsInner (P X) (P X)).re))
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re)
    (X : Operator D) (hGX : hsInner G X=0) (hX : X≠0) :
    γ*(hsInner X X).re < (hsInner X (L X)).re := by
  by_cases hPX : P X=0
  · have hc := hcomp X hPX hGX
    have hp := mul_pos (sub_pos.mpr hγμ) (hsInner_self_pos hX)
    nlinarith only [hc, hp]
  let Z := X-P X
  let R := L (P X)-P (L (P X))
  have hPZ : P Z=0 := by simp [Z, map_sub, hPP]
  have hGZ : hsInner G Z=0 := by
    dsimp only [Z]
    rw [hsInner_sub_right, ← hP, hPG, hGX]
    simp [hsInner]
  have hc := hcomp Z hPZ hGZ
  have hs := hsInner_self_nonneg (((μ-γ:ℝ):ℂ) • Z+R)
  have hid := source_schurResidual_square L P hL hP hPP μ γ X
  dsimp only at hid
  have hpos : 0 <
      (μ-γ)*((hsInner X (L X)).re-γ*(hsInner X X).re) := by
    rw [hid]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (sub_pos.mpr (hschur X hPX)) hs)
      (mul_nonneg (sub_pos.mpr hγμ).le (sub_nonneg.mpr hc))
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (sub_pos.mpr hγμ)).mp hpos)

/-- Matrix-residual data imply the unique ground line, a full form gap, the
attained positive gap and an exact positive low count. -/
theorem source_schurResidual_certificate
    (hD : 1 < D) (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    {lam μ γ t : ℝ} (hγ : 0<γ) (hγμ : γ<μ) (hlt : lam<t) (htμ : t<μ)
    (hschur : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        (μ-γ)*((hsInner (P X) (L (P X))).re-γ*(hsInner (P X) (P X)).re))
    (hritzUpper : ∀ X, (hsInner (P X) (L (P X))).re ≤
      lam*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (∀ X, L X=0 ↔ ∃ c : ℂ, X=c • G) ∧
      FormGapAtLeast (fun X => (hsInner X (L X)).re) G γ ∧
      γ ≤ sourcePositiveGap L hL ∧
      (sourcePositiveLowModes L hL t).card=Module.finrank ℂ (LinearMap.range P) := by
  have hcoerc := source_schurResidual_coercive L P hL hP hPP G hPG
    hγμ hschur hcomp
  let P0 : Operator D →ₗ[ℂ] Operator D := 0
  have hzero : SourceSelfAdjoint P0 := by
    intro X Y
    simp [P0, hsInner]
  have hritz0 (X : Operator D) :
      γ*(hsInner (P0 X) (P0 X)).re ≤ (hsInner (P0 X) (L (P0 X))).re := by
    simp [P0, hsInner]
  have hres0 (X : Operator D) :
      (hsInner (L (P0 X)-P0 (L (P0 X))) (L (P0 X)-P0 (L (P0 X)))).re ≤
        (0:ℝ)^2*(hsInner (P0 X) (P0 X)).re := by
    simp [P0, hsInner]
  have hc0 (Y : Operator D) (_ : P0 Y=0) (hGY : hsInner G Y=0) :
      γ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re := hcoerc Y hGY
  have hker := source_blockResidual_kernel L P0 hL hzero (by simp [P0]) G hG hLG
    (by simp [P0]) hγ le_rfl le_rfl le_rfl (by simp) hritz0 hres0 hc0
  have hform := source_blockResidual_formGap L P0 hL hzero (by simp [P0]) G hG hLG
    (by simp [P0]) hγ.le le_rfl le_rfl le_rfl (by simp) hritz0 hres0 hc0
  have hgap := source_blockResidual_positiveGap hD L P0 hL hzero (by simp [P0]) G hG hLG
    (by simp [P0]) hγ le_rfl le_rfl le_rfl (by simp) hritz0 hres0 hc0
  refine ⟨hker, hform, hgap.2, ?_⟩
  exact source_lowSpectral_count_of_blocks L P hL hP hPP G hLG hPG hgap.1
    (fun X hX => (hker X).mp hX) hlt htμ hritzUpper hcomp

/-- Arbitrary full-rank trial coordinates consume their actual Gram forms.
The norms and energies retain the actual coordinate Gram form. -/
theorem source_schurResidual_coordinate_certificate {r : ℕ}
    (hD : 1 < D) (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    (F : (Fin r → ℂ) →ₗ[ℂ] Operator D)
    (hF : Function.Injective F) (hspan : LinearMap.range F=LinearMap.range P)
    {lam μ γ t : ℝ} (hγ : 0<γ) (hγμ : γ<μ) (hlt : lam<t) (htμ : t<μ)
    (hschur : ∀ v,
      (hsInner (L (F v)-P (L (F v))) (L (F v)-P (L (F v)))).re ≤
        (μ-γ)*((hsInner (F v) (L (F v))).re-γ*(hsInner (F v) (F v)).re))
    (hritzUpper : ∀ v, (hsInner (F v) (L (F v))).re ≤
      lam*(hsInner (F v) (F v)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (∀ X, L X=0 ↔ ∃ c : ℂ, X=c • G) ∧
      FormGapAtLeast (fun X => (hsInner X (L X)).re) G γ ∧
      γ ≤ sourcePositiveGap L hL ∧
      (sourcePositiveLowModes L hL t).card=r := by
  have hcover (X : Operator D) : ∃ v, F v=P X := by
    have hmem : P X ∈ LinearMap.range F := by
      rw [hspan]
      exact ⟨X, rfl⟩
    exact hmem
  have hs (X : Operator D) :
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        (μ-γ)*((hsInner (P X) (L (P X))).re-γ*(hsInner (P X) (P X)).re) := by
    obtain ⟨v, hv⟩ := hcover X
    simpa only [hv] using hschur v
  have hu (X : Operator D) : (hsInner (P X) (L (P X))).re ≤
      lam*(hsInner (P X) (P X)).re := by
    obtain ⟨v, hv⟩ := hcover X
    simpa only [hv] using hritzUpper v
  have hdim : Module.finrank ℂ (LinearMap.range P)=r := by
    rw [← hspan, LinearMap.finrank_range_of_inj hF]
    simp
  have h := source_schurResidual_certificate hD L P hL hP hPP G hG hLG hPG
    hγ hγμ hlt htμ hs hu hcomp
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hdim⟩



/-- A strictly positive matrix pencil gives a strict actual-gap bound.
Its proof uses the attained positive spectrum and the original residual. -/
theorem source_schurResidual_strict_coordinate_certificate {r : ℕ}
    (hD : 1 < D) (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    (F : (Fin r → ℂ) →ₗ[ℂ] Operator D)
    (hF : Function.Injective F) (hspan : LinearMap.range F=LinearMap.range P)
    {lam μ γ t : ℝ} (hγ : 0<γ) (hγμ : γ<μ) (hlt : lam<t) (htμ : t<μ)
    (hschur : ∀ v, v≠0 →
      (hsInner (L (F v)-P (L (F v))) (L (F v)-P (L (F v)))).re <
        (μ-γ)*((hsInner (F v) (L (F v))).re-γ*(hsInner (F v) (F v)).re))
    (hritzUpper : ∀ v, (hsInner (F v) (L (F v))).re ≤
      lam*(hsInner (F v) (F v)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (∀ X, L X=0 ↔ ∃ c : ℂ, X=c • G) ∧
      FormGapAtLeast (fun X => (hsInner X (L X)).re) G γ ∧
      γ < sourcePositiveGap L hL ∧
      (sourcePositiveLowModes L hL t).card=r := by
  have hweak (v : Fin r → ℂ) :
      (hsInner (L (F v)-P (L (F v))) (L (F v)-P (L (F v)))).re ≤
        (μ-γ)*((hsInner (F v) (L (F v))).re-γ*(hsInner (F v) (F v)).re) := by
    by_cases hv : v=0
    · subst v
      simp [hsInner]
    · exact (hschur v hv).le
  have h := source_schurResidual_coordinate_certificate hD L P hL hP hPP G
    hG hLG hPG F hF hspan hγ hγμ hlt htμ hweak hritzUpper hcomp
  have hp : 0 < sourcePositiveGap L hL := hγ.trans_le h.2.2.1
  obtain ⟨i, hi, he⟩ := sourcePositiveGap_attained L hL
    ((sourcePositiveGap_pos_iff L hL).mp hp)
  have hs (X : Operator D) (hPX : P X≠0) :
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re <
        (μ-γ)*((hsInner (P X) (L (P X))).re-γ*(hsInner (P X) (P X)).re) := by
    have hmem : P X ∈ LinearMap.range F := by
      rw [hspan]
      exact ⟨X, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    have hv0 : v≠0 := by
      intro hz
      rw [hz, map_zero] at hv
      exact hPX hv.symm
    simpa only [hv] using hschur v hv0
  have ho := hsInner_kernel_eigenvector_eq_zero L hL G _ hLG
    (Complex.ofReal_ne_zero.mpr hi.ne') (sourceEigenoperator_apply L hL i)
  have hg := source_schurResidual_strict_coercive L P hL hP hPP G hPG hγμ hs hcomp
    (sourceEigenoperator L hL i) ho (sourceEigenoperator_ne_zero L hL i)
  rw [sourceEigenoperator_apply, hsInner_smul_right, ofReal_mul_re,
    sourceEigenoperator_normSq, mul_one, mul_one] at hg
  exact ⟨h.1, h.2.1, hg.trans_eq he, h.2.2.2⟩


end Qatlib.Concepts.GibbsSource.SpectralGeom
