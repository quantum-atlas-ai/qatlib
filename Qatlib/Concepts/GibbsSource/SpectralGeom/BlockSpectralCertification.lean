/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Qatlib.Concepts.GibbsSource.SpectralGeom.BlockResidualLeakage
public import Qatlib.Concepts.GibbsSource.SpectralGeom.SourceNonzero

@[expose] public section


/-! Spectral certification from actual trial and complementary blocks.
The block assumptions imply full coercivity and the unique Gibbs line. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- A root-free two-block budget controls the actual mixed residual term. -/
theorem block_residual_young {a b η p q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hbudget : η^2 ≤ a*b) :
    2*η*Real.sqrt (p*q) ≤ a*p+b*q := by
  have hpq : 0 ≤ p*q := mul_nonneg hp hq
  have hs : (2*η*Real.sqrt (p*q))^2 ≤ (a*p+b*q)^2 := by
    calc
      _ = 4*η^2*(p*q) := by rw [mul_pow, mul_pow, Real.sq_sqrt hpq]; ring
      _ ≤ 4*(a*b)*(p*q) := by
        nlinarith only [mul_le_mul_of_nonneg_right hbudget hpq]
      _ ≤ _ := by nlinarith only [sq_nonneg (a*p-b*q)]
  have hleft : 0 ≤ 2*η*Real.sqrt (p*q) := by positivity
  have hright : 0 ≤ a*p+b*q := by positivity
  nlinarith only [hs, hleft, hright]

/-- Ritz and complementary floors plus the genuine whole-block residual imply
a lower form bound on the complete ground-orthogonal complex space. -/
theorem source_blockResidual_coercive
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D) (hPG : P G=0)
    {θ μ γ η : ℝ} (hθ : γ ≤ θ) (hμ : γ ≤ μ) (hη : 0 ≤ η)
    (hbudget : η^2 ≤ (θ-γ)*(μ-γ))
    (hritz : ∀ X, θ*(hsInner (P X) (P X)).re ≤
      (hsInner (P X) (L (P X))).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        η^2*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re)
    (X : Operator D) (hGX : hsInner G X=0) :
    γ*(hsInner X X).re ≤ (hsInner X (L X)).re := by
  let U := P X
  let Z := X-P X
  let R := L (P X)-P (L (P X))
  have hPZ : P Z=0 := by simp [Z, map_sub, hPP]
  have hGZ : hsInner G Z=0 := by
    dsimp only [Z]
    rw [hsInner_sub_right, ← hP, hPG, hGX]
    simp [hsInner]
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
    have haddl (A B C : Operator D) : hsInner (A+B) C=hsInner A C+hsInner B C := by
      simp [hsInner, add_mul, Matrix.trace_add]
    have haddr (A B C : Operator D) : hsInner A (B+C)=hsInner A B+hsInner A C := by
      simp [hsInner, mul_add, Matrix.trace_add]
    rw [map_add, haddl, haddr, haddr]
    simp only [Complex.add_re, hsym, hcross]
    ring
  have hu : 0 ≤ (hsInner U U).re := hsInner_self_nonneg U
  have hz : 0 ≤ (hsInner Z Z).re := hsInner_self_nonneg Z
  have hsqrt : Real.sqrt ((hsInner Z Z).re*(hsInner R R).re) ≤
      η*Real.sqrt ((hsInner Z Z).re*(hsInner U U).re) := by
    calc
      _ ≤ Real.sqrt (η^2*((hsInner Z Z).re*(hsInner U U).re)) := by
        apply Real.sqrt_le_sqrt
        have hr := mul_le_mul_of_nonneg_left (hres X) hz
        change (hsInner Z Z).re*(hsInner R R).re ≤
          (hsInner Z Z).re*(η^2*(hsInner U U).re) at hr
        nlinarith only [hr]
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη]
  have hr : -(η*Real.sqrt ((hsInner Z Z).re*(hsInner U U).re)) ≤
      (hsInner Z R).re := by
    have hc := hsInner_re_ge_neg_sqrt Z R
    linarith only [hc, hsqrt]
  have hy := block_residual_young (sub_nonneg.mpr hμ) (sub_nonneg.mpr hθ)
    hη hz hu (by nlinarith only [hbudget])
  have ht := hritz X
  have hc := hcomp Z hPZ hGZ
  have hnorm := source_projection_pythagoras P hP hPP X
  change (hsInner Z Z).re=(hsInner X X).re-(hsInner U U).re at hnorm
  change θ*(hsInner U U).re ≤ (hsInner U (L U)).re at ht
  have hnorm' : (hsInner X X).re=(hsInner U U).re+(hsInner Z Z).re := by
    linarith only [hnorm]
  rw [hsplit, hnorm']
  nlinarith only [ht, hc, hr, hy]

/-- Block ground centering for the stated finite source data. -/
private theorem block_ground_centering
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (G X : Operator D) (hG : (hsInner G G).re=1) (hLG : L G=0) :
    let Y := X-hsInner G X • G
    hsInner G Y=0 ∧
      (hsInner Y (L Y)).re=(hsInner X (L X)).re ∧
      hsVar G X ≤ (hsInner Y Y).re := by
  have hGG : hsInner G G=1 := by
    apply Complex.ext
    · simpa using hG
    · simpa using hsInner_self_re G
  have hGX : hsInner G (L X)=0 := by
    rw [← hL, hLG]
    simp [hsInner]
  dsimp only
  constructor
  · simp only [hsInner_sub_right, hsInner_smul_right, hGG, mul_one, sub_self]
  constructor
  · simp only [map_sub, map_smul, hLG, smul_zero, sub_zero,
      hsInner_sub_left, hsInner_smul_left, hGX, mul_zero, sub_zero]
  · exact hsInner_sub_normSq_ge X G (by linarith only [hG]) (hsInner G X)

/-- Full form coercivity is derived from independently checkable block data. -/
theorem source_blockResidual_formGap
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    {θ μ γ η : ℝ} (hγ : 0 ≤ γ) (hθ : γ ≤ θ) (hμ : γ ≤ μ) (hη : 0 ≤ η)
    (hbudget : η^2 ≤ (θ-γ)*(μ-γ))
    (hritz : ∀ X, θ*(hsInner (P X) (P X)).re ≤
      (hsInner (P X) (L (P X))).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        η^2*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    FormGapAtLeast (fun X => (hsInner X (L X)).re) G γ := by
  intro X
  obtain ⟨ho, he, hv⟩ := block_ground_centering L hL G X hG hLG
  have hc := source_blockResidual_coercive L P hL hP hPP G hPG
    hθ hμ hη hbudget hritz hres hcomp _ ho
  exact (mul_le_mul_of_nonneg_left hv hγ).trans (hc.trans_eq he)

/-- A positive block floor derives the complete scalar kernel. -/
theorem source_blockResidual_kernel
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    {θ μ γ η : ℝ} (hγ : 0 < γ) (hθ : γ ≤ θ) (hμ : γ ≤ μ) (hη : 0 ≤ η)
    (hbudget : η^2 ≤ (θ-γ)*(μ-γ))
    (hritz : ∀ X, θ*(hsInner (P X) (P X)).re ≤
      (hsInner (P X) (L (P X))).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        η^2*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) (X : Operator D) :
    L X=0 ↔ ∃ c : ℂ, X=c • G := by
  constructor
  · intro hLX
    let Y := X-hsInner G X • G
    obtain ⟨ho, he, _⟩ := block_ground_centering L hL G X hG hLG
    have hc := source_blockResidual_coercive L P hL hP hPP G hPG
      hθ hμ hη hbudget hritz hres hcomp Y ho
    rw [he, hLX] at hc
    simp only [hsInner, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re] at hc
    have hY : Y=0 := by
      by_contra hY
      have hp := hsInner_self_pos hY
      have hpos := mul_pos hγ hp
      exact (not_lt_of_ge hc) hpos
    refine ⟨hsInner G X, ?_⟩
    exact sub_eq_zero.mp hY
  · rintro ⟨c, rfl⟩
    simp [map_smul, hLG]


/-- A positive block certificate also establishes positivity of the full form
and the lower bound on the attained minimum positive spectrum. -/
theorem source_blockResidual_positiveGap
    (hD : 1 < D) (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    {θ μ γ η : ℝ} (hγ : 0 < γ) (hθ : γ ≤ θ) (hμ : γ ≤ μ) (hη : 0 ≤ η)
    (hbudget : η^2 ≤ (θ-γ)*(μ-γ))
    (hritz : ∀ X, θ*(hsInner (P X) (P X)).re ≤
      (hsInner (P X) (L (P X))).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        η^2*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (∀ X, 0 ≤ (hsInner X (L X)).re) ∧
      γ ≤ sourcePositiveGap L hL := by
  have hcoerc := source_blockResidual_coercive L P hL hP hPP G hPG
    hθ hμ hη hbudget hritz hres hcomp
  have hnonneg (X : Operator D) : 0 ≤ (hsInner X (L X)).re := by
    obtain ⟨ho, he, _⟩ := block_ground_centering L hL G X hG hLG
    have hc := hcoerc _ ho
    exact (mul_nonneg hγ.le (hsInner_self_nonneg _)).trans (hc.trans_eq he)
  refine ⟨hnonneg, ?_⟩
  have hker (X : Operator D) (hX : L X=0) : ∃ c : ℂ, X=c • G :=
    (source_blockResidual_kernel L P hL hP hPP G hG hLG hPG
      hγ hθ hμ hη hbudget hritz hres hcomp X).mp hX
  apply le_sourcePositiveGap L hL
    (sourcePositiveSpectrum_nonempty_of_nonneg_ne_zero L hL hnonneg
      (sourceMap_ne_zero_of_kernel_scalar_line hD L G hker))
  intro i hi
  have ho := hsInner_kernel_eigenvector_eq_zero L hL G _ hLG
    (Complex.ofReal_ne_zero.mpr hi.ne') (sourceEigenoperator_apply L hL i)
  have hc := hcoerc _ ho
  rw [sourceEigenoperator_apply, hsInner_smul_right, ofReal_mul_re,
    sourceEigenoperator_normSq, mul_one, mul_one] at hc
  exact hc

/-- The source trace agrees with the standard linear trace on the complete
complex matrix space. -/
theorem sourceTrace_eq_linearTrace (L : Operator D →ₗ[ℂ] Operator D) :
    sourceTrace L=(LinearMap.trace ℂ (Operator D) L).re := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin D) (Fin D))]
  apply congrArg (fun M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ => (Matrix.trace M).re)
  ext i j
  simp only [sourceSuperMatrix, LinearMap.toMatrix_apply]
  simp [Matrix.stdBasis]
  apply congrArg (fun A : Operator D => L A i.1 i.2)
  ext a b
  by_cases ha : a=j.1
  · subst a
    simp [matUnit_apply, Pi.single_apply]
  · simp [matUnit_apply, ha]

/-- The trace of an actual projection is the dimension of its range. -/
theorem sourceTrace_eq_finrank_range (P : Operator D →ₗ[ℂ] Operator D)
    (hPP : ∀ X, P (P X)=P X) :
    sourceTrace P=(Module.finrank ℂ (LinearMap.range P) : ℝ) := by
  have hp : LinearMap.IsProj (LinearMap.range P) P := by
    refine ⟨fun X => LinearMap.mem_range_self P X, ?_⟩
    rintro X ⟨Y, rfl⟩
    exact hPP Y
  rw [sourceTrace_eq_linearTrace, hp.trace]
  simp


/-- Source Spectral Cut finrank range for the stated finite source data. -/
theorem sourceSpectralCut_finrank_range
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D)) :
    Module.finrank ℂ (LinearMap.range (sourceSpectralCut L hL S))=S.card := by
  have h := sourceTrace_eq_finrank_range (sourceSpectralCut L hL S)
    (sourceSpectralCut_idempotent L hL S)
  rw [sourceTrace_spectralCut] at h
  exact_mod_cast h.symm

/-- Source Family Projection finrank range for the stated finite source data. -/
theorem sourceFamilyProjection_finrank_range {r : ℕ} (X : Fin r → Operator D)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0) :
    Module.finrank ℂ (LinearMap.range (sourceFamilyProjection X))=r := by
  have h := sourceTrace_eq_finrank_range (sourceFamilyProjection X)
    (sourceFamilyProjection_idempotent X horth)
  rw [sourceTrace_familyProjection X horth] at h
  exact_mod_cast h.symm

/-- A faithful restriction of one projection to the other's range bounds
the actual finite-dimensional range dimensions. -/
theorem source_projection_range_finrank_le
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hRR : ∀ X, R (R X)=R X)
    (hfaith : ∀ X, R X=X → P X=0 → X=0) :
    Module.finrank ℂ (LinearMap.range R) ≤
      Module.finrank ℂ (LinearMap.range P) := by
  let f : LinearMap.range R →ₗ[ℂ] LinearMap.range P :=
    P.rangeRestrict.comp (LinearMap.range R).subtype
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro X Y hXY
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hfix (Z : LinearMap.range R) : R (Z : Operator D)=(Z : Operator D) := by
    obtain ⟨W, hW⟩ := Z.property
    rw [← hW, hRR]
  apply hfaith
  · simp only [map_sub, hfix X, hfix Y]
  · have h := congrArg (fun Z : LinearMap.range P => (Z : Operator D)) hXY
    change P (X : Operator D)=P (Y : Operator D) at h
    rw [map_sub, h, sub_self]

/-- The actual positive spectral cut has the cutoff as its Ritz cap. -/
theorem sourcePositiveLowProjection_energy_le
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (t : ℝ) (X : Operator D) :
    (hsInner (sourcePositiveLowProjection L hL t X)
      (L (sourcePositiveLowProjection L hL t X))).re ≤
      t*(hsInner (sourcePositiveLowProjection L hL t X)
        (sourcePositiveLowProjection L hL t X)).re := by
  classical
  rw [source_energy_eq_sum_eigenvalues L hL, source_hsNormSq_eq_sum_coefficients L hL,
    Finset.mul_sum]
  simp only [sourcePositiveLowProjection, sourceSpectralCut_coefficient]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ sourcePositiveLowModes L hL t
  · rw [ite_eq_left hi]
    exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hi).2.2
      (Complex.normSq_nonneg _)
  · rw [ite_eq_right hi]
    simp

/-- The complement of the actual positive low cut has the cutoff as a form
floor after the unique ground line has been removed. -/
theorem sourcePositiveLowProjection_complement_floor
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (G : Operator D) (hE : ∀ X, 0 ≤ (hsInner X (L X)).re)
    (hker : ∀ X, L X=0 → ∃ c : ℂ, X=c • G)
    (t : ℝ) (X : Operator D) (hGX : hsInner G X=0)
    (hRX : sourcePositiveLowProjection L hL t X=0) :
    t*(hsInner X X).re ≤ (hsInner X (L X)).re := by
  classical
  rw [source_hsNormSq_eq_sum_coefficients L hL, source_energy_eq_sum_eigenvalues L hL,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 0 < sourceEigenvalues L hL i
  · by_cases hit : sourceEigenvalues L hL i ≤ t
    · have hmem : i ∈ sourcePositiveLowModes L hL t :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi, hit⟩
      have hc : hsInner (sourceEigenoperator L hL i)
          (sourcePositiveLowProjection L hL t X)=hsInner (sourceEigenoperator L hL i) X := by
        simp only [sourcePositiveLowProjection, sourceSpectralCut_coefficient, ite_eq_left hmem]
      rw [hRX] at hc
      have hz : hsInner (sourceEigenoperator L hL i) X=0 := by
        simpa [hsInner] using hc.symm
      simp [hz]
    · exact mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hit))
        (Complex.normSq_nonneg _)
  · have hi0 : sourceEigenvalues L hL i=0 :=
      le_antisymm (le_of_not_gt hi) (sourceEigenvalues_nonneg L hL hE i)
    have hzero : L (sourceEigenoperator L hL i)=0 := by
      rw [sourceEigenoperator_apply, hi0, Complex.ofReal_zero, zero_smul]
    obtain ⟨c, hc⟩ := hker _ hzero
    have hz : hsInner (sourceEigenoperator L hL i) X=0 := by
      rw [hc, hsInner_smul_left, hGX, mul_zero]
    simp [hz]

/-- Ritz upper bounds and complementary floors certify the count in an actual
spectral interval. Two faithful projection restrictions prove equal dimension. -/
theorem source_lowSpectral_count_of_blocks
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D) (hLG : L G=0) (hPG : P G=0)
    (hE : ∀ X, 0 ≤ (hsInner X (L X)).re)
    (hker : ∀ X, L X=0 → ∃ c : ℂ, X=c • G)
    {lam μ t : ℝ} (hlt : lam<t) (htμ : t<μ)
    (hritz : ∀ X, (hsInner (P X) (L (P X))).re ≤
      lam*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (sourcePositiveLowModes L hL t).card=Module.finrank ℂ (LinearMap.range P) := by
  let R := sourcePositiveLowProjection L hL t
  have hRR : ∀ X, R (R X)=R X := sourceSpectralCut_idempotent L hL _
  have hRP : Module.finrank ℂ (LinearMap.range R) ≤
      Module.finrank ℂ (LinearMap.range P) := by
    apply source_projection_range_finrank_le P R hRR
    intro X hRX hPX
    have ho : hsInner G X=0 := by
      rw [← hRX]
      exact sourcePositiveLowProjection_kernel_orthogonal L hL G hLG t X
    have hlow := sourcePositiveLowProjection_energy_le L hL t X
    change (hsInner (R X) (L (R X))).re ≤ t*(hsInner (R X) (R X)).re at hlow
    rw [hRX] at hlow
    have hc := hcomp X hPX ho
    by_contra hX
    have hp := mul_pos (sub_pos.mpr htμ) (hsInner_self_pos hX)
    nlinarith only [hlow, hc, hp]
  have hPR : Module.finrank ℂ (LinearMap.range P) ≤
      Module.finrank ℂ (LinearMap.range R) := by
    apply source_projection_range_finrank_le R P hPP
    intro X hPX hRX
    have ho : hsInner G X=0 := by
      rw [← hPX, ← hP, hPG]
      simp [hsInner]
    have hh := sourcePositiveLowProjection_complement_floor L hL G hE hker t X ho hRX
    have ht := hritz X
    rw [hPX] at ht
    by_contra hX
    have hp := mul_pos (sub_pos.mpr hlt) (hsInner_self_pos hX)
    nlinarith only [hh, ht, hp]
  have hd := le_antisymm hRP hPR
  exact (sourceSpectralCut_finrank_range L hL _).symm.trans hd

/-- The actual off-diagonal certificate derives the kernel assumptions needed
by the count theorem, giving a low count without a supplied kernel or rank. -/
theorem source_blockResidual_lowSpectral_count
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) (G : Operator D)
    (hG : (hsInner G G).re=1) (hLG : L G=0) (hPG : P G=0)
    {θ lam μ γ η t : ℝ} (hγ : 0 < γ)
    (hθ : γ ≤ θ) (hμ : γ ≤ μ) (hη : 0 ≤ η)
    (hbudget : η^2 ≤ (θ-γ)*(μ-γ)) (hlt : lam<t) (htμ : t<μ)
    (hritzLower : ∀ X, θ*(hsInner (P X) (P X)).re ≤
      (hsInner (P X) (L (P X))).re)
    (hritzUpper : ∀ X, (hsInner (P X) (L (P X))).re ≤
      lam*(hsInner (P X) (P X)).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re ≤
        η^2*(hsInner (P X) (P X)).re)
    (hcomp : ∀ Y, P Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (sourcePositiveLowModes L hL t).card=Module.finrank ℂ (LinearMap.range P) := by
  have hcoerc := source_blockResidual_coercive L P hL hP hPP G hPG
    hθ hμ hη hbudget hritzLower hres hcomp
  have hE (X : Operator D) : 0 ≤ (hsInner X (L X)).re := by
    obtain ⟨ho, he, _⟩ := block_ground_centering L hL G X hG hLG
    exact (mul_nonneg hγ.le (hsInner_self_nonneg _)).trans ((hcoerc _ ho).trans_eq he)
  have hker (X : Operator D) (hX : L X=0) : ∃ c : ℂ, X=c • G :=
    (source_blockResidual_kernel L P hL hP hPP G hG hLG hPG
      hγ hθ hμ hη hbudget hritzLower hres hcomp X).mp hX
  exact source_lowSpectral_count_of_blocks L P hL hP hPP G hLG hPG
    hE hker hlt htμ hritzUpper hcomp


/-- Positivity of the full lifted form certifies the ground-orthogonal
complementary block floor. -/
theorem source_complement_floor_of_lift
    (L P : Operator D →ₗ[ℂ] Operator D) (G : Operator D) (μ ζ : ℝ)
    (hlift : ∀ X, 0 ≤
      (hsInner X (L X-(μ:ℂ) • X+((μ+1:ℝ):ℂ) • sourceRankOne G X+
        (ζ:ℂ) • P X)).re) (X : Operator D)
    (hPX : P X=0) (hGX : hsInner G X=0) :
    μ*(hsInner X X).re ≤ (hsInner X (L X)).re := by
  have hr : sourceRankOne G X=0 := by
    change hsInner G X • G = 0
    rw [hGX, zero_smul]
  have h := hlift X
  simp only [hPX, hr, smul_zero, add_zero, hsInner_sub_right,
    hsInner_smul_right, Complex.sub_re, ofReal_mul_re] at h
  linarith only [h]

/-- An orthonormal trial family provides its dimension internally. The block
data certify the kernel, a full form gap, an actual gap and the exact low count. -/
theorem source_blockResidual_family_certificate {r : ℕ}
    (hD : 1 < D) (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (G : Operator D) (hG : (hsInner G G).re=1) (hLG : L G=0)
    (X : Fin r → Operator D)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0)
    (hGX : ∀ i, hsInner G (X i)=0)
    {θ lam μ γ η t : ℝ} (hγ : 0 < γ)
    (hθ : γ ≤ θ) (hμ : γ ≤ μ) (hη : 0 ≤ η)
    (hbudget : η^2 ≤ (θ-γ)*(μ-γ)) (hlt : lam<t) (htμ : t<μ)
    (hritzLower : ∀ Y, θ*(hsInner (sourceFamilyProjection X Y)
      (sourceFamilyProjection X Y)).re ≤
        (hsInner (sourceFamilyProjection X Y) (L (sourceFamilyProjection X Y))).re)
    (hritzUpper : ∀ Y,
      (hsInner (sourceFamilyProjection X Y) (L (sourceFamilyProjection X Y))).re ≤
        lam*(hsInner (sourceFamilyProjection X Y) (sourceFamilyProjection X Y)).re)
    (hres : ∀ Y,
      (hsInner (L (sourceFamilyProjection X Y)-sourceFamilyProjection X (L (sourceFamilyProjection X Y)))
        (L (sourceFamilyProjection X Y)-sourceFamilyProjection X (L (sourceFamilyProjection X Y)))).re ≤
        η^2*(hsInner (sourceFamilyProjection X Y) (sourceFamilyProjection X Y)).re)
    (hcomp : ∀ Y, sourceFamilyProjection X Y=0 → hsInner G Y=0 →
      μ*(hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    (∀ Y, L Y=0 ↔ ∃ c : ℂ, Y=c • G) ∧
      FormGapAtLeast (fun Y => (hsInner Y (L Y)).re) G γ ∧
      γ ≤ sourcePositiveGap L hL ∧
      (sourcePositiveLowModes L hL t).card=r := by
  have hP := sourceFamilyProjection_selfAdjoint X
  have hPP := sourceFamilyProjection_idempotent X horth
  have hPG := sourceFamilyProjection_kernel X G hGX
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact source_blockResidual_kernel L (sourceFamilyProjection X) hL hP hPP G hG hLG hPG
      hγ hθ hμ hη hbudget hritzLower hres hcomp
  · exact source_blockResidual_formGap L (sourceFamilyProjection X) hL hP hPP G hG hLG hPG
      hγ.le hθ hμ hη hbudget hritzLower hres hcomp
  · exact (source_blockResidual_positiveGap hD L (sourceFamilyProjection X) hL hP hPP
      G hG hLG hPG hγ hθ hμ hη hbudget hritzLower hres hcomp).2
  · have h := source_blockResidual_lowSpectral_count L (sourceFamilyProjection X)
      hL hP hPP G hG hLG hPG hγ hθ hμ hη hbudget hlt htμ
      hritzLower hritzUpper hres hcomp
    simpa only [sourceFamilyProjection_finrank_range X horth] using h


/-- The root-free budget for the explicit six-mode physical certificate is
checked over exact rationals and is homogeneous in the physical factor. -/
theorem block_sixMode_rootfree_budget {s : ℝ} (hs : 0 < s) :
    0 < ((295355695829:ℝ)/10^11)*s ∧
    ((295355695829:ℝ)/10^11)*s ≤ ((29535569582984:ℝ)/10^13)*s ∧
    ((295355695829:ℝ)/10^11)*s ≤ ((51:ℝ)/10)*s ∧
    0 ≤ ((4:ℝ)/10^6)*s ∧
    (((4:ℝ)/10^6)*s)^2 ≤
      (((29535569582984:ℝ)/10^13)*s-((295355695829:ℝ)/10^11)*s)*
      (((51:ℝ)/10)*s-((295355695829:ℝ)/10^11)*s) := by
  refine ⟨by positivity, ?_, ?_, by positivity, ?_⟩
  · nlinarith only [hs]
  · nlinarith only [hs]
  · nlinarith only [sq_nonneg s]

end Qatlib.Concepts.GibbsSource.SpectralGeom
