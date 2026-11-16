/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.CenteredResidualProjection

@[expose] public section


/-! Rank-sensitive transport of observable traces across actual spectral projections.
The positive and negative spectral counts retain the trial-space rank. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom

variable {D : ℕ}

/-- Rank Trace sub self Adjoint for the stated finite source data. -/
private theorem rankTrace_sub_selfAdjoint
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R) :
    SourceSelfAdjoint (P-R) := by
  intro X Y
  simp only [LinearMap.sub_apply, hsInner_sub_left, hsInner_sub_right]
  exact congrArg₂ (·-·) (hP X Y) (hR X Y)

/-- Every nonzero vector of a positive spectral cut has positive actual energy. -/
theorem source_positiveSpectralCut_energy_pos
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (S : Finset (Fin D × Fin D))
    (hS : ∀ i ∈ S, 0<sourceEigenvalues L hL i)
    (X : Operator D) (hSX : sourceSpectralCut L hL S X=X) (hX : X≠0) :
    0<(hsInner X (L X)).re := by
  classical
  have hz (i : Fin D × Fin D) (hi : i∉S) :
      hsInner (sourceEigenoperator L hL i) X=0 := by
    have h := congrArg (fun Y => hsInner (sourceEigenoperator L hL i) Y) hSX
    change hsInner (sourceEigenoperator L hL i) (sourceSpectralCut L hL S X)=
      hsInner (sourceEigenoperator L hL i) X at h
    rw [sourceSpectralCut_coefficient, ite_eq_right hi] at h
    exact h.symm
  have hnorm := hsInner_self_pos hX
  rw [source_hsNormSq_eq_sum_coefficients L hL] at hnorm
  obtain ⟨i, hi, hci⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => Complex.normSq_nonneg
      (hsInner (sourceEigenoperator L hL j) X))).mp hnorm
  have hiS : i∈S := by
    by_contra h
    rw [hz i h, Complex.normSq_zero] at hci
    exact (lt_irrefl 0) hci
  rw [source_energy_eq_sum_eigenvalues L hL]
  apply (Finset.sum_pos_iff_of_nonneg ?_).mpr
  · exact ⟨i, hi, mul_pos (hS i hiS) hci⟩
  · intro j _
    by_cases hj : j∈S
    · exact mul_nonneg (hS j hj).le (Complex.normSq_nonneg _)
    · rw [hz j hj, Complex.normSq_zero, mul_zero]

/-- A positive spectral cut of a difference injects into the first range
when the second operator has a nonnegative form. -/
theorem source_positiveSpectralCut_rank_le
    (P R : Operator D →ₗ[ℂ] Operator D)
    (hM : SourceSelfAdjoint (P-R))
    (hRpos : ∀ X, 0≤(hsInner X (R X)).re)
    (S : Finset (Fin D × Fin D))
    (hS : ∀ i ∈ S, 0<sourceEigenvalues (P-R) hM i) :
    S.card≤Module.finrank ℂ (LinearMap.range P) := by
  have h := source_projection_range_finrank_le P (sourceSpectralCut (P-R) hM S)
    (sourceSpectralCut_idempotent (P-R) hM S) (fun X hSX hPX => by
      by_contra hX
      have hp := source_positiveSpectralCut_energy_pos (P-R) hM S hS X hSX hX
      change 0<(hsInner X (P X-R X)).re at hp
      rw [hPX, zero_sub] at hp
      have hn := hRpos X
      change 0≤(Xᴴ * R X).trace.re at hn
      simp only [hsInner, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re] at hp
      linarith)
  simpa only [sourceSpectralCut_finrank_range] using h

/-- A full Hilbert--Schmidt norm bound controls every actual source eigenvalue. -/
theorem source_eigenvalues_abs_le_of_norm_bound
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    {ε : ℝ} (hε : 0≤ε)
    (hbound : ∀ X, (hsInner (L X) (L X)).re≤ε^2*(hsInner X X).re)
    (i : Fin D × Fin D) :
    |sourceEigenvalues L hL i|≤ε := by
  have h := hbound (sourceEigenoperator L hL i)
  simp only [sourceEigenoperator_apply, hsInner_smul_left, hsInner_smul_right,
    sourceEigenoperator_inner, ite_true, star_ofReal, mul_one,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.one_re] at h
  rw [abs_le]
  constructor <;> nlinarith

/-- An effect with form cap w measures at most w times the positive spectral
mass of a projection difference, retaining the first projection's rank. -/
theorem source_effect_trace_difference_upper
    (P R A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hRR : ∀ X, R (R X)=R X)
    {ε w : ℝ} (hε : 0≤ε) (hw : 0≤w)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤
      ε^2*(hsInner X X).re)
    (hApos : ∀ X, 0≤(hsInner X (A X)).re)
    (hAcap : ∀ X, (hsInner X (A X)).re≤w*(hsInner X X).re) :
    sourceTrace (A.comp P)-sourceTrace (A.comp R)≤
      w*ε*(Module.finrank ℂ (LinearMap.range P) : ℝ) := by
  classical
  let M := P-R
  have hM : SourceSelfAdjoint M := rankTrace_sub_selfAdjoint P R hP hR
  let S := Finset.univ.filter (fun i => 0<sourceEigenvalues M hM i)
  have hcount : S.card≤Module.finrank ℂ (LinearMap.range P) := by
    apply source_positiveSpectralCut_rank_le P R hM
    · intro X
      have he : hsInner X (R X)=hsInner (R X) (R X) := by rw [hR, hRR]
      rw [he]
      exact hsInner_self_nonneg _
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hspec (i : Fin D × Fin D) : |sourceEigenvalues M hM i|≤ε :=
    source_eigenvalues_abs_le_of_norm_bound M hM hε hclose i
  have ht : sourceTrace (A.comp P)-sourceTrace (A.comp R)=
      ∑ i, sourceEigenvalues M hM i *
        (hsInner (sourceEigenoperator M hM i) (A (sourceEigenoperator M hM i))).re := by
    rw [← sourceTrace_sub, ← LinearMap.comp_sub,
      sourceTrace_eq_sum_eigenoperators M _ hM]
    apply Finset.sum_congr rfl
    intro i _
    change (hsInner (sourceEigenoperator M hM i)
      (A (M (sourceEigenoperator M hM i)))).re=_
    rw [sourceEigenoperator_apply, map_smul, hsInner_smul_right, ofReal_mul_re]
  rw [ht]
  have hb :
      (∑ i, sourceEigenvalues M hM i *
        (hsInner (sourceEigenoperator M hM i) (A (sourceEigenoperator M hM i))).re)
      ≤∑ i, if 0<sourceEigenvalues M hM i then w*ε else 0 := by
    apply Finset.sum_le_sum
    intro i _
    have ha := hApos (sourceEigenoperator M hM i)
    have hc := hAcap (sourceEigenoperator M hM i)
    rw [sourceEigenoperator_normSq, mul_one] at hc
    by_cases hi : 0<sourceEigenvalues M hM i
    · rw [ite_eq_left hi]
      have hm := mul_le_mul_of_nonneg_left hc hi.le
      have he := mul_le_mul_of_nonneg_right (le_abs_self _ |>.trans (hspec i)) hw
      nlinarith only [hm, he]
    · rw [ite_eq_right hi]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) ha
  have hs : (∑ i, if 0<sourceEigenvalues M hM i then w*ε else 0)=
      w*ε*(S.card:ℝ) := by
    rw [← Finset.sum_filter]
    simp [S, mul_comm]
  rw [hs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount)
    (mul_nonneg hw hε))

/-- Equal actual projection ranks give a sharp effect-trace error bound. -/
theorem source_equalRank_effect_trace_bound
    (P R A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range R))
    {ε w : ℝ} (hε : 0≤ε) (hw : 0≤w)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤
      ε^2*(hsInner X X).re)
    (hApos : ∀ X, 0≤(hsInner X (A X)).re)
    (hAcap : ∀ X, (hsInner X (A X)).re≤w*(hsInner X X).re) :
    |sourceTrace (A.comp P)-sourceTrace (A.comp R)|≤
      w*ε*(Module.finrank ℂ (LinearMap.range P) : ℝ) := by
  have hu := source_effect_trace_difference_upper P R A hP hR hRR hε hw
    hclose hApos hAcap
  have hl := source_effect_trace_difference_upper R P A hR hP hPP hε hw
    (fun X => by
      have h := hclose X
      have he : R X-P X=-(P X-R X) := by abel
      simpa only [he, hsInner, Matrix.conjTranspose_neg, neg_mul_neg] using h)
    hApos hAcap
  rw [← hdim] at hl
  rw [abs_le]
  exact ⟨by linarith, hu⟩

/-- Scalar shifts cancel at equal rank, so only the observable's form width
enters the trace-transport cost. -/
theorem source_equalRank_observable_trace_bound
    (P R A : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range R))
    {ε a b : ℝ} (hε : 0≤ε) (hab : a≤b)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤
      ε^2*(hsInner X X).re)
    (hAlower : ∀ X, a*(hsInner X X).re≤(hsInner X (A X)).re)
    (hAupper : ∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re) :
    |sourceTrace (A.comp P)-sourceTrace (A.comp R)|≤
      (b-a)*ε*(Module.finrank ℂ (LinearMap.range P) : ℝ) := by
  let A₀ := A-(a:ℂ) • LinearMap.id
  have he (X : Operator D) :
      (hsInner X (A₀ X)).re=(hsInner X (A X)).re-a*(hsInner X X).re := by
    change (hsInner X (A X-(a:ℂ) • X)).re=_
    rw [hsInner_sub_right, Complex.sub_re, hsInner_smul_right, ofReal_mul_re]
  have h := source_equalRank_effect_trace_bound P R A₀ hP hR hPP hRR hdim
    hε (sub_nonneg.mpr hab) hclose
    (fun X => by rw [he]; linarith [hAlower X])
    (fun X => by rw [he]; nlinarith only [hAupper X])
  have htrace : sourceTrace P=sourceTrace R := by
    rw [sourceTrace_eq_finrank_range P hPP, sourceTrace_eq_finrank_range R hRR, hdim]
  have ht (Q : Operator D →ₗ[ℂ] Operator D) :
      sourceTrace (A₀.comp Q)=sourceTrace (A.comp Q)-a*sourceTrace Q := by
    rw [show A₀=A-(a:ℂ) • LinearMap.id from rfl, LinearMap.sub_comp,
      LinearMap.smul_comp, LinearMap.id_comp, sourceTrace_sub, sourceTrace_real_smul]
  rw [ht P, ht R, htrace] at h
  simpa only [sub_sub_sub_cancel_right] using h


/-- Two projection ranks and the observable projection rank give the smaller
of the cluster and observation-space trace budgets. -/
theorem source_equalRank_projection_trace_bound
    (P R Q : Operator D →ₗ[ℂ] Operator D)
    (hP : SourceSelfAdjoint P) (hR : SourceSelfAdjoint R)
    (hQ : SourceSelfAdjoint Q)
    (hPP : ∀ X, P (P X)=P X) (hRR : ∀ X, R (R X)=R X)
    (hQQ : ∀ X, Q (Q X)=Q X)
    (hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range R))
    {ε : ℝ} (hε : 0≤ε)
    (hclose : ∀ X, (hsInner (P X-R X) (P X-R X)).re≤
      ε^2*(hsInner X X).re) :
    |sourceTrace (Q.comp P)-sourceTrace (Q.comp R)|≤
      ε*min (Module.finrank ℂ (LinearMap.range P) : ℝ) (sourceTrace Q) := by
  have hpair (X : Operator D) :
      hsInner X (Q X)=hsInner (Q X) (Q X) := by rw [hQ, hQQ]
  have hr := source_equalRank_effect_trace_bound P R Q hP hR hPP hRR hdim hε
    (w:=1) zero_le_one hclose
    (fun X => by rw [hpair]; exact hsInner_self_nonneg _)
    (fun X => by rw [hpair, one_mul]; exact source_projection_norm_le Q hQ hQQ X)
  have hq := source_projection_difference_trace_bound P R Q hQ hQQ hε hclose
  rw [mul_min_of_nonneg _ _ hε]
  exact le_min (by simpa only [one_mul] using hr) hq

/-- The actual centered-square certificate transports every bounded observable
and every projection trace with its smaller physical rank. -/
theorem source_centeredResidual_observable_trace_certificate
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
    (∀ (A : Operator D →ₗ[ℂ] Operator D) (a b : ℝ), a≤b →
      (∀ X, a*(hsInner X X).re≤(hsInner X (A X)).re) →
      (∀ X, (hsInner X (A X)).re≤b*(hsInner X X).re) →
      |sourceTrace (A.comp P)-sourceTrace (A.comp (sourceSpectralCut L hL S))|≤
        (b-a)*(ρ/d)*(r:ℝ)) ∧
    ∀ (Q : Operator D →ₗ[ℂ] Operator D), SourceSelfAdjoint Q →
      (∀ X, Q (Q X)=Q X) →
      |sourceTrace (Q.comp P)-sourceTrace (Q.comp (sourceSpectralCut L hL S))|≤
        (ρ/d)*min (r:ℝ) (sourceTrace Q) := by
  have hdimP : Module.finrank ℂ (LinearMap.range P)=r := by
    rw [← hspan, LinearMap.finrank_range_of_inj hF]
    simp
  have hdim : Module.finrank ℂ (LinearMap.range P)=
      Module.finrank ℂ (LinearMap.range (sourceSpectralCut L hL S)) := by
    rw [hdimP, sourceSpectralCut_finrank_range, hcount]
  have hclose := source_centeredResidual_projection_certificate
    L P hL hP hPP G hPG hker F hF hspan S hcount hρ hd hsmall hsep hres
  constructor
  · intro A a b hab hAlower hAupper
    have h := source_equalRank_observable_trace_bound P
      (sourceSpectralCut L hL S) A hP (sourceSpectralCut_selfAdjoint L hL S)
      hPP (sourceSpectralCut_idempotent L hL S) hdim
      (div_nonneg hρ hd.le) hab hclose hAlower hAupper
    simpa only [hdimP] using h
  · intro Q hQ hQQ
    have h := source_equalRank_projection_trace_bound P
      (sourceSpectralCut L hL S) Q hP (sourceSpectralCut_selfAdjoint L hL S)
      hQ hPP (sourceSpectralCut_idempotent L hL S) hQQ hdim
      (div_nonneg hρ hd.le) hclose
    simpa only [hdimP] using h


end Qatlib.Concepts.GibbsSource.SpectralGeom
