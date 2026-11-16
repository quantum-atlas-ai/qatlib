/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.ApproximateEnergyBandLeakage
public import Qatlib.Concepts.GibbsSource.SpectralGeom.LowSpectralTraceLeakage

@[expose] public section


/-! Whole trial-subspace leakage from the actual off-diagonal parent residual.
The trial projection acts on the complete complex Hilbert--Schmidt space. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
variable {D : ℕ}

/-- Block inner re le sqrt for the stated finite source data. -/
private theorem block_inner_re_le_sqrt (X Y : Operator D) :
    (hsInner X Y).re ≤ Real.sqrt ((hsInner X X).re*(hsInner Y Y).re) := by
  have h := hsInner_re_ge_neg_sqrt X ((-1:ℂ) • Y)
  simp only [hsInner_smul_left, hsInner_smul_right] at h
  norm_num at h
  linarith

/-- Orthogonal block decomposition, with its mixed term bounded by the
actual residual `(I-P) L P` on the entire trial range. -/
theorem source_block_residual_cap
    (L P : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P)
    (hPP : ∀ X, P (P X)=P X) {B lam η : ℝ} (hη : 0≤η)
    (hritz : ∀ X, (hsInner (P X) (L (P X))).re≤lam*(hsInner (P X) (P X)).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re≤
        η^2*(hsInner (P X) (P X)).re)
    (hcap : ∀ X, (hsInner X (L X)).re≤B*(hsInner X X).re) (X : Operator D) :
    (hsInner X (L X)).re≤
      lam*(hsInner (P X) (P X)).re+
      B*((hsInner X X).re-(hsInner (P X) (P X)).re)+
      2*η*Real.sqrt (((hsInner X X).re-(hsInner (P X) (P X)).re)*
        (hsInner (P X) (P X)).re) := by
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
    have haddl (A B C : Operator D) : hsInner (A+B) C=hsInner A C+hsInner B C := by
      simp [hsInner, add_mul, Matrix.trace_add]
    have haddr (A B C : Operator D) : hsInner A (B+C)=hsInner A B+hsInner A C := by
      simp [hsInner, mul_add, Matrix.trace_add]
    rw [map_add, haddl, haddr, haddr]
    simp only [Complex.add_re, hsym, hcross]
    ring
  have hpr : 0≤(hsInner U U).re := hsInner_self_nonneg U
  have hzr : 0≤(hsInner Z Z).re := hsInner_self_nonneg Z
  have hr : (hsInner Z R).re≤η*Real.sqrt ((hsInner Z Z).re*(hsInner U U).re) := by
    calc
      _≤Real.sqrt ((hsInner Z Z).re*(hsInner R R).re) := block_inner_re_le_sqrt Z R
      _≤Real.sqrt (η^2*((hsInner Z Z).re*(hsInner U U).re)) := by
        apply Real.sqrt_le_sqrt
        have h := mul_le_mul_of_nonneg_left (hres X) hzr
        change (hsInner Z Z).re*(hsInner R R).re≤
          (hsInner Z Z).re*(η^2*(hsInner U U).re) at h
        nlinarith only [h]
      _=_ := by rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη]
  have hc := hcap Z
  have ht := hritz X
  rw [hsplit]
  have hz := source_projection_pythagoras P hP hPP X
  change (hsInner Z Z).re=_ at hz
  rw [← hz]
  change (hsInner U (L U)).re+_+_≤lam*(hsInner U U).re+B*(hsInner Z Z).re+_
  nlinarith only [hc, ht, hr]

/-- Homogeneous form of the scalar residual-angle inequality. -/
theorem residual_angle_norm_lower_bound {a b η n p : ℝ}
    (ha : 0<a) (hab : a≤b) (hη : 0≤η) (hn : 0≤n) (hp : 0≤p) (hpn : p≤n)
    (hangle : a*n≤b*(n-p)+2*η*Real.sqrt ((n-p)*p)) :
    residualLeakageFactor a b η*n≤n-p := by
  by_cases hn0 : n=0
  · have hp0 : p=0 := by linarith
    simp [hn0, hp0]
  have hnpos : 0<n := lt_of_le_of_ne hn (Ne.symm hn0)
  have hu : 0≤(n-p)/n := div_nonneg (sub_nonneg.mpr hpn) hn
  have hu1 : (n-p)/n≤1 := (div_le_iff₀ hnpos).mpr (by linarith)
  have hr : Real.sqrt (((n-p)/n)*(1-(n-p)/n))=
      Real.sqrt ((n-p)*p)/n := by
    rw [show ((n-p)/n)*(1-(n-p)/n)=((n-p)*p)/n^2 by field_simp; ring,
      Real.sqrt_div (mul_nonneg (sub_nonneg.mpr hpn) hp), Real.sqrt_sq hn]
  have hs : a≤b*((n-p)/n)+2*η*Real.sqrt (((n-p)/n)*(1-(n-p)/n)) := by
    rw [hr]
    rw [show b*((n-p)/n)+2*η*(Real.sqrt ((n-p)*p)/n)=
      (b*(n-p)+2*η*Real.sqrt ((n-p)*p))/n by ring]
    exact (le_div_iff₀ hnpos).mpr hangle
  have h := residual_angle_lower_bound ha hab hη hu hu1 hs
  exact (le_div_iff₀ hnpos).mp h

/-- The residual factor lies in the unit interval, including zero residual. -/
theorem residualLeakageFactor_bounds {a b η : ℝ}
    (ha : 0<a) (hab : a≤b) (hη : 0≤η) :
    0≤residualLeakageFactor a b η ∧ residualLeakageFactor a b η≤1 := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<a*b+2*η^2+2*η*Real.sqrt (a*(b-a)+η^2) := by positivity
  constructor
  · exact div_nonneg (sq_nonneg a) hd.le
  · apply (div_le_iff₀ hd).mpr
    have h := mul_le_mul_of_nonneg_left hab ha.le
    have hr : 0≤2*η*Real.sqrt (a*(b-a)+η^2) := by positivity
    nlinarith only [h, hr, sq_nonneg η]

/-- The actual centered band is uniformly separated from the trial projection. -/
theorem source_blockResidual_centered_angle
    (L P Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P) (hQ : SourceSelfAdjoint Q)
    (hPP : ∀ X, P (P X)=P X) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) {B α lam η : ℝ}
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α) (hη : 0≤η)
    (hritz : ∀ X, (hsInner (P X) (L (P X))).re≤lam*(hsInner (P X) (P X)).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re≤
        η^2*(hsInner (P X) (P X)).re)
    (hcap : ∀ X, (hsInner X (L X)).re≤B*(hsInner X X).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) (X : Operator D) :
    (hsInner (P (sourceCenteredProjection Q G X))
      (P (sourceCenteredProjection Q G X))).re≤
      (1-residualLeakageFactor (α-lam) (B-lam) η)*
        (hsInner (sourceCenteredProjection Q G X) (sourceCenteredProjection Q G X)).re := by
  let Y := sourceCenteredProjection Q G X
  obtain ⟨hf, ho, _⟩ := sourceCenteredProjection_properties Q hQ hQQ G hp X
  have hb := hband Y hf ho
  have hc := source_block_residual_cap L P hL hP hPP hη hritz hres hcap Y
  have ha : (α-lam)*(hsInner Y Y).re≤
      (B-lam)*((hsInner Y Y).re-(hsInner (P Y) (P Y)).re)+
      2*η*Real.sqrt (((hsInner Y Y).re-(hsInner (P Y) (P Y)).re)*
        (hsInner (P Y) (P Y)).re) := by linarith only [hb, hc]
  have h := residual_angle_norm_lower_bound (sub_pos.mpr hgap)
    (by linarith only [hαB]) hη (hsInner_self_nonneg Y) (hsInner_self_nonneg (P Y))
    (source_projection_norm_le P hP hPP Y) ha
  change (hsInner (P Y) (P Y)).re≤(1-residualLeakageFactor (α-lam) (B-lam) η)*_
  linarith only [h]

/-- Every vector in the trial space obeys the Gibbs-mass-sensitive leakage
bound. The statement is homogeneous and accepts complex non-Hermitian modes. -/
theorem source_blockResidual_uniform_leakage
    (L P Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P) (hQ : SourceSelfAdjoint Q)
    (hPP : ∀ X, P (P X)=P X) (hQQ : ∀ X, Q (Q X)=Q X)
    (G X : Operator D) {B α lam η : ℝ}
    (hG : (hsInner G G).re=1) (hPG : P G=0) (hPX : P X=X)
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α) (hη : 0≤η)
    (hritz : ∀ Y, (hsInner (P Y) (L (P Y))).re≤lam*(hsInner (P Y) (P Y)).re)
    (hres : ∀ Y,
      (hsInner (L (P Y)-P (L (P Y))) (L (P Y)-P (L (P Y)))).re≤
        η^2*(hsInner (P Y) (P Y)).re)
    (hcap : ∀ Y, (hsInner Y (L Y)).re≤B*(hsInner Y Y).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    (hsInner (Q G) (Q G)).re*residualLeakageFactor (α-lam) (B-lam) η*
      (hsInner X X).re≤(hsInner (X-Q X) (X-Q X)).re := by
  have hd := residualLeakageFactor_bounds (b := B-lam)
    (sub_pos.mpr hgap) (by linarith only [hαB]) hη
  have ho : hsInner G X=0 := by
    rw [← hPX, ← hP, hPG]
    simp [hsInner]
  have ha := source_blockResidual_centered_angle L P Q hL hP hQ hPP hQQ G
    hp hαB hgap hη hritz hres hcap hband
  have hv := source_projection_angle_dual (sourceCenteredProjection Q G) P
    (sourceCenteredProjection_selfAdjoint Q hQ G) hP
    (sourceCenteredProjection_idempotent Q hQ hQQ G hp) hPP
    (sub_nonneg.mpr hd.2) ha X
  rw [hPX] at hv
  have hm := sourceCenteredProjection_mass_angle Q hQ hQQ G X hG ho hp
  have hmul := mul_le_mul_of_nonneg_left hv hp.le
  nlinarith only [hm, hmul]

/-- Both sharp trace constraints are derived from the actual block residual. -/
theorem source_blockResidual_sharp_trace_leakage
    (L P Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P) (hQ : SourceSelfAdjoint Q)
    (hPP : ∀ X, P (P X)=P X) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) {B α lam η : ℝ}
    (hG : (hsInner G G).re=1) (hPG : P G=0)
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α) (hη : 0≤η)
    (hritz : ∀ X, (hsInner (P X) (L (P X))).re≤lam*(hsInner (P X) (P X)).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re≤
        η^2*(hsInner (P X) (P X)).re)
    (hcap : ∀ X, (hsInner X (L X)).re≤B*(hsInner X X).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    max ((sourceTrace P-1+(hsInner (Q G) (Q G)).re)*
        residualLeakageFactor (α-lam) (B-lam) η)
      (sourceTrace P-(sourceTrace Q-1)-1+(hsInner (Q G) (Q G)).re+
        (sourceTrace Q-1)*residualLeakageFactor (α-lam) (B-lam) η)≤
      sourceTrace P-sourceTrace (P.comp Q) := by
  have hd := residualLeakageFactor_bounds (b := B-lam)
    (sub_pos.mpr hgap) (by linarith only [hαB]) hη
  have h := source_projection_sharp_trace_leakage P Q hP hQ hPP hQQ G hG hPG
    (sub_nonneg.mpr hd.2) (by linarith only [hd.1]) hp
    (source_blockResidual_centered_angle L P Q hL hP hQ hPP hQQ G
      hp hαB hgap hη hritz hres hcap hband)
  simpa only [sub_sub_cancel] using h

/-- Orthogonality of a supplied trial family removes the actual Gibbs root. -/
theorem sourceFamilyProjection_kernel {r : ℕ} (X : Fin r → Operator D) (G : Operator D)
    (horth : ∀ i, hsInner G (X i)=0) : sourceFamilyProjection X G=0 := by
  have ho (i : Fin r) : hsInner (X i) G=0 := by
    rw [hsInner_conj_swap, horth i, star_zero]
  simp [sourceFamilyProjection_apply, ho]

/-- Every orthonormal subfamily of the trial range inherits the original
whole-block residual certificate, including coherent rotations and smaller spans. -/
theorem source_blockResidual_subfamily_sharp_trace_leakage {r : ℕ}
    (L P Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P) (hQ : SourceSelfAdjoint Q)
    (hPP : ∀ Y, P (P Y)=P Y) (hQQ : ∀ Y, Q (Q Y)=Q Y)
    (G : Operator D) (X : Fin r → Operator D) {B α lam η : ℝ}
    (hG : (hsInner G G).re=1) (hPG : P G=0)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0)
    (hPX : ∀ i, P (X i)=X i)
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α) (hη : 0≤η)
    (hritz : ∀ Y, (hsInner (P Y) (L (P Y))).re≤lam*(hsInner (P Y) (P Y)).re)
    (hres : ∀ Y,
      (hsInner (L (P Y)-P (L (P Y))) (L (P Y)-P (L (P Y)))).re≤
        η^2*(hsInner (P Y) (P Y)).re)
    (hcap : ∀ Y, (hsInner Y (L Y)).re≤B*(hsInner Y Y).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    max (((r:ℝ)-1+(hsInner (Q G) (Q G)).re)*residualLeakageFactor (α-lam) (B-lam) η)
      ((r:ℝ)-(sourceTrace Q-1)-1+(hsInner (Q G) (Q G)).re+
        (sourceTrace Q-1)*residualLeakageFactor (α-lam) (B-lam) η)≤
      ∑ i, (hsInner (X i-Q (X i)) (X i-Q (X i))).re := by
  let F := sourceFamilyProjection X
  have hF : SourceSelfAdjoint F := sourceFamilyProjection_selfAdjoint X
  have hFF : ∀ Y, F (F Y)=F Y := sourceFamilyProjection_idempotent X horth
  have hFP (Y : Operator D) : F (P Y)=F Y := by
    simp only [F, sourceFamilyProjection_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← hP, hPX]
  have hFG : F G=0 := by rw [← hFP G, hPG, map_zero]
  have hd := residualLeakageFactor_bounds (b := B-lam)
    (sub_pos.mpr hgap) (by linarith only [hαB]) hη
  have ha (Y : Operator D) :
      (hsInner (F (sourceCenteredProjection Q G Y)) (F (sourceCenteredProjection Q G Y))).re≤
      (1-residualLeakageFactor (α-lam) (B-lam) η)*
        (hsInner (sourceCenteredProjection Q G Y) (sourceCenteredProjection Q G Y)).re := by
    rw [← hFP (sourceCenteredProjection Q G Y)]
    exact (source_projection_norm_le F hF hFF _).trans
      (source_blockResidual_centered_angle L P Q hL hP hQ hPP hQQ G
        hp hαB hgap hη hritz hres hcap hband Y)
  have h := source_projection_sharp_trace_leakage F Q hF hQ hFF hQQ G hG hFG
    (sub_nonneg.mpr hd.2) (by linarith only [hd.1]) hp ha
  change max _ _≤sourceTrace (sourceFamilyProjection X)-sourceTrace ((sourceFamilyProjection X).comp Q) at h
  rw [sourceFamilyProjection_leakage_sum X horth Q hQ hQQ] at h
  change max (((sourceTrace (sourceFamilyProjection X))-1+(hsInner (Q G) (Q G)).re)*_) _≤_ at h
  rw [sourceTrace_familyProjection X horth] at h
  simpa only [sub_sub_cancel] using h

/-- Both sharp bounds hold for an arbitrary orthonormal trial family,
using the Ritz bound and block residual of its actual span projection. -/
theorem source_blockResidualFamily_sharp_trace_leakage {r : ℕ}
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ Y, Q (Q Y)=Q Y)
    (G : Operator D) (X : Fin r → Operator D) {B α lam η : ℝ}
    (hG : (hsInner G G).re=1)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0)
    (hGX : ∀ i, hsInner G (X i)=0)
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α) (hη : 0≤η)
    (hritz : ∀ Y,
      (hsInner (sourceFamilyProjection X Y) (L (sourceFamilyProjection X Y))).re≤
        lam*(hsInner (sourceFamilyProjection X Y) (sourceFamilyProjection X Y)).re)
    (hres : ∀ Y,
      (hsInner (L (sourceFamilyProjection X Y)-sourceFamilyProjection X (L (sourceFamilyProjection X Y)))
        (L (sourceFamilyProjection X Y)-sourceFamilyProjection X (L (sourceFamilyProjection X Y)))).re≤
        η^2*(hsInner (sourceFamilyProjection X Y) (sourceFamilyProjection X Y)).re)
    (hcap : ∀ Y, (hsInner Y (L Y)).re≤B*(hsInner Y Y).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    max (((r:ℝ)-1+(hsInner (Q G) (Q G)).re)*residualLeakageFactor (α-lam) (B-lam) η)
      ((r:ℝ)-(sourceTrace Q-1)-1+(hsInner (Q G) (Q G)).re+
        (sourceTrace Q-1)*residualLeakageFactor (α-lam) (B-lam) η)≤
      ∑ i, (hsInner (X i-Q (X i)) (X i-Q (X i))).re := by
  have h := source_blockResidual_sharp_trace_leakage L (sourceFamilyProjection X) Q
    hL (sourceFamilyProjection_selfAdjoint X) hQ
    (sourceFamilyProjection_idempotent X horth) hQQ G hG
    (sourceFamilyProjection_kernel X G hGX) hp hαB hgap hη hritz hres hcap hband
  rw [sourceFamilyProjection_leakage_sum X horth Q hQ hQQ,
    sourceTrace_familyProjection X horth] at h
  exact h

/-- A rational lower factor can be consumed without evaluating the radical. -/
theorem source_blockResidual_centered_angle_budget
    (L P Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hP : SourceSelfAdjoint P) (hQ : SourceSelfAdjoint Q)
    (hPP : ∀ X, P (P X)=P X) (hQQ : ∀ X, Q (Q X)=Q X)
    (G : Operator D) {B α lam η w ell : ℝ}
    (hp : 0<(hsInner (Q G) (Q G)).re) (hαB : α≤B) (hgap : lam<α)
    (hη : 0≤η) (hw : 0≤w) (hell : 0≤ell)
    (hroot : (α-lam)*(B-α)+η^2≤w^2)
    (hbudget : ell*((α-lam)*(B-lam)+2*η^2+2*η*w)≤(α-lam)^2)
    (hritz : ∀ X, (hsInner (P X) (L (P X))).re≤lam*(hsInner (P X) (P X)).re)
    (hres : ∀ X,
      (hsInner (L (P X)-P (L (P X))) (L (P X)-P (L (P X)))).re≤
        η^2*(hsInner (P X) (P X)).re)
    (hcap : ∀ X, (hsInner X (L X)).re≤B*(hsInner X X).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) (X : Operator D) :
    (hsInner (P (sourceCenteredProjection Q G X))
      (P (sourceCenteredProjection Q G X))).re≤
      (1-ell)*(hsInner (sourceCenteredProjection Q G X) (sourceCenteredProjection Q G X)).re := by
  have hd : ell≤residualLeakageFactor (α-lam) (B-lam) η :=
    residual_leakage_budget (sub_pos.mpr hgap) (by linarith only [hαB]) hη hw hell
      (by convert hroot using 1; ring) hbudget
  have h := source_blockResidual_centered_angle L P Q hL hP hQ hPP hQQ G
    hp hαB hgap hη hritz hres hcap hband X
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith only [hd]) (hsInner_self_nonneg _))

/-- Vanishing off-diagonal residual recovers the invariant-subspace factor. -/
theorem residualLeakageFactor_zero {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    residualLeakageFactor a b 0=a/b := by
  have hb : 0<b := ha.trans_le hab
  unfold residualLeakageFactor
  simp only [zero_pow (by decide : (2:ℕ)≠0), mul_zero, zero_mul, add_zero]
  field_simp

/-- Exact rational budget for the scaled six-dimensional trial certificate. -/
theorem residualLeakageFactor_sixMode_budget {s : ℝ} (hs : 0<s) :
    (677:ℝ)/1000≤residualLeakageFactor (6*s-(39/10)*s) (7*s-(39/10)*s) (s/10000) := by
  apply residual_leakage_budget (w := (3/2)*s)
  · linarith
  · linarith
  · positivity
  · positivity
  · norm_num
  · nlinarith only [sq_nonneg s]
  · nlinarith only [sq_nonneg s]

/-- A six-vector block certificate consumes the same scaled cap, band floor,
thermal mass and source-band dimension as the exact-low-space budget. -/
theorem source_blockResidual_sixMode_budget
    (L Q : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hQ : SourceSelfAdjoint Q) (hQQ : ∀ Y, Q (Q Y)=Q Y)
    (G : Operator D) (X : Fin 6 → Operator D) {s : ℝ} (hs : 0<s)
    (hG : (hsInner G G).re=1)
    (horth : ∀ i j, hsInner (X i) (X j)=if i=j then 1 else 0)
    (hGX : ∀ i, hsInner G (X i)=0)
    (hmass : (119:ℝ)/1000<(hsInner (Q G) (Q G)).re)
    (hdim : sourceTrace Q=4)
    (hritz : ∀ Y,
      (hsInner (sourceFamilyProjection X Y) (L (sourceFamilyProjection X Y))).re≤
        ((39/10)*s)*(hsInner (sourceFamilyProjection X Y) (sourceFamilyProjection X Y)).re)
    (hres : ∀ Y,
      (hsInner (L (sourceFamilyProjection X Y)-sourceFamilyProjection X (L (sourceFamilyProjection X Y)))
        (L (sourceFamilyProjection X Y)-sourceFamilyProjection X (L (sourceFamilyProjection X Y)))).re≤
        (s/10000)^2*(hsInner (sourceFamilyProjection X Y) (sourceFamilyProjection X Y)).re)
    (hcap : ∀ Y, (hsInner Y (L Y)).re≤(7*s)*(hsInner Y Y).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      (6*s)*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    (83:ℝ)/20<∑ i, (hsInner (X i-Q (X i)) (X i-Q (X i))).re := by
  have hp : 0<(hsInner (Q G) (Q G)).re := by linarith
  have h := source_blockResidualFamily_sharp_trace_leakage L Q hL hQ hQQ G X hG horth hGX
    hp (show 6*s≤7*s by linarith) (show (39/10)*s<6*s by linarith)
    (show 0≤s/10000 by positivity) hritz hres hcap hband
  have hsecond := (le_max_right _ _).trans h
  rw [hdim] at hsecond
  norm_num at hsecond
  have hd := residualLeakageFactor_sixMode_budget hs
  linarith only [hsecond, hd, hmass]

end Qatlib.Concepts.GibbsSource.SpectralGeom
