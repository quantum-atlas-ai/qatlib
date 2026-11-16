/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SpectralGeom.EnergyBandLeakage

@[expose] public section


/-! Residual-certified energy-band leakage for the original CKG parents.
The residual is measured in the full complex Hilbert--Schmidt space. -/

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.SpectralGeom
variable {D : ℕ}

/-- The real Hilbert--Schmidt inner product is bounded below by the negative norm product. -/
theorem hsInner_re_ge_neg_sqrt {D : ℕ} (U V : Operator D) :
    -Real.sqrt ((hsInner U U).re * (hsInner V V).re) ≤ (hsInner U V).re := by
  have hU : 0 ≤ (hsInner U U).re := hsInner_self_nonneg U
  have hV : 0 ≤ (hsInner V V).re := hsInner_self_nonneg V
  have hprod : 0 ≤ (hsInner U U).re * (hsInner V V).re := mul_nonneg hU hV
  rcases eq_or_lt_of_le hprod with h0 | hpos
  · rw [← h0, Real.sqrt_zero, neg_zero]
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · have hU0 : U = 0 := hsInner_self_re_zero_iff h1
      rw [hU0]; simp [hsInner]
    · have hV0 : V = 0 := hsInner_self_re_zero_iff h1
      rw [hV0]; simp [hsInner]
  · set nU : ℝ := (hsInner U U).re with hnU
    set nV : ℝ := (hsInner V V).re with hnV
    have hstar_real : ∀ r : ℝ, star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := fun r => by simp
    have hsU : Real.sqrt nU * Real.sqrt nU = nU := by
      rw [← sq]; exact Real.sq_sqrt hU
    have hsV : Real.sqrt nV * Real.sqrt nV = nV := by
      rw [← sq]; exact Real.sq_sqrt hV
    have hcoefV : (((Real.sqrt nV : ℝ) : ℂ) * ((Real.sqrt nV : ℝ) : ℂ))
        = ((nV : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hsV]
    have hcoefX : (((Real.sqrt nV : ℝ) : ℂ) * ((Real.sqrt nU : ℝ) : ℂ))
        = ((Real.sqrt nV * Real.sqrt nU : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
    have hY := hsInner_re_ge_neg_half (((Real.sqrt nV : ℝ) : ℂ) • U)
      (((Real.sqrt nU : ℝ) : ℂ) • V)
    have hself1 : (hsInner (((Real.sqrt nV : ℝ) : ℂ) • U)
          (((Real.sqrt nV : ℝ) : ℂ) • U)).re = nV * nU := by
      rw [hsInner_smul_left, hsInner_smul_right, ← mul_assoc, hstar_real, hcoefV,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, ← hnU]
    have hself2 : (hsInner (((Real.sqrt nU : ℝ) : ℂ) • V)
          (((Real.sqrt nU : ℝ) : ℂ) • V)).re = nU * nV := by
      rw [hsInner_smul_left, hsInner_smul_right, ← mul_assoc, hstar_real,
        ← Complex.ofReal_mul, hsU,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, ← hnV]
    have hcross : (hsInner (((Real.sqrt nV : ℝ) : ℂ) • U)
          (((Real.sqrt nU : ℝ) : ℂ) • V)).re
        = Real.sqrt nV * Real.sqrt nU * (hsInner U V).re := by
      rw [hsInner_smul_left, hsInner_smul_right, ← mul_assoc, hstar_real, hcoefX,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
    rw [hself1, hself2, hcross] at hY
    have hq2 : Real.sqrt nU * Real.sqrt nV * (Real.sqrt nU * Real.sqrt nV)
        = nU * nV := by nlinarith [hsU, hsV]
    have hq : 0 < Real.sqrt nU * Real.sqrt nV := by
      have h1 : 0 < Real.sqrt (nU * nV) := Real.sqrt_pos_of_pos hpos
      rw [Real.sqrt_mul hU nV] at h1
      exact h1
    rw [Real.sqrt_mul hU nV]
    have hfin : Real.sqrt nU * Real.sqrt nV
        * ((hsInner U V).re + Real.sqrt nU * Real.sqrt nV) ≥ 0 := by
      nlinarith [hY, hq, hq2]
    nlinarith [hfin, hq]


/-- Hs Inner real self for the stated finite source data. -/
private theorem hsInner_real_self (X : Operator D) :
    hsInner X X = ((hsInner X X).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using hsInner_self_re X

/-- Hs Inner re le sqrt product for the stated finite source data. -/
private theorem hsInner_re_le_sqrt_product (X Y : Operator D) :
    (hsInner X Y).re ≤ Real.sqrt ((hsInner X X).re * (hsInner Y Y).re) := by
  have h := hsInner_re_ge_neg_sqrt X ((-1:ℂ) • Y)
  simp only [hsInner_smul_left, hsInner_smul_right] at h
  norm_num at h
  linarith

/-- The angle estimate for a unit trial and its orthogonal projection.
The residual bound is an inequality on the actual parent applied to the
trial, so it can be supplied by a certified numerical enclosure. -/
theorem source_trial_projection_angle
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (X Y : Operator D) {B α E η : ℝ}
    (hX : (hsInner X X).re = 1)
    (hXY : hsInner X Y = hsInner Y Y)
    (hE : (hsInner X (L X)).re = E) (hη : 0 ≤ η)
    (hres : (hsInner (L X - (E:ℂ) • X) (L X - (E:ℂ) • X)).re ≤ η^2)
    (hαB : α ≤ B)
    (hcap : ∀ Z, (hsInner Z (L Z)).re ≤ B * (hsInner Z Z).re)
    (hband : α * (hsInner Y Y).re ≤ (hsInner Y (L Y)).re) :
    α-E ≤ (B-E) * (1-(hsInner Y Y).re) +
      2*η*Real.sqrt ((1-(hsInner Y Y).re)*(hsInner Y Y).re) := by
  let t := (hsInner Y Y).re
  let Z := Y - (t:ℂ) • X
  let R := L X - (E:ℂ) • X
  have ht : 0 ≤ t := hsInner_self_nonneg Y
  have hXX : hsInner X X = (1:ℂ) := by
    rw [hsInner_real_self, hX]
    rfl
  have hYY : hsInner Y Y = (t:ℂ) := hsInner_real_self Y
  have hXY' : hsInner X Y = (t:ℂ) := hXY.trans hYY
  have hYX' : hsInner Y X = (t:ℂ) := by
    rw [hsInner_conj_swap, hXY']
    simp
  have hnZ : (hsInner Z Z).re = t-t^2 := by
    dsimp only [Z]
    rw [hsInner_sub_smul_self, hXX, hXY', hYY]
    simp only [star_ofReal, mul_one, ← Complex.ofReal_mul,
      Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    ring
  have ht1 : t ≤ 1 := by
    have h := hsInner_self_nonneg Z
    rw [hnZ] at h
    nlinarith
  have hLX : (hsInner (L X) X).re = E := by
    rw [hL]
    exact hE
  have hcross : (hsInner Y (L X)).re = (hsInner X (L Y)).re := by
    rw [← hL, hsInner_conj_swap]
    simp
  have hcross' : (hsInner (L X) Y).re = (hsInner X (L Y)).re := by
    rw [hL]
  have hRZ : (hsInner R Z).re = (hsInner X (L Y)).re - E*t := by
    dsimp only [R, Z]
    simp only [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left,
      hsInner_smul_right, star_ofReal, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      hLX, hXY', hXX, Complex.one_re, hcross']
    ring
  have heZ : (hsInner Z (L Z)).re =
      (hsInner Y (L Y)).re - E*t^2 - 2*t*(hsInner R Z).re := by
    rw [hRZ]
    dsimp only [Z]
    simp only [map_sub, map_smul, hsInner_sub_left, hsInner_sub_right,
      hsInner_smul_left, hsInner_smul_right, star_ofReal, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, hE, hcross]
    ring
  have hn : 0 ≤ (1-t)*t := mul_nonneg (sub_nonneg.mpr ht1) ht
  have hr : (hsInner R Z).re ≤ η * Real.sqrt ((1-t)*t) := by
    calc
      _ ≤ Real.sqrt ((hsInner R R).re * (hsInner Z Z).re) :=
        hsInner_re_le_sqrt_product R Z
      _ ≤ Real.sqrt (η^2 * ((1-t)*t)) := by
        apply Real.sqrt_le_sqrt
        rw [hnZ]
        have hr := mul_le_mul_of_nonneg_right hres hn
        change (hsInner R R).re * ((1-t)*t) ≤ _ at hr
        nlinarith
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη]
  by_cases ht0 : t=0
  · change α-E ≤ (B-E)*(1-t)+2*η*Real.sqrt ((1-t)*t)
    rw [ht0]
    simp only [sub_zero, mul_zero, Real.sqrt_zero, mul_one, add_zero]
    linarith
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hc := hcap Z
  rw [hnZ, heZ] at hc
  have hr' := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*t)
  change α*t ≤ _ at hband
  have h : (α-E)*t ≤ ((B-E)*(1-t)+2*η*Real.sqrt ((1-t)*t))*t := by
    nlinarith only [hc, hband, hr']
  exact (mul_le_mul_iff_left₀ htpos).mp h

/-- Solving the residual angle inequality gives its smaller quadratic root.
The rationalized form remains well defined when the residual is zero. -/
theorem residual_angle_lower_bound {a b η u : ℝ}
    (ha : 0<a) (hab : a≤b) (hη : 0≤η) (hu : 0≤u) (hu1 : u≤1)
    (hangle : a≤b*u+2*η*Real.sqrt (u*(1-u))) :
    a^2 / (a*b+2*η^2+2*η*Real.sqrt (a*(b-a)+η^2)) ≤ u := by
  let radical := Real.sqrt (a*(b-a)+η^2)
  let center := a*b+2*η^2
  let quad := b^2+4*η^2
  let denom := center+2*η*radical
  have hb : 0<b := ha.trans_le hab
  have hrad : 0≤a*(b-a)+η^2 := by positivity
  have hs : radical^2=a*(b-a)+η^2 := Real.sq_sqrt hrad
  have hs0 : 0≤radical := Real.sqrt_nonneg _
  have hquad : 0<quad := by dsimp [quad]; positivity
  have hcenter : 0<center := by dsimp [center]; positivity
  have hdenom : 0<denom := by dsimp [denom]; positivity
  change a^2/denom≤u
  apply (div_le_iff₀ hdenom).mpr
  by_cases hlinear : a≤b*u
  · have h1 := mul_le_mul_of_nonneg_right hlinear ha.le
    have h2 : a*b≤denom := by
      dsimp [denom, center]
      nlinarith only [sq_nonneg η, mul_nonneg hη hs0]
    have h3 := mul_le_mul_of_nonneg_left h2 hu
    nlinarith only [h1, h3]
  have hdiff : 0≤a-b*u := by linarith
  have hu2 : 0≤u*(1-u) := mul_nonneg hu (sub_nonneg.mpr hu1)
  have hright : 0≤2*η*Real.sqrt (u*(1-u)) := by positivity
  have hsquare := (sq_le_sq₀ hdiff hright).mpr
    (show a-b*u≤2*η*Real.sqrt (u*(1-u)) by linarith only [hangle])
  rw [mul_pow, Real.sq_sqrt hu2, mul_pow] at hsquare
  have hpoly : quad*u^2-2*center*u+a^2≤0 := by
    dsimp [quad, center]
    nlinarith only [hsquare]
  have hidentity : center^2-(2*η*radical)^2=quad*a^2 := by
    dsimp [center, quad]
    rw [mul_pow, hs]
    ring
  have hmul := mul_nonpos_of_nonneg_of_nonpos hquad.le hpoly
  have hsq : (center-quad*u)^2≤(2*η*radical)^2 := by
    nlinarith only [hmul, hidentity]
  have hroot : center-quad*u≤2*η*radical :=
    le_of_sq_le_sq hsq (by positivity)
  have hroot' : center-2*η*radical≤quad*u := by linarith only [hroot]
  apply (mul_le_mul_iff_right₀ hquad).mp
  calc
    quad*a^2 = (center-2*η*radical)*denom := by
      dsimp [denom]
      nlinarith only [hidentity]
    _ ≤ (quad*u)*denom := mul_le_mul_of_nonneg_right hroot' hdenom.le
    _ = quad*(u*denom) := by ring

/-- A root-free sufficient budget for the same leakage factor.
All four budget inequalities are polynomial inequalities and allow exact
rational arithmetic once a square-root upper enclosure w is chosen. -/
theorem residual_leakage_budget {a b η w ell : ℝ}
    (ha : 0<a) (hab : a≤b) (hη : 0≤η) (hw : 0≤w) (hell : 0≤ell)
    (hroot : a*(b-a)+η^2≤w^2)
    (hbudget : ell*(a*b+2*η^2+2*η*w)≤a^2) :
    ell≤a^2/(a*b+2*η^2+2*η*Real.sqrt (a*(b-a)+η^2)) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<a*b+2*η^2+2*η*Real.sqrt (a*(b-a)+η^2) := by positivity
  have hr : Real.sqrt (a*(b-a)+η^2)≤w := (Real.sqrt_le_iff).mpr ⟨hw, hroot⟩
  apply (le_div_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0≤2*η)
  have hd' : a*b+2*η^2+2*η*Real.sqrt (a*(b-a)+η^2)≤a*b+2*η^2+2*η*w := by
    linarith only [hm]
  exact (mul_le_mul_of_nonneg_left hd' hell).trans hbudget

/-- The rationalized smaller root of the residual angle inequality. -/
noncomputable def residualLeakageFactor (a b η : ℝ) : ℝ :=
  a^2 / (a*b+2*η^2+2*η*Real.sqrt (a*(b-a)+η^2))

/-- Projection norm le one for the stated finite source data. -/
private theorem projection_norm_le_one (X Y : Operator D)
    (hX : (hsInner X X).re=1) (hXY : hsInner X Y=hsInner Y Y) :
    (hsInner Y Y).re≤1 := by
  have hYX : hsInner Y X=hsInner Y Y := by
    rw [hsInner_conj_swap, hXY, hsInner_real_self]
    simp
  have h := hsInner_self_nonneg (X-Y)
  rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right] at h
  simp only [hX, hXY, hYX, Complex.sub_re] at h
  linarith

/-- The real Rayleigh center minimizes the squared HS residual among all
real centers. This permits a certificate to use any rational center c. -/
theorem source_rayleigh_residual_min (X W : Operator D) {E c : ℝ}
    (hX : (hsInner X X).re=1) (hE : (hsInner X W).re=E) :
    (hsInner (W-(E:ℂ) • X) (W-(E:ℂ) • X)).re ≤
      (hsInner (W-(c:ℂ) • X) (W-(c:ℂ) • X)).re := by
  have hWX : (hsInner W X).re=E := by
    rw [hsInner_conj_swap]
    simpa using hE
  have hnorm (r : ℝ) :
      (hsInner (W-(r:ℂ) • X) (W-(r:ℂ) • X)).re =
        (hsInner W W).re-2*r*E+r^2 := by
    simp only [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left,
      hsInner_smul_right, star_ofReal, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hX, hE, hWX]
    ring
  rw [hnorm E, hnorm c]
  nlinarith only [sq_nonneg (c-E)]

/-- The closed leakage factor uses verified energy enclosures and a
residual at an arbitrary real center. -/
theorem source_trial_projection_le_of_bounds
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (X Y : Operator D) {B α Elo Ehi η c : ℝ}
    (hX : (hsInner X X).re=1) (hXY : hsInner X Y=hsInner Y Y)
    (hElo : Elo≤(hsInner X (L X)).re)
    (hEhi : (hsInner X (L X)).re≤Ehi)
    (hη : 0≤η)
    (hres : (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re≤η^2)
    (hαB : α≤B) (hgap : Ehi<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    residualLeakageFactor (α-Ehi) (B-Elo) η≤1-(hsInner Y Y).re := by
  let E := (hsInner X (L X)).re
  let t := (hsInner Y Y).re
  have ht : 0≤t := hsInner_self_nonneg Y
  have ht1 : t≤1 := projection_norm_le_one X Y hX hXY
  have hu : 0≤1-t := sub_nonneg.mpr ht1
  have hu1 : 1-t≤1 := by linarith only [ht]
  have hresE : (hsInner (L X-(E:ℂ) • X) (L X-(E:ℂ) • X)).re≤η^2 :=
    (source_rayleigh_residual_min X (L X) hX (rfl : (hsInner X (L X)).re=E)).trans hres
  have hangle := source_trial_projection_angle L hL X Y hX hXY rfl hη hresE hαB hcap hband
  change α-E≤(B-E)*(1-t)+2*η*Real.sqrt ((1-t)*t) at hangle
  have hcoefficient : (B-E)*(1-t)≤(B-Elo)*(1-t) :=
    mul_le_mul_of_nonneg_right (by dsimp [E]; linarith only [hElo]) hu
  have hangle' : α-Ehi≤(B-Elo)*(1-t)+2*η*Real.sqrt ((1-t)*(1-(1-t))) := by
    rw [show 1-(1-t)=t by ring]
    change E≤Ehi at hEhi
    linarith only [hangle, hcoefficient, hEhi]
  exact residual_angle_lower_bound (sub_pos.mpr hgap)
    (by linarith only [hαB, hElo, hEhi]) hη hu hu1 hangle'

/-- Gibbs-centering transports the residual factor to the actual squared
mass outside the supplied orthogonal compression. -/
theorem source_trial_centered_leakage_of_bounds
    (L Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G X : Operator D) {B α Elo Ehi η c : ℝ}
    (hG : (hsInner G G).re=1) (hX : (hsInner X X).re=1)
    (horth : hsInner G X=0) (hp : 0<(hsInner (Q G) (Q G)).re)
    (hElo : Elo≤(hsInner X (L X)).re)
    (hEhi : (hsInner X (L X)).re≤Ehi)
    (hη : 0≤η)
    (hres : (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re≤η^2)
    (hαB : α≤B) (hgap : Ehi<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    (hsInner (Q G) (Q G)).re*residualLeakageFactor (α-Ehi) (B-Elo) η≤
      (hsInner (X-Q X) (X-Q X)).re := by
  obtain ⟨hf, ho, hxy, hpdist⟩ := source_centered_projection Q hQ hQQ G X hG hX horth hp
  have h := source_trial_projection_le_of_bounds L hL X _ hX hxy hElo hEhi
    hη hres hαB hgap hcap (hband _ hf ho)
  exact (mul_le_mul_of_nonneg_left h hp.le).trans hpdist

/-- If the compressed trial is already Gibbs-orthogonal, the full residual
factor bounds exterior mass directly, without a centering loss. -/
theorem source_trial_compression_leakage_of_bounds
    (L Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G X : Operator D) {B α Elo Ehi η c : ℝ}
    (hX : (hsInner X X).re=1) (hcenter : hsInner G (Q X)=0)
    (hElo : Elo≤(hsInner X (L X)).re)
    (hEhi : (hsInner X (L X)).re≤Ehi)
    (hη : 0≤η)
    (hres : (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re≤η^2)
    (hαB : α≤B) (hgap : Ehi<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re) :
    residualLeakageFactor (α-Ehi) (B-Elo) η≤
      (hsInner (X-Q X) (X-Q X)).re := by
  have hXY : hsInner X (Q X)=hsInner (Q X) (Q X) := by
    simpa only [hQQ] using (hQ X (Q X)).symm
  have hYX : hsInner (Q X) X=hsInner (Q X) (Q X) := by
    rw [hsInner_conj_swap, hXY, hsInner_real_self]
    simp
  have hnorm : (hsInner (X-Q X) (X-Q X)).re=1-(hsInner (Q X) (Q X)).re := by
    rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right, hXY, hYX]
    simp only [Complex.sub_re, hX]
    ring
  rw [hnorm]
  exact source_trial_projection_le_of_bounds L hL X (Q X) hX hXY hElo hEhi
    hη hres hαB hgap hcap (hband _ (hQQ X) hcenter)

/-- A polynomial certificate for a trial whose compressed component is
Gibbs-orthogonal. A certified tighter parent cap can be used directly. -/
theorem source_trial_compression_budget
    (L Q : Operator D →ₗ[ℂ] Operator D)
    (hL : SourceSelfAdjoint L) (hQ : SourceSelfAdjoint Q)
    (hQQ : ∀ X, Q (Q X)=Q X) (G X : Operator D)
    {B α Elo Ehi η c w ell : ℝ}
    (hX : (hsInner X X).re=1) (hcenter : hsInner G (Q X)=0)
    (hElo : Elo≤(hsInner X (L X)).re)
    (hEhi : (hsInner X (L X)).re≤Ehi)
    (hη : 0≤η)
    (hres : (hsInner (L X-(c:ℂ) • X) (L X-(c:ℂ) • X)).re≤η^2)
    (hαB : α≤B) (hgap : Ehi<α)
    (hcap : ∀ Z, (hsInner Z (L Z)).re≤B*(hsInner Z Z).re)
    (hband : ∀ Y, Q Y=Y → hsInner G Y=0 →
      α*(hsInner Y Y).re≤(hsInner Y (L Y)).re)
    (hw : 0≤w) (hell : 0≤ell)
    (hroot : (α-Ehi)*((B-Elo)-(α-Ehi))+η^2≤w^2)
    (hbudget : ell*((α-Ehi)*(B-Elo)+2*η^2+2*η*w)≤(α-Ehi)^2) :
    ell≤(hsInner (X-Q X) (X-Q X)).re := by
  have hscalar := residual_leakage_budget (sub_pos.mpr hgap)
    (by linarith only [hαB, hElo, hEhi]) hη hw hell hroot hbudget
  exact hscalar.trans (source_trial_compression_leakage_of_bounds
    L Q hL hQ hQQ G X hX hcenter hElo hEhi hη hres hαB hgap hcap hband)

end Qatlib.Concepts.GibbsSource.SpectralGeom
