/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanSphereField

import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Polar coordinates on the Bateman magnetic quotient

[Kedia2013TyingKnots], discussion of Fig. 2.
The quotient coordinates are the first squared radius and the
imaginary product label. On an intermediate real level their polar
angle about the critical radius increases along the normalized field.
Each ray from that center meets the quotient once, so the polar
direction gives a global circle coordinate.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open scoped ComplexConjugate

/-- The planar quotient after translating the peak radius to the origin. -/
noncomputable def batemanMagneticQuotient (p q : ℕ) (w : ℂ × ℂ) : ℂ :=
  ((Complex.normSq w.1 - poweredPeakRadius p q : ℝ) : ℂ) +
    Complex.I * (((w.1 ^ p * w.2 ^ q).im : ℝ) : ℂ)

/-- The radial equation of an intermediate quotient level increases
strictly along every nonzero ray from the peak, for as long as its
first squared radius belongs to the unit interval. -/
theorem batemanMagneticQuotient_ray_strictMono
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (c x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    let k := poweredPeakRadius p q
    StrictMonoOn (fun t : ℝ => (t * y) ^ 2 + c ^ 2 - poweredRadiusProfile p q (k + t * x))
      {t : ℝ | 0 ≤ t ∧ k + t * x ∈ Set.Icc (0 : ℝ) 1} := by
  intro k s hs t ht hst
  have hs₀ : 0 ≤ s := hs.1
  have ht₀ : 0 ≤ t := ht.1
  have hsq : s ^ 2 < t ^ 2 := pow_lt_pow_left₀ hst hs₀ (by decide : (2 : ℕ) ≠ 0)
  have hquad : (s * y) ^ 2 ≤ (t * y) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right hsq.le (sq_nonneg y)
  obtain ⟨hm, hanti⟩ := poweredRadiusProfile_monotone hp hq
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hs' : k + s * x ∈ Set.Icc 0 k :=
      ⟨hs.2.1, by linarith [mul_nonpos_of_nonneg_of_nonpos hs₀ hx.le]⟩
    have ht' : k + t * x ∈ Set.Icc 0 k :=
      ⟨ht.2.1, by linarith [mul_nonpos_of_nonneg_of_nonpos ht₀ hx.le]⟩
    have hlt : k + t * x < k + s * x := by linarith [mul_lt_mul_of_neg_right hst hx]
    linarith only [hquad, hm ht' hs' hlt]
  · have hy : y ^ 2 = 1 := by simpa only [hx, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hxy
    simp only [hx, mul_zero, add_zero, mul_pow, hy, mul_one]
    linarith only [hsq]
  · have hs' : k + s * x ∈ Set.Icc k 1 :=
      ⟨by linarith [mul_nonneg hs₀ hx.le], hs.2.2⟩
    have ht' : k + t * x ∈ Set.Icc k 1 :=
      ⟨by linarith [mul_nonneg ht₀ hx.le], ht.2.2⟩
    have hlt : k + s * x < k + t * x := by linarith [mul_lt_mul_of_pos_right hst hx]
    linarith only [hquad, hanti hs' ht' hlt]

/-- The actual planar quotient of the real product level, centered at
the peak squared radius. -/
def batemanMagneticOval (p q : ℕ) (c : ℝ) : Set ℂ :=
  {z | z.re + poweredPeakRadius p q ∈ Set.Icc (0 : ℝ) 1 ∧
    z.im ^ 2 + c ^ 2 = poweredRadiusProfile p q (z.re + poweredPeakRadius p q)}

/-- The unit-sphere identity makes the physical label project to this oval. -/
theorem batemanMagneticQuotient_mem_oval (p q : ℕ) (w : ℂ × ℂ)
    (hw : Complex.normSq w.1 + Complex.normSq w.2 = 1) :
    batemanMagneticQuotient p q w ∈ batemanMagneticOval p q (w.1 ^ p * w.2 ^ q).re := by
  let r := Complex.normSq w.1
  let g := w.1 ^ p * w.2 ^ q
  have ht : Complex.normSq g = poweredRadiusProfile p q r :=
    normSq_poweredProduct_on_sphere p q hw
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Complex.normSq_nonneg _, by linarith [hw, Complex.normSq_nonneg w.2]⟩
  have hRe : (batemanMagneticQuotient p q w).re + poweredPeakRadius p q = r := by
    simp [batemanMagneticQuotient, Complex.add_re, Complex.mul_re, r]
  have hIm : (batemanMagneticQuotient p q w).im = g.im := by
    simp [batemanMagneticQuotient, Complex.add_im, Complex.mul_im, g]
  change (batemanMagneticQuotient p q w).re + poweredPeakRadius p q ∈ Set.Icc (0 : ℝ) 1 ∧
    (batemanMagneticQuotient p q w).im ^ 2 + g.re ^ 2 =
      poweredRadiusProfile p q ((batemanMagneticQuotient p q w).re + poweredPeakRadius p q)
  rw [hRe, hIm, ← ht, Complex.normSq_apply]
  exact ⟨hr, by ring⟩

/-- When the real product is strictly below peak modulus, the center
of the quotient is outside its level curve. -/
theorem batemanMagneticOval_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hc : |c| < poweredPeakAmplitude p q) {z : ℂ} (hz : z ∈ batemanMagneticOval p q c) :
    z ≠ 0 := by
  rintro rfl
  have hh := hz.2
  simp only [Complex.zero_re, Complex.zero_im, zero_add, zero_pow (by decide : (2 : ℕ) ≠ 0),
    ← poweredPeakAmplitude_sq hp hq] at hh
  have hl := pow_lt_pow_left₀ hc (abs_nonneg c) (by decide : (2 : ℕ) ≠ 0)
  rw [sq_abs] at hl
  exact hl.ne hh

/-- Each unit direction meets a strict intermediate quotient curve
at exactly one positive radius. -/
theorem batemanMagneticOval_existsUnique_radius
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ} (h₀ : c ≠ 0)
    (hc : |c| < poweredPeakAmplitude p q) (u : Circle) :
    ∃! t : ℝ, 0 < t ∧ (t : ℂ) * (u : ℂ) ∈ batemanMagneticOval p q c := by
  let k := poweredPeakRadius p q
  let A := poweredPeakAmplitude p q
  let x := (u : ℂ).re
  let y := (u : ℂ).im
  let F := fun t : ℝ => (t * y) ^ 2 + c ^ 2 - poweredRadiusProfile p q (k + t * x)
  let D := {t : ℝ | 0 ≤ t ∧ k + t * x ∈ Set.Icc (0 : ℝ) 1}
  have hk : k ∈ Set.Ioo (0 : ℝ) 1 := poweredPeakRadius_mem hp hq
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two, x, y] using Circle.normSq_coe u
  have hA : 0 < A := poweredPeakAmplitude_pos hp hq
  have hF : Continuous F := by
    dsimp only [F, poweredRadiusProfile]
    fun_prop
  have hF₀ : F 0 < 0 := by
    have hs := pow_lt_pow_left₀ hc (abs_nonneg c) (by decide : (2 : ℕ) ≠ 0)
    rw [sq_abs, poweredPeakAmplitude_sq hp hq] at hs
    simpa only [F, zero_mul, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add,
      k, sub_neg] using hs
  have hEnd : ∃ T : ℝ, 0 < T ∧ k + T * x ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < F T := by
    rcases lt_trichotomy x 0 with hx | hx | hx
    · let T := k / (-x)
      have hT : 0 < T := div_pos hk.1 (neg_pos.mpr hx)
      have he : k + T * x = 0 := by
        dsimp only [T]
        field_simp [hx.ne]
        ring
      refine ⟨T, hT, by rw [he]; exact ⟨le_rfl, zero_le_one⟩, ?_⟩
      dsimp only [F]
      rw [he, poweredRadiusProfile, zero_pow hp.ne', zero_mul, sub_zero]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₀)
    · have hy : y ^ 2 = 1 := by
        simpa only [hx, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using hxy
      refine ⟨A, hA, by simpa only [hx, mul_zero, add_zero] using ⟨hk.1.le, hk.2.le⟩, ?_⟩
      dsimp only [F]
      rw [hx, mul_zero, add_zero, mul_pow, hy, mul_one, ← poweredPeakAmplitude_sq hp hq]
      change 0 < A ^ 2 + c ^ 2 - A ^ 2
      linarith only [sq_pos_of_ne_zero h₀]
    · let T := (1 - k) / x
      have hT : 0 < T := div_pos (sub_pos.mpr hk.2) hx
      have he : k + T * x = 1 := by
        dsimp only [T]
        field_simp [hx.ne']
        ring
      refine ⟨T, hT, by rw [he]; exact ⟨zero_le_one, le_rfl⟩, ?_⟩
      dsimp only [F]
      rw [he, poweredRadiusProfile, sub_self, zero_pow hq.ne', mul_zero, sub_zero]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₀)
  obtain ⟨T, hT, hTD, hTF⟩ := hEnd
  have hsub : Set.Icc (0 : ℝ) T ⊆ D := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rcases le_or_gt 0 x with hx | hx
    · exact ⟨by linarith [mul_nonneg ht.1 hx, hk.1],
        by linarith [mul_le_mul_of_nonneg_right ht.2 hx, hTD.2]⟩
    · exact ⟨by linarith [mul_le_mul_of_nonpos_right ht.2 hx.le, hTD.1],
        by linarith [mul_nonpos_of_nonneg_of_nonpos ht.1 hx.le, hk.2]⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hT.le hF.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (F 0) (F T) from ⟨hF₀.le, hTF.le⟩)
  have hpos : 0 < t := by
    refine lt_of_le_of_ne ht.1 ?_
    intro he
    rw [← he] at hzero
    exact hF₀.ne hzero
  have hmem (s : ℝ) :
      (s : ℂ) * (u : ℂ) ∈ batemanMagneticOval p q c ↔
        k + s * x ∈ Set.Icc (0 : ℝ) 1 ∧ F s = 0 := by
    unfold batemanMagneticOval
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, F, sub_eq_zero, x, y, k, add_comm]
  refine ⟨t, ⟨hpos, (hmem t).2 ⟨(hsub ht).2, hzero⟩⟩, ?_⟩
  rintro s ⟨hs, hsm⟩
  obtain ⟨hsI, hs0⟩ := (hmem s).1 hsm
  exact (batemanMagneticQuotient_ray_strictMono hp hq c x y hxy).injOn
    ⟨hs.le, hsI⟩ (hsub ht) (hs0.trans hzero.symm)

/-- The quotient oval is compact in the complex plane. -/
theorem isCompact_batemanMagneticOval {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (c : ℝ) :
    IsCompact (batemanMagneticOval p q c) := by
  let k := poweredPeakRadius p q
  let A := poweredPeakAmplitude p q
  have hk : k ∈ Set.Ioo (0 : ℝ) 1 := poweredPeakRadius_mem hp hq
  have hA : 0 < A := poweredPeakAmplitude_pos hp hq
  have hR : Continuous (fun z : ℂ => z.re + k) := Complex.continuous_re.add_const k
  have hP : Continuous (poweredRadiusProfile p q) := by
    unfold poweredRadiusProfile
    fun_prop
  have hClosed : IsClosed (batemanMagneticOval p q c) :=
    (isClosed_Icc.preimage hR).inter
      (isClosed_eq ((Complex.continuous_im.pow 2).add_const (c ^ 2)) (hP.comp hR))
  refine (isCompact_closedBall (0 : ℂ) (1 + A)).of_isClosed_subset hClosed ?_
  intro z hz
  change z.re + k ∈ Set.Icc (0 : ℝ) 1 ∧
    z.im ^ 2 + c ^ 2 = poweredRadiusProfile p q (z.re + k) at hz
  have hPeak : poweredRadiusProfile p q (z.re + k) ≤ A ^ 2 := by
    change poweredRadiusProfile p q _ ≤ poweredPeakAmplitude p q ^ 2
    rw [poweredPeakAmplitude_sq hp hq]
    by_cases h : z.re + k = poweredPeakRadius p q
    · rw [h]
    · exact (poweredRadiusProfile_lt_peak hp hq hz.1 h).le
  have hx : |z.re| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hz.1.1, hk.2], by linarith [hz.1.2, hk.1]⟩
  have hx₂ := pow_le_pow_left₀ (abs_nonneg z.re) hx 2
  rw [sq_abs, one_pow] at hx₂
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, pow_two, pow_two]
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  have hlt := pow_lt_pow_left₀ h (by positivity : 0 ≤ 1 + A) (by decide : (2 : ℕ) ≠ 0)
  nlinarith [hz.2, sq_nonneg c]

/-- The actual polar direction of a quotient point gives a unit phase. -/
noncomputable def batemanMagneticOvalPhase {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hc : |c| < poweredPeakAmplitude p q) (z : ↥(batemanMagneticOval p q c)) : Circle :=
  ⟨z.val / (‖z.val‖ : ℂ), by
    change _ ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr
        (batemanMagneticOval_ne_zero hp hq hc z.property))]⟩

/-- The polar direction varies continuously along the oval. -/
theorem continuous_batemanMagneticOvalPhase {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hc : |c| < poweredPeakAmplitude p q) :
    Continuous (batemanMagneticOvalPhase hp hq hc) :=
  (continuous_subtype_val.div (Complex.continuous_ofReal.comp continuous_subtype_val.norm)
    fun z => Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (batemanMagneticOval_ne_zero hp hq hc z.property))).subtype_mk _

/-- The quotient circle uses its geometric polar angle about the peak
radius as a global coordinate. -/
noncomputable def batemanMagneticOvalHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    ↥(batemanMagneticOval p q c) ≃ₜ Circle := by
  let f := batemanMagneticOvalPhase hp hq hc
  have recover (z : ↥(batemanMagneticOval p q c)) : (‖z.val‖ : ℂ) * (f z : ℂ) = z.val := by
    change (‖z.val‖ : ℂ) * (z.val / (‖z.val‖ : ℂ)) = _
    rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (batemanMagneticOval_ne_zero hp hq hc z.property)))]
  have hinj : Function.Injective f := by
    intro z w h
    have hz := norm_pos_iff.mpr (batemanMagneticOval_ne_zero hp hq hc z.property)
    have hw := norm_pos_iff.mpr (batemanMagneticOval_ne_zero hp hq hc w.property)
    have ht := batemanMagneticOval_existsUnique_radius hp hq h₀ hc (f z)
    have hnorm : ‖z.val‖ = ‖w.val‖ := ht.unique
      ⟨hz, by rw [recover z]; exact z.property⟩
      ⟨hw, by rw [h, recover w]; exact w.property⟩
    apply Subtype.ext
    rw [← recover z, ← recover w, hnorm, h]
  have hsurj : Function.Surjective f := by
    intro u
    obtain ⟨t, ⟨ht, hm⟩, _⟩ := batemanMagneticOval_existsUnique_radius hp hq h₀ hc u
    refine ⟨⟨(t : ℂ) * (u : ℂ), hm⟩, Circle.ext ?_⟩
    change (t : ℂ) * (u : ℂ) / (‖(t : ℂ) * (u : ℂ)‖ : ℂ) = (u : ℂ)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, Circle.norm_coe, mul_one]
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  letI : CompactSpace ↥(batemanMagneticOval p q c) :=
    isCompact_iff_compactSpace.mp (isCompact_batemanMagneticOval hp hq c)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩)
    (continuous_batemanMagneticOvalPhase hp hq hc)

/-- The closed planar system for the centered radius and imaginary
product of the normalized magnetic field. -/
noncomputable def batemanMagneticOvalVector (p q : ℕ) (z : ℂ) : ℂ :=
  let r := z.re + poweredPeakRadius p q
  let M := (p : ℝ) * (q : ℝ) * r ^ (p - 1) * (1 - r) ^ (q - 1)
  ((-2 * (p : ℝ) * (q : ℝ) * z.im : ℝ) : ℂ) +
    Complex.I * ((M * ((p : ℝ) + (q : ℝ)) * z.re : ℝ) : ℂ)

/-- The quotient of an actual normalized sphere tangent satisfies
the autonomous planar differential equation. -/
theorem hasDerivAt_batemanMagneticQuotient
    (p q : ℕ) {w : ℝ → ℂ × ℂ} {s : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s)
    (hs : Complex.normSq (w s).1 + Complex.normSq (w s).2 = 1) :
    HasDerivAt (fun u => batemanMagneticQuotient p q (w u))
      (batemanMagneticOvalVector p q (batemanMagneticQuotient p q (w s))) s := by
  let r := Complex.normSq (w s).1
  let b := Complex.normSq (w s).2
  let k := poweredPeakRadius p q
  let g := (w s).1 ^ p * (w s).2 ^ q
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hcrit : k * ((p : ℝ) + (q : ℝ)) = (p : ℝ) :=
    (eq_div_iff (add_pos hpR hqR).ne').1 rfl
  have hb : b = 1 - r := by change r + b = 1 at hs; linarith
  have hbal : (q : ℝ) * r - (p : ℝ) * b = ((p : ℝ) + (q : ℝ)) * (r - k) := by
    linear_combination (p : ℝ) * hb.symm + hcrit
  have hRe := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_batemanSphereMagnetic_radius hp hq hw).sub_const k)
  have hIm := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_batemanSphereMagnetic_imaginary hp hq hw)
  have h := hRe.add (hIm.const_mul Complex.I)
  have hxr : (batemanMagneticQuotient p q (w s)).re = r - k := by
    simp [batemanMagneticQuotient, Complex.add_re, Complex.mul_re, r, k]
  have hyi : (batemanMagneticQuotient p q (w s)).im = g.im := by
    simp [batemanMagneticQuotient, Complex.add_im, Complex.mul_im, g]
  unfold batemanMagneticOvalVector
  rw [hxr, hyi, sub_add_cancel]
  change HasDerivAt (fun u => batemanMagneticQuotient p q (w u))
    (((-2 * (p : ℝ) * (q : ℝ) * g.im : ℝ) : ℂ) +
      Complex.I * (((p : ℝ) * (q : ℝ) * r ^ (p - 1) * (1 - r) ^ (q - 1) *
        ((p : ℝ) + (q : ℝ)) * (r - k) : ℝ) : ℂ)) s
  have hv : (p : ℝ) * (q : ℝ) * r ^ (p - 1) * (1 - r) ^ (q - 1) *
      ((p : ℝ) + (q : ℝ)) * (r - k) =
      (p : ℝ) * (q : ℝ) * r ^ (p - 1) * b ^ (q - 1) * ((q : ℝ) * r - (p : ℝ) * b) := by
    rw [hbal, hb]
    ring
  rw [hv]
  exact h

/-- A nonzero real product forces both squared radii to be interior
on the quotient oval. -/
theorem batemanMagneticOval_radial_mem {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (h₀ : c ≠ 0) {z : ℂ} (hz : z ∈ batemanMagneticOval p q c) :
    z.re + poweredPeakRadius p q ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨lt_of_le_of_ne hz.1.1 ?_, lt_of_le_of_ne hz.1.2 ?_⟩
  · intro he
    have h := hz.2
    rw [← he, poweredRadiusProfile, zero_pow hp.ne', zero_mul] at h
    nlinarith [sq_pos_of_ne_zero h₀]
  · intro he
    have h := hz.2
    rw [he, poweredRadiusProfile, sub_self, zero_pow hq.ne', mul_zero] at h
    nlinarith [sq_pos_of_ne_zero h₀]

/-- The centered position and the autonomous velocity have strictly
positive signed determinant at every point of the oval. -/
theorem batemanMagneticOval_determinant_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {z : ℂ} (hz : z ∈ batemanMagneticOval p q c) :
    0 < (conj z * batemanMagneticOvalVector p q z).im := by
  let r := z.re + poweredPeakRadius p q
  let M := (p : ℝ) * (q : ℝ) * r ^ (p - 1) * (1 - r) ^ (q - 1)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := batemanMagneticOval_radial_mem hp hq h₀ hz
  have hM : 0 < M :=
    mul_pos (mul_pos (mul_pos hpR hqR) (pow_pos hr.1 _)) (pow_pos (sub_pos.mpr hr.2) _)
  have he : (conj z * batemanMagneticOvalVector p q z).im =
      M * ((p : ℝ) + (q : ℝ)) * z.re ^ 2 + 2 * (p : ℝ) * (q : ℝ) * z.im ^ 2 := by
    dsimp only [batemanMagneticOvalVector]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero]
    change z.re * (M * ((p : ℝ) + (q : ℝ)) * z.re) +
      -z.im * (-2 * (p : ℝ) * (q : ℝ) * z.im) = _
    ring
  rw [he]
  by_cases h : z.re = 0
  · have hi : z.im ≠ 0 := by
      intro hi
      exact batemanMagneticOval_ne_zero hp hq hc hz (Complex.ext h hi)
    have hh : 0 < z.im ^ 2 := sq_pos_of_ne_zero hi
    positivity
  · have hh : 0 < z.re ^ 2 := sq_pos_of_ne_zero h
    positivity

/-- The determinant for a normalized magnetic tangent is positive on
a nonzero strict intermediate real level. -/
theorem batemanMagneticQuotient_angle_pos
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s)
    (hs : Complex.normSq (w s).1 + Complex.normSq (w s).2 = 1)
    (h₀ : ((w s).1 ^ p * (w s).2 ^ q).re ≠ 0)
    (hc : |((w s).1 ^ p * (w s).2 ^ q).re| < poweredPeakAmplitude p q) :
    0 < (conj (batemanMagneticQuotient p q (w s)) *
      deriv (fun u => batemanMagneticQuotient p q (w u)) s).im := by
  rw [(hasDerivAt_batemanMagneticQuotient p q hp hq hw hs).deriv]
  exact batemanMagneticOval_determinant_pos hp hq h₀ hc
    (batemanMagneticQuotient_mem_oval p q (w s) hs)

/-- The unit phase of a complex curve rotates at the signed determinant
of position and velocity divided by squared radius. -/
theorem hasDerivAt_batemanUnitPhase {z : ℝ → ℂ} {s : ℝ} {v : ℂ}
    (hz : HasDerivAt z v s) (hne : z s ≠ 0) :
    HasDerivAt (fun t => z t / (‖z t‖ : ℂ))
      (Complex.I * (((conj (z s) * v).im / Complex.normSq (z s) : ℝ) : ℂ) *
        (z s / (‖z s‖ : ℂ))) s := by
  let N := ‖z s‖
  let a := (conj (z s) * v).re
  let b := (conj (z s) * v).im
  have hN : N ≠ 0 := norm_ne_zero_iff.mpr hne
  have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hz
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hz
  have hsq := (hRe.mul hRe).add (hIm.mul hIm)
  change HasDerivAt (fun t => (z t).re * (z t).re + (z t).im * (z t).im)
    (v.re * (z s).re + (z s).re * v.re + (v.im * (z s).im + (z s).im * v.im)) s at hsq
  have hsq' : HasDerivAt (fun t => Complex.normSq (z t)) (2 * a) s := by
    have he : v.re * (z s).re + (z s).re * v.re + (v.im * (z s).im + (z s).im * v.im) = 2 * a := by
      simp only [a, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    simpa only [Complex.normSq_apply, he] using hsq
  have hnorm := hsq'.sqrt (Complex.normSq_pos.mpr hne).ne'
  have hsqrt (t : ℝ) : Real.sqrt (Complex.normSq (z t)) = ‖z t‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simp only [hsqrt, mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0 by norm_num)] at hnorm
  have hden := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hnorm
  have hd := hz.fun_div hden hNc
  change HasDerivAt (fun t => z t / (‖z t‖ : ℂ))
    ((v * (N : ℂ) - z s * (↑(a / N) : ℂ)) / (N : ℂ) ^ 2) s at hd
  have hdecomp : (a : ℂ) + Complex.I * (b : ℂ) = conj (z s) * v := by
    simpa only [mul_comm Complex.I (b : ℂ)] using Complex.re_add_im (conj (z s) * v)
  have hmul : v * (N : ℂ) ^ 2 = z s * ((a : ℂ) + Complex.I * (b : ℂ)) := by
    rw [hdecomp, ← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    ring
  have hEq : (v * (N : ℂ) - z s * (↑(a / N) : ℂ)) / (N : ℂ) ^ 2 =
      Complex.I * (↑(b / N ^ 2) : ℂ) * (z s / (N : ℂ)) := by
    push_cast
    field_simp [hNc]
    linear_combination hmul
  rw [hEq] at hd
  simpa only [Complex.normSq_eq_norm_sq, N, b] using hd

/-- Angular speed of the normalized quotient in its polar circle coordinate. -/
noncomputable def batemanMagneticOvalSpeed (p q : ℕ) (z : ℂ) : ℝ :=
  (conj z * batemanMagneticOvalVector p q z).im / Complex.normSq z

/-- The quotient angle advances everywhere on each strict intermediate oval. -/
theorem batemanMagneticOvalSpeed_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {z : ℂ} (hz : z ∈ batemanMagneticOval p q c) :
    0 < batemanMagneticOvalSpeed p q z :=
  div_pos (batemanMagneticOval_determinant_pos hp hq h₀ hc hz)
    (Complex.normSq_pos.mpr (batemanMagneticOval_ne_zero hp hq hc hz))

/-- The angular speed is continuous on the whole intermediate quotient. -/
theorem continuous_batemanMagneticOvalSpeed {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hc : |c| < poweredPeakAmplitude p q) :
    Continuous (fun z : ↥(batemanMagneticOval p q c) => batemanMagneticOvalSpeed p q z.val) := by
  have hvec : Continuous (batemanMagneticOvalVector p q) := by
    unfold batemanMagneticOvalVector
    fun_prop
  have h : Continuous (fun z : ℂ => (conj z * batemanMagneticOvalVector p q z).im) :=
    Complex.continuous_im.comp (Complex.continuous_conj.mul hvec)
  exact (h.comp continuous_subtype_val).div
    (Complex.continuous_normSq.comp continuous_subtype_val) (fun z =>
      (Complex.normSq_pos.mpr (batemanMagneticOval_ne_zero hp hq hc z.property)).ne')

/-- The projection of the normalized magnetic flow obeys the scalar
angular equation, with speed depending on the quotient point alone. -/
theorem hasDerivAt_batemanMagneticOvalPhase
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hc : |c| < poweredPeakAmplitude p q) {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s)
    (hs : Complex.normSq (w s).1 + Complex.normSq (w s).2 = 1)
    (hlevel : ∀ t, (batemanMagneticQuotient p q (w t)) ∈ batemanMagneticOval p q c) :
    let z := fun t => batemanMagneticQuotient p q (w t)
    let phase := fun t => (batemanMagneticOvalPhase hp hq hc ⟨z t, hlevel t⟩ : ℂ)
    HasDerivAt phase (Complex.I * (batemanMagneticOvalSpeed p q (z s) : ℂ) * phase s) s :=
  hasDerivAt_batemanUnitPhase (hasDerivAt_batemanMagneticQuotient p q hp hq hw hs)
    (batemanMagneticOval_ne_zero hp hq hc (hlevel s))

end Qatlib.Papers.KnotLight13.TorusFamily
