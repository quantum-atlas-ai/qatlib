/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PoweredCoreCircle
public import Qatlib.Papers.KnotLight13.TorusFamily.PowerRadialHeight

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Nonzero intermediate levels on the Bateman sphere

[Kedia2013TyingKnots], discussion of Fig. 2.
The radial height and the imaginary part of the product trace a round
quotient circle at fixed real part. Coprimality trivializes the circle
of coordinate phases over that quotient. Their product parametrizes
the entire intermediate level on the sphere.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set

/-- A fixed real part of the product label on the unit three-sphere. -/
def poweredSphereRealLevel (p q : ℕ) (c : ℝ) : Set (ℂ × ℂ) :=
  {z | Complex.normSq z.1 + Complex.normSq z.2 = 1 ∧ (z.1 ^ p * z.2 ^ q).re = c}

/-- Radius of the quotient circle at real level `c`. -/
noncomputable def poweredLevelRadius (p q : ℕ) (c : ℝ) : ℝ :=
  Real.sqrt (poweredPeakAmplitude p q ^ 2 - c ^ 2)

/-- A strict intermediate level gives a positive quotient radius. -/
theorem poweredLevelRadius_sq_pos {p q : ℕ} {c : ℝ} (hc : |c| < poweredPeakAmplitude p q) :
    poweredLevelRadius p q c ^ 2 = poweredPeakAmplitude p q ^ 2 - c ^ 2 ∧
      0 < poweredLevelRadius p q c := by
  have h := pow_lt_pow_left₀ hc (abs_nonneg c) (by decide : (2 : ℕ) ≠ 0)
  rw [sq_abs] at h
  exact ⟨Real.sq_sqrt (sub_nonneg.mpr h.le), Real.sqrt_pos.2 (sub_pos.mpr h)⟩

/-- For a nonzero level the quotient circle stays away from the two axes. -/
theorem poweredLevelRadius_lt_peak {p q : ℕ} {c : ℝ} (hn : c ≠ 0)
    (hc : |c| < poweredPeakAmplitude p q) : poweredLevelRadius p q c < poweredPeakAmplitude p q := by
  obtain ⟨hs, hpos⟩ := poweredLevelRadius_sq_pos hc
  have hA : 0 ≤ poweredPeakAmplitude p q := (abs_nonneg c).trans hc.le
  by_contra! h
  have hh := pow_le_pow_left₀ hA h 2
  nlinarith [sq_pos_of_ne_zero hn]

/-- The real component of a unit phase gives the signed radial height. -/
noncomputable def poweredLevelHeight {p q : ℕ} {c : ℝ} (hn : c ≠ 0)
    (hc : |c| < poweredPeakAmplitude p q) (u : Circle) :
    ↥(Icc (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q)) := by
  have hr := (poweredLevelRadius_sq_pos hc).2.le
  have hu : |(u : ℂ).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe u)
  have h : |poweredLevelRadius p q c * (u : ℂ).re| < poweredPeakAmplitude p q := by
    rw [abs_mul, abs_of_nonneg hr]
    calc
      _ ≤ poweredLevelRadius p q c * 1 := mul_le_mul_of_nonneg_left hu hr
      _ < poweredPeakAmplitude p q := by rw [mul_one]; exact poweredLevelRadius_lt_peak hn hc
  exact ⟨_, (abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩

/-- The inverse height coordinate supplies the first squared radius. -/
noncomputable def poweredLevelSquaredRadius {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) (u : Circle) : ℝ :=
  ((poweredRadialHeightHomeomorph hp hq).symm (poweredLevelHeight hn hc u) : ℝ)

/-- The squared radius is interior for the entire quotient circle. -/
theorem poweredLevelSquaredRadius_mem {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) (u : Circle) :
    poweredLevelSquaredRadius hp hq hn hc u ∈ Ioo (0 : ℝ) 1 := by
  apply poweredRadialHeight_inverse_mem_Ioo hp hq
  have hr := (poweredLevelRadius_sq_pos hc).2.le
  have hu : |(u : ℂ).re| ≤ 1 := (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe u)
  change -(poweredPeakAmplitude p q) < poweredLevelRadius p q c * (u : ℂ).re ∧
    poweredLevelRadius p q c * (u : ℂ).re < poweredPeakAmplitude p q
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hr]
  exact (mul_le_mul_of_nonneg_left hu hr).trans_lt (by simpa using poweredLevelRadius_lt_peak hn hc)

/-- The inverse radius recovers the quotient's height. -/
theorem poweredRadialHeight_level {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) (u : Circle) :
    poweredRadialHeight p q (poweredLevelSquaredRadius hp hq hn hc u) =
      poweredLevelRadius p q c * (u : ℂ).re :=
  poweredRadialHeight_inverse_apply hp hq (poweredLevelHeight hn hc u)

/-- The squared radius varies continuously around the quotient. -/
theorem continuous_poweredLevelSquaredRadius {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    Continuous (poweredLevelSquaredRadius hp hq hn hc) := by
  have h : Continuous (poweredLevelHeight hn hc) :=
    ((Complex.continuous_re.comp continuous_subtype_val).const_mul
      (poweredLevelRadius p q c)).subtype_mk _
  exact continuous_subtype_val.comp ((poweredRadialHeightHomeomorph hp hq).symm.continuous.comp h)

/-- The actual complex level on a quotient point, before normalization to a phase. -/
noncomputable def poweredLevelProduct (p q : ℕ) (c : ℝ) (u : Circle) : ℂ :=
  ⟨c, poweredLevelRadius p q c * (u : ℂ).im⟩

/-- The prescribed real part makes the complex product nonzero on the whole level. -/
theorem poweredLevelProduct_ne_zero (p q : ℕ) {c : ℝ} (hn : c ≠ 0) (u : Circle) :
    poweredLevelProduct p q c u ≠ 0 := by
  intro h
  exact hn (congrArg Complex.re h)

/-- Divide a nonzero complex number by its positive norm to obtain its phase. -/
noncomputable def poweredLevelPhase (p q : ℕ) {c : ℝ} (hn : c ≠ 0) (u : Circle) : Circle := by
  let g := poweredLevelProduct p q c u
  refine ⟨g / (‖g‖ : ℂ), ?_⟩
  change g / (‖g‖ : ℂ) ∈ Metric.sphere 0 1
  rw [Metric.mem_sphere, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg g)]
  exact div_self (norm_ne_zero_iff.mpr (poweredLevelProduct_ne_zero p q hn u))

/-- The product phase depends continuously on the quotient parameter. -/
theorem continuous_poweredLevelPhase (p q : ℕ) {c : ℝ} (hn : c ≠ 0) :
    Continuous (poweredLevelPhase p q hn) := by
  have hin : Continuous (fun u : Circle => (u : ℂ).im) := Complex.continuous_im.comp continuous_subtype_val
  have hg : Continuous (poweredLevelProduct p q c) :=
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk
      (hin.const_mul (poweredLevelRadius p q c)))
  exact (hg.div (Complex.continuous_ofReal.comp hg.norm) fun u =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (poweredLevelProduct_ne_zero p q hn u))).subtype_mk _

/-- Multiplying the unit phase by the norm recovers the product. -/
theorem poweredLevelProduct_phase (p q : ℕ) {c : ℝ} (hn : c ≠ 0) (u : Circle) :
    (‖poweredLevelProduct p q c u‖ : ℂ) * (poweredLevelPhase p q hn u : ℂ) =
      poweredLevelProduct p q c u := by
  let g := poweredLevelProduct p q c u
  change (‖g‖ : ℂ) * (g / (‖g‖ : ℂ)) = g
  rw [mul_comm, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (poweredLevelProduct_ne_zero p q hn u)))]

/-- The product modulus agrees with the power product of the two radii. -/
theorem norm_poweredLevelProduct {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) (u : Circle) :
    let r := poweredLevelSquaredRadius hp hq hn hc u
    ‖poweredLevelProduct p q c u‖ = Real.sqrt r ^ p * Real.sqrt (1 - r) ^ q := by
  let r := poweredLevelSquaredRadius hp hq hn hc u
  have hr := poweredLevelSquaredRadius_mem hp hq hn hc u
  obtain ⟨hR, _⟩ := poweredLevelRadius_sq_pos hc
  have hh := poweredRadialHeight_sq hp hq (r := r) ⟨hr.1.le, hr.2.le⟩
  rw [poweredRadialHeight_level hp hq hn hc u] at hh
  have hu := Circle.normSq_coe u
  rw [Complex.normSq_apply] at hu
  dsimp only
  apply (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (pow_nonneg (Real.sqrt_nonneg _) _)) (by decide : (2 : ℕ) ≠ 0)).1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, mul_pow,
    pow_right_comm _ p 2, pow_right_comm _ q 2, Real.sq_sqrt hr.1.le,
    Real.sq_sqrt (sub_nonneg.mpr hr.2.le)]
  change c * c + (poweredLevelRadius p q c * (u : ℂ).im) *
    (poweredLevelRadius p q c * (u : ℂ).im) = poweredRadiusProfile p q r
  linear_combination hR - hh + poweredLevelRadius p q c ^ 2 * hu


/-- The first circle chooses the quotient point, and the second runs
through the entire fiber of coordinate phases. -/
noncomputable def poweredSphereTorusParam {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) (u : Circle × Circle) :
    ℂ × ℂ :=
  let r := poweredLevelSquaredRadius hp hq hn hc u.1
  poweredTorusPhaseParam p q (Real.sqrt r) (Real.sqrt (1 - r)) (poweredLevelPhase p q hn u.1) u.2

/-- The torus parametrization depends continuously on both circle parameters. -/
theorem continuous_poweredSphereTorusParam {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    Continuous (poweredSphereTorusParam hp hq hn hc) := by
  have hr := (continuous_poweredLevelSquaredRadius hp hq hn hc).comp
    (continuous_fst : Continuous (Prod.fst : Circle × Circle → Circle))
  have hphase := (continuous_poweredLevelPhase p q hn).comp
    (continuous_fst : Continuous (Prod.fst : Circle × Circle → Circle))
  exact (continuous_poweredTorusPhaseParam p q).comp
    (((Real.continuous_sqrt.comp hr).prodMk
      (Real.continuous_sqrt.comp (continuous_const.sub hr))).prodMk
      (hphase.prodMk continuous_snd))

/-- The torus parameters recover the quotient radius and exact complex label. -/
theorem poweredSphereTorusParam_spec {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    (u : Circle × Circle) :
    let r := poweredLevelSquaredRadius hp hq hn hc u.1
    let z := poweredSphereTorusParam hp hq hn hc u
    Complex.normSq z.1 = r ∧ Complex.normSq z.2 = 1 - r ∧
      z.1 ^ p * z.2 ^ q = poweredLevelProduct p q c u.1 := by
  let r := poweredLevelSquaredRadius hp hq hn hc u.1
  let phase := poweredLevelPhase p q hn u.1
  let z := poweredSphereTorusParam hp hq hn hc u
  have hr := poweredLevelSquaredRadius_mem hp hq hn hc u.1
  obtain ⟨h₁, h₂, hpv⟩ := poweredTorusPhaseParam_spec hpq (Real.sqrt_nonneg r)
    (Real.sqrt_nonneg (1 - r)) phase u.2
  change ‖z.1‖ = Real.sqrt r at h₁
  change ‖z.2‖ = Real.sqrt (1 - r) at h₂
  refine ⟨?_, ?_, ?_⟩
  · change Complex.normSq z.1 = r
    rw [Complex.normSq_eq_norm_sq, h₁, Real.sq_sqrt hr.1.le]
  · change Complex.normSq z.2 = 1 - r
    rw [Complex.normSq_eq_norm_sq, h₂, Real.sq_sqrt (sub_nonneg.mpr hr.2.le)]
  · change z.1 ^ p * z.2 ^ q = _
    change z.1 ^ p * z.2 ^ q = (((Real.sqrt r ^ p * Real.sqrt (1 - r) ^ q : ℝ)) : ℂ) *
      (phase : ℂ) at hpv
    rw [hpv, ← norm_poweredLevelProduct hp hq hn hc u.1]
    exact poweredLevelProduct_phase p q hn u.1

/-- Equality of radius and complex label recovers the first circle parameter. -/
private theorem poweredLevelParameter_eq {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) {u v : Circle}
    (hr : poweredLevelSquaredRadius hp hq hn hc u = poweredLevelSquaredRadius hp hq hn hc v)
    (hg : poweredLevelProduct p q c u = poweredLevelProduct p q c v) : u = v := by
  have hR := (poweredLevelRadius_sq_pos hc).2.ne'
  have hreal := congrArg (poweredRadialHeight p q) hr
  rw [poweredRadialHeight_level hp hq hn hc u, poweredRadialHeight_level hp hq hn hc v] at hreal
  have him := congrArg Complex.im hg
  apply Circle.ext
  exact Complex.ext (mul_left_cancel₀ hR hreal) (mul_left_cancel₀ hR him)

/-- The quotient of a sphere point at the chosen real level gives its
first circle parameter. Its radius and product are recovered exactly. -/
private theorem exists_poweredLevelParameter {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) {z : ℂ × ℂ}
    (hz : z ∈ poweredSphereRealLevel p q c) :
    ∃ u : Circle, poweredLevelSquaredRadius hp hq hn hc u = Complex.normSq z.1 ∧
      poweredLevelProduct p q c u = z.1 ^ p * z.2 ^ q := by
  let r := Complex.normSq z.1
  let g := z.1 ^ p * z.2 ^ q
  let R := poweredLevelRadius p q c
  let H := poweredRadialHeight p q r
  have hR : 0 < R := (poweredLevelRadius_sq_pos hc).2
  have hsum := poweredSphereProduct_radial_circle hp hq hz.1
  change H ^ 2 + g.im ^ 2 = poweredPeakAmplitude p q ^ 2 - g.re ^ 2 at hsum
  have hre : g.re = c := hz.2
  rw [hre, ← (poweredLevelRadius_sq_pos hc).1] at hsum
  change H ^ 2 + g.im ^ 2 = R ^ 2 at hsum
  let u : Circle := ⟨⟨H / R, g.im / R⟩, by
    change (⟨H / R, g.im / R⟩ : ℂ) ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right]
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (2 : ℕ) ≠ 0)).1
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, one_pow]
    change (H / R) * (H / R) + (g.im / R) * (g.im / R) = 1
    field_simp [hR.ne']
    nlinarith⟩
  refine ⟨u, ?_, ?_⟩
  · apply (strictMonoOn_poweredRadialHeight hp hq).injOn
    · have hi := poweredLevelSquaredRadius_mem hp hq hn hc u
      exact ⟨hi.1.le, hi.2.le⟩
    · exact ⟨Complex.normSq_nonneg _, by linarith [hz.1, Complex.normSq_nonneg z.2]⟩
    · rw [poweredRadialHeight_level hp hq hn hc u]
      change R * (H / R) = H
      rw [mul_comm, div_mul_cancel₀ _ hR.ne']
  · apply Complex.ext hre.symm
    change R * (g.im / R) = g.im
    rw [mul_comm, div_mul_cancel₀ _ hR.ne']

/-- The entire nonzero intermediate real level on the sphere is
parametrized exactly once by the product of two circles. -/
theorem poweredSphereTorusParam_bijective {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    Function.Injective (poweredSphereTorusParam hp hq hn hc) ∧
      Set.range (poweredSphereTorusParam hp hq hn hc) = poweredSphereRealLevel p q c := by
  constructor
  · intro u v h
    obtain ⟨hu, _, hgu⟩ := poweredSphereTorusParam_spec hp hq hpq hn hc u
    obtain ⟨hv, _, hgv⟩ := poweredSphereTorusParam_spec hp hq hpq hn hc v
    have h₁ : u.1 = v.1 := poweredLevelParameter_eq hp hq hn hc
      (hu.symm.trans ((congrArg (fun z : ℂ × ℂ => Complex.normSq z.1) h).trans hv))
      (hgu.symm.trans ((congrArg (fun z : ℂ × ℂ => z.1 ^ p * z.2 ^ q) h).trans hgv))
    rcases u with ⟨u, w⟩
    rcases v with ⟨v, w'⟩
    change u = v at h₁
    subst v
    have hr := poweredLevelSquaredRadius_mem hp hq hn hc u
    have hinj := (poweredTorusPhaseParam_bijective hpq (Real.sqrt_pos.2 hr.1)
      (Real.sqrt_pos.2 (sub_pos.mpr hr.2)) (poweredLevelPhase p q hn u)).1
    exact Prod.ext rfl (hinj h)
  · ext z
    constructor
    · rintro ⟨u, rfl⟩
      have ⟨h₁, h₂, hprod⟩ := poweredSphereTorusParam_spec hp hq hpq hn hc u
      refine ⟨by linarith, ?_⟩
      have h := congrArg Complex.re hprod
      exact h
    · intro hz
      obtain ⟨u, hu, hg⟩ := exists_poweredLevelParameter hp hq hn hc hz
      let r := poweredLevelSquaredRadius hp hq hn hc u
      have hr := poweredLevelSquaredRadius_mem hp hq hn hc u
      change r = Complex.normSq z.1 at hu
      have h₂ : 1 - r = Complex.normSq z.2 := by linarith [hz.1]
      have hnorm₁ : ‖z.1‖ = Real.sqrt r := by
        rw [hu, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      have hnorm₂ : ‖z.2‖ = Real.sqrt (1 - r) := by
        rw [h₂, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      have hrange := (poweredTorusPhaseParam_bijective hpq (Real.sqrt_pos.2 hr.1)
        (Real.sqrt_pos.2 (sub_pos.mpr hr.2)) (poweredLevelPhase p q hn u)).2
      have hz' : z ∈ Set.range (poweredTorusPhaseParam p q (Real.sqrt r)
          (Real.sqrt (1 - r)) (poweredLevelPhase p q hn u)) := by
        rw [hrange]
        refine ⟨hnorm₁, hnorm₂, ?_⟩
        rw [← norm_poweredLevelProduct hp hq hn hc u, poweredLevelProduct_phase, hg]
      obtain ⟨w, hw⟩ := hz'
      exact ⟨(u, w), hw⟩

/-- The entire nonzero intermediate real level on the sphere is an
embedded topological torus. -/
noncomputable def poweredSphereRealLevelHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    (Circle × Circle) ≃ₜ ↥(poweredSphereRealLevel p q c) := by
  obtain ⟨hinj, hrange⟩ := poweredSphereTorusParam_bijective hp hq hpq hn hc
  let f : Circle × Circle → ↥(poweredSphereRealLevel p q c) := fun w =>
    ⟨poweredSphereTorusParam hp hq hn hc w, hrange ▸ mem_range_self w⟩
  have hsurj : Function.Surjective f := by
    intro z
    have hz : z.val ∈ Set.range (poweredSphereTorusParam hp hq hn hc) := by
      rw [hrange]
      exact z.property
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨fun _ _ h => hinj (congrArg Subtype.val h), hsurj⟩)
    ((continuous_poweredSphereTorusParam hp hq hn hc).subtype_mk _)

end Qatlib.Papers.KnotLight13.TorusFamily
