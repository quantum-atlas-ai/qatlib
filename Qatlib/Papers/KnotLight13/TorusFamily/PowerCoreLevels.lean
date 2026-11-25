/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PowerLineLevels

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Extremal powered Bateman levels

[Kedia2013TyingKnots], Fig. 2. The squared modulus of the true complex
field-line label on the unit sphere is the radial function
`r^p (1-r)^q`, where `r = |α|²`. It has exactly one peak for positive
powers. Its value controls both projected labels, and saturation
identifies the radius and complex phase of the corresponding core level.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)

/-- Squared modulus of the powered product at first squared radius `r`. -/
def poweredRadiusProfile (p q : ℕ) (r : ℝ) : ℝ := r ^ p * (1 - r) ^ q

/-- The first squared radius at the peak of the powered radial profile. -/
noncomputable def poweredPeakRadius (p q : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) + (q : ℝ))

/-- The positive amplitude of the product label at its peak radius. -/
noncomputable def poweredPeakAmplitude (p q : ℕ) : ℝ :=
  Real.sqrt (poweredRadiusProfile p q (poweredPeakRadius p q))

/-- For positive exponents the peak radius lies strictly between the two axes. -/
theorem poweredPeakRadius_mem {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    poweredPeakRadius p q ∈ Ioo (0 : ℝ) 1 := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  unfold poweredPeakRadius
  exact ⟨div_pos hp' (by positivity), (div_lt_one (by positivity)).2 (by linarith)⟩

/-- The radial derivative consists of a nonnegative power factor times
a linear factor that changes sign exactly at the peak. -/
theorem deriv_poweredRadiusProfile_succ (m n : ℕ) (r : ℝ) :
    deriv (poweredRadiusProfile (m + 1) (n + 1)) r =
      (r ^ m * (1 - r) ^ n) * ((m : ℝ) + 1 - ((m : ℝ) + (n : ℝ) + 2) * r) := by
  have h₁ := (hasDerivAt_id r).pow (m + 1)
  have h₂ := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).pow (n + 1)
  have h := (h₁.mul h₂).deriv
  change deriv (poweredRadiusProfile (m + 1) (n + 1)) r = _ at h
  rw [h]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq, zero_sub]
  change ((m : ℝ) + 1) * r ^ m * 1 * (1 - r) ^ (n + 1) +
    r ^ (m + 1) * (((n : ℝ) + 1) * (1 - r) ^ n * -1) = _
  rw [pow_succ r m, pow_succ (1 - r) n]
  ring

/-- The profile increases strictly to its peak and decreases strictly
from there to the opposite axis. -/
theorem poweredRadiusProfile_monotone {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (poweredRadiusProfile p q) (Icc 0 (poweredPeakRadius p q)) ∧
      StrictAntiOn (poweredRadiusProfile p q) (Icc (poweredPeakRadius p q) 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  let peak := poweredPeakRadius (m + 1) (n + 1)
  have hpeak := poweredPeakRadius_mem hp hq
  change peak ∈ Ioo (0 : ℝ) 1 at hpeak
  have hct : Continuous (poweredRadiusProfile (m + 1) (n + 1)) := by
    unfold poweredRadiusProfile
    fun_prop
  have hsum : 0 < (m : ℝ) + (n : ℝ) + 2 := by positivity
  have hbalance : ((m : ℝ) + (n : ℝ) + 2) * peak = (m : ℝ) + 1 := by
    change ((m : ℝ) + (n : ℝ) + 2) * poweredPeakRadius (m + 1) (n + 1) = _
    unfold poweredPeakRadius
    push_cast
    field_simp
    ring
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hct.continuousOn
    intro r hr
    rw [interior_Icc] at hr
    have hr1 := hr.2.trans hpeak.2
    have hlin : 0 < (m : ℝ) + 1 - ((m : ℝ) + (n : ℝ) + 2) * r := by
      have hlt := mul_lt_mul_of_pos_left hr.2 hsum
      change ((m : ℝ) + (n : ℝ) + 2) * r < ((m : ℝ) + (n : ℝ) + 2) * peak at hlt
      linarith
    rw [deriv_poweredRadiusProfile_succ]
    exact mul_pos (mul_pos (pow_pos hr.1 _) (pow_pos (sub_pos.mpr hr1) _)) hlin
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hct.continuousOn
    intro r hr
    rw [interior_Icc] at hr
    have hr0 := hpeak.1.trans hr.1
    have hlin : (m : ℝ) + 1 - ((m : ℝ) + (n : ℝ) + 2) * r < 0 := by
      have hlt := mul_lt_mul_of_pos_left hr.1 hsum
      change ((m : ℝ) + (n : ℝ) + 2) * peak < ((m : ℝ) + (n : ℝ) + 2) * r at hlt
      linarith
    rw [deriv_poweredRadiusProfile_succ]
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos hr0 _) (pow_pos (sub_pos.mpr hr.2) _)) hlin

/-- The maximum is strict at every other radius on the unit sphere. -/
theorem poweredRadiusProfile_lt_peak {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hne : r ≠ poweredPeakRadius p q) :
    poweredRadiusProfile p q r < poweredRadiusProfile p q (poweredPeakRadius p q) := by
  have hpeak := poweredPeakRadius_mem hp hq
  have ⟨hleft, hright⟩ := poweredRadiusProfile_monotone hp hq
  rcases lt_or_gt_of_ne hne with hl | hgt
  · exact hleft ⟨hr.1, hl.le⟩ ⟨hpeak.1.le, le_rfl⟩ hl
  · exact hright ⟨le_rfl, hpeak.2.le⟩ ⟨hgt.le, hr.2⟩ hgt

/-- The amplitude is nonzero for positive powers. -/
theorem poweredPeakAmplitude_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < poweredPeakAmplitude p q := by
  have hk := poweredPeakRadius_mem hp hq
  exact Real.sqrt_pos.2 (mul_pos (pow_pos hk.1 _) (pow_pos (sub_pos.mpr hk.2) _))

/-- Squaring the amplitude gives exactly the peak radial value. -/
theorem poweredPeakAmplitude_sq {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    poweredPeakAmplitude p q ^ 2 = poweredRadiusProfile p q (poweredPeakRadius p q) := by
  have hk := poweredPeakRadius_mem hp hq
  exact Real.sq_sqrt (mul_nonneg (pow_nonneg hk.1.le _) (pow_nonneg (sub_nonneg.mpr hk.2.le) _))

/-- The product label on the unit sphere has the radial squared modulus. -/
theorem normSq_poweredProduct_on_sphere (p q : ℕ) {α β : ℂ}
    (h : Complex.normSq α + Complex.normSq β = 1) :
    Complex.normSq (α ^ p * β ^ q) = poweredRadiusProfile p q (Complex.normSq α) := by
  rw [map_mul, map_pow, map_pow, poweredRadiusProfile, show Complex.normSq β = 1 - Complex.normSq α by linarith]

/-- The squared modulus reaches the peak exactly at the peak radius,
independently of the phase on that torus. -/
theorem normSq_poweredProduct_eq_peak_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {α β : ℂ} (h : Complex.normSq α + Complex.normSq β = 1) :
    Complex.normSq (α ^ p * β ^ q) = poweredPeakAmplitude p q ^ 2 ↔
      Complex.normSq α = poweredPeakRadius p q := by
  rw [normSq_poweredProduct_on_sphere p q h, poweredPeakAmplitude_sq hp hq]
  constructor
  · intro he
    by_contra hne
    have hr : Complex.normSq α ∈ Icc (0 : ℝ) 1 :=
      ⟨Complex.normSq_nonneg α, by linarith [Complex.normSq_nonneg β]⟩
    exact (poweredRadiusProfile_lt_peak hp hq hr hne).ne he
  · intro he
    rw [he]

/-- The physical complex label never exceeds the amplitude on any
space-time slice. -/
theorem norm_poweredProductLabel_le_peak {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x y z t : ℝ) :
    ‖poweredProductLabel p q x y z t‖ ≤ poweredPeakAmplitude p q := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (poweredPeakAmplitude_pos hp hq).le
  rw [← Complex.normSq_eq_norm_sq, poweredProductLabel,
    normSq_poweredProduct_on_sphere p q (complex_rational_pair_unit x y z t),
    poweredPeakAmplitude_sq hp hq]
  let r := Complex.normSq (rationalAlpha x y z t)
  change poweredRadiusProfile p q r ≤ poweredRadiusProfile p q (poweredPeakRadius p q)
  by_cases he : r = poweredPeakRadius p q
  · rw [he]
  · have hu := complex_rational_pair_unit x y z t
    have hr : r ∈ Icc (0 : ℝ) 1 :=
      ⟨Complex.normSq_nonneg _, by dsimp [r]; linarith [Complex.normSq_nonneg (rationalBeta x y z t)]⟩
    exact (poweredRadiusProfile_lt_peak hp hq hr he).le

/-- At a positive or negative extremal real label the imaginary part
vanishes and the point lies over exactly the peak-radius torus. -/
theorem poweredProductLabel_real_extreme {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x y z t : ℝ) (he : |(poweredProductLabel p q x y z t).re| = poweredPeakAmplitude p q) :
    (poweredProductLabel p q x y z t).im = 0 ∧
      Complex.normSq (rationalAlpha x y z t) = poweredPeakRadius p q := by
  let z₀ := poweredProductLabel p q x y z t
  have hnorm := norm_poweredProductLabel_le_peak hp hq x y z t
  have h₁ : Complex.normSq z₀ ≤ poweredPeakAmplitude p q ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg z₀) hnorm 2
  have h₂ : z₀.re ^ 2 = poweredPeakAmplitude p q ^ 2 := by rw [← sq_abs, he]
  have hi : z₀.im = 0 := by
    rw [Complex.normSq_apply] at h₁
    nlinarith [sq_nonneg z₀.im]
  have hn : Complex.normSq z₀ = poweredPeakAmplitude p q ^ 2 := by
    rw [Complex.normSq_apply, hi]
    nlinarith
  exact ⟨hi, (normSq_poweredProduct_eq_peak_iff hp hq (complex_rational_pair_unit x y z t)).1 hn⟩

/-- At a positive or negative extremal imaginary label the real part
vanishes and the point has the same peak radius. -/
theorem poweredProductLabel_imaginary_extreme {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x y z t : ℝ) (he : |(poweredProductLabel p q x y z t).im| = poweredPeakAmplitude p q) :
    (poweredProductLabel p q x y z t).re = 0 ∧
      Complex.normSq (rationalAlpha x y z t) = poweredPeakRadius p q := by
  let z₀ := poweredProductLabel p q x y z t
  have hnorm := norm_poweredProductLabel_le_peak hp hq x y z t
  have h₁ : Complex.normSq z₀ ≤ poweredPeakAmplitude p q ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg z₀) hnorm 2
  have h₂ : z₀.im ^ 2 = poweredPeakAmplitude p q ^ 2 := by rw [← sq_abs, he]
  have hr : z₀.re = 0 := by
    rw [Complex.normSq_apply] at h₁
    nlinarith [sq_nonneg z₀.re]
  have hn : Complex.normSq z₀ = poweredPeakAmplitude p q ^ 2 := by
    rw [Complex.normSq_apply, hr]
    nlinarith
  exact ⟨hr, (normSq_poweredProduct_eq_peak_iff hp hq (complex_rational_pair_unit x y z t)).1 hn⟩

end Qatlib.Papers.KnotLight13.TorusFamily
