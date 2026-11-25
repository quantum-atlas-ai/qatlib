/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PowerCoreLevels

import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# A monotone radial coordinate for the powered Bateman levels

The signed square root of the deficit below the maximal squared label
modulus is an increasing coordinate across the product torus. With
this coordinate, a nonextremal fixed real or imaginary label reduces
to a round circle in the two-dimensional radial and phase quotient.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)

/-- The deficit in squared modulus relative to the peak. -/
noncomputable def poweredRadialDeficit (p q : ℕ) (r : ℝ) : ℝ :=
  poweredPeakAmplitude p q ^ 2 - poweredRadiusProfile p q r

/-- The square root of the deficit with the sign of the side of the peak. -/
noncomputable def poweredRadialHeight (p q : ℕ) (r : ℝ) : ℝ :=
  if r ≤ poweredPeakRadius p q then -Real.sqrt (poweredRadialDeficit p q r)
  else Real.sqrt (poweredRadialDeficit p q r)

/-- The deficit is nonnegative on the unit radial interval. -/
private theorem poweredRadialDeficit_nonneg {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) : 0 ≤ poweredRadialDeficit p q r := by
  unfold poweredRadialDeficit
  rw [poweredPeakAmplitude_sq hp hq]
  apply sub_nonneg.mpr
  rcases eq_or_ne r (poweredPeakRadius p q) with h | h
  · rw [h]
  · exact (poweredRadiusProfile_lt_peak hp hq hr h).le

/-- The square of the new coordinate is exactly the deficit. -/
theorem poweredRadialHeight_sq {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    poweredRadialHeight p q r ^ 2 = poweredPeakAmplitude p q ^ 2 - poweredRadiusProfile p q r := by
  have hh := Real.sq_sqrt (poweredRadialDeficit_nonneg hp hq hr)
  change _ = poweredRadialDeficit p q r
  unfold poweredRadialHeight
  split
  · simpa only [neg_sq] using hh
  · exact hh

/-- The signed root is continuous across the peak where both branches vanish. -/
theorem continuous_poweredRadialHeight {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Continuous (poweredRadialHeight p q) := by
  have hcont : Continuous (fun r => Real.sqrt (poweredRadialDeficit p q r)) := by
    unfold poweredRadialDeficit poweredRadiusProfile
    fun_prop
  unfold poweredRadialHeight
  refine hcont.neg.if_le hcont continuous_id continuous_const ?_
  intro r hr
  change r = poweredPeakRadius p q at hr
  simp [hr, poweredRadialDeficit, poweredPeakAmplitude_sq hp hq]

/-- The signed root increases strictly from the first axis to the second. -/
theorem strictMonoOn_poweredRadialHeight {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    StrictMonoOn (poweredRadialHeight p q) (Icc (0 : ℝ) 1) := by
  have hpeak := poweredPeakRadius_mem hp hq
  obtain ⟨hinc, hdec⟩ := poweredRadiusProfile_monotone hp hq
  intro r hr s hs hrs
  by_cases h₁ : s ≤ poweredPeakRadius p q
  · have hr' := hrs.le.trans h₁
    have hlt := hinc ⟨hr.1, hr'⟩ ⟨hs.1, h₁⟩ hrs
    have hrl : poweredRadialDeficit p q s < poweredRadialDeficit p q r := by
      unfold poweredRadialDeficit
      linarith
    simpa only [poweredRadialHeight, ite_eq_left hr', ite_eq_left h₁, neg_lt_neg_iff] using
      Real.sqrt_lt_sqrt (poweredRadialDeficit_nonneg hp hq hs) hrl
  · rcases le_or_gt r (poweredPeakRadius p q) with h₂ | h₂
    · have hs' : s ≠ poweredPeakRadius p q := (lt_of_not_ge h₁).ne'
      have hlt := poweredRadiusProfile_lt_peak hp hq hs hs'
      have hd : 0 < poweredRadialDeficit p q s := by
        unfold poweredRadialDeficit
        rw [poweredPeakAmplitude_sq hp hq]
        exact sub_pos.mpr hlt
      simp only [poweredRadialHeight, ite_eq_left h₂, ite_eq_right h₁]
      exact (neg_nonpos.mpr (Real.sqrt_nonneg _)).trans_lt (Real.sqrt_pos.2 hd)
    · have h₂' := not_le.mpr h₂
      have hlt := hdec ⟨h₂.le, hr.2⟩ ⟨(lt_of_not_ge h₁).le, hs.2⟩ hrs
      have hrl : poweredRadialDeficit p q r < poweredRadialDeficit p q s := by
        unfold poweredRadialDeficit
        linarith
      simpa only [poweredRadialHeight, ite_eq_right h₁, ite_eq_right h₂'] using
        Real.sqrt_lt_sqrt (poweredRadialDeficit_nonneg hp hq hr) hrl

/-- The two boundary points of the radial interval map to opposite endpoints. -/
theorem poweredRadialHeight_endpoints {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    poweredRadialHeight p q 0 = -poweredPeakAmplitude p q ∧
      poweredRadialHeight p q 1 = poweredPeakAmplitude p q := by
  have hpeak := poweredPeakRadius_mem hp hq
  have hA : 0 ≤ poweredPeakAmplitude p q := (poweredPeakAmplitude_pos hp hq).le
  constructor
  · simp [poweredRadialHeight, hpeak.1.le, poweredRadialDeficit, poweredRadiusProfile,
      zero_pow hp.ne', Real.sqrt_sq hA]
  · simp [poweredRadialHeight, not_le.mpr hpeak.2, poweredRadialDeficit, poweredRadiusProfile,
      zero_pow hq.ne', Real.sqrt_sq hA]

/-- The closed radial interval is homeomorphic to the interval between
the signed amplitudes by the explicit signed deficit coordinate. -/
noncomputable def poweredRadialHeightHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ↥(Icc (0 : ℝ) 1) ≃ₜ ↥(Icc (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q)) := by
  let H := poweredRadialHeight p q
  have hcont := continuous_poweredRadialHeight hp hq
  have hmono := strictMonoOn_poweredRadialHeight hp hq
  obtain ⟨h0, h1⟩ := poweredRadialHeight_endpoints hp hq
  have him : H '' Icc (0 : ℝ) 1 = Icc (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q) := by
    rw [hcont.continuousOn.image_Icc_of_monotoneOn (by norm_num : (0 : ℝ) ≤ 1) hmono.monotoneOn]
    exact congrArg₂ Icc h0 h1
  let f : ↥(Icc (0 : ℝ) 1) → ↥(Icc (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q)) :=
    fun r => ⟨H r, him ▸ mem_image_of_mem H r.property⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y.val ∈ H '' Icc (0 : ℝ) 1 := by rw [him]; exact y.property
    obtain ⟨r, hr, h⟩ := hy
    exact ⟨⟨r, hr⟩, Subtype.ext h⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨fun u v h => Subtype.ext (hmono.injOn u.property v.property
      (congrArg Subtype.val h)), hsurj⟩) ((hcont.comp continuous_subtype_val).subtype_mk _)

/-- The inverse radial chart has the prescribed height. -/
theorem poweredRadialHeight_inverse_apply {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (u : ↥(Icc (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q))) :
    poweredRadialHeight p q ((poweredRadialHeightHomeomorph hp hq).symm u : ℝ) = u := by
  exact congrArg Subtype.val ((poweredRadialHeightHomeomorph hp hq).apply_symm_apply u)

/-- An interior height comes from an interior radius. -/
theorem poweredRadialHeight_inverse_mem_Ioo {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {u : ↥(Icc (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q))}
    (hu : u.val ∈ Ioo (-poweredPeakAmplitude p q) (poweredPeakAmplitude p q)) :
    ((poweredRadialHeightHomeomorph hp hq).symm u : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  let r := (poweredRadialHeightHomeomorph hp hq).symm u
  have he : poweredRadialHeight p q r.val = u := poweredRadialHeight_inverse_apply hp hq u
  have hh := poweredRadialHeight_endpoints hp hq
  constructor
  · apply lt_of_le_of_ne r.property.1
    intro h
    rw [← h, hh.1] at he
    exact hu.1.ne he
  · apply lt_of_le_of_ne r.property.2
    intro h
    rw [h, hh.2] at he
    exact hu.2.ne he.symm

/-- The radial coordinate and imaginary part on the unit sphere lie on
the exact circle associated with the real part. -/
theorem poweredSphereProduct_radial_circle {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {α β : ℂ} (hs : Complex.normSq α + Complex.normSq β = 1) :
    let g := α ^ p * β ^ q
    poweredRadialHeight p q (Complex.normSq α) ^ 2 + g.im ^ 2 =
      poweredPeakAmplitude p q ^ 2 - g.re ^ 2 := by
  dsimp only
  have hr : Complex.normSq α ∈ Icc (0 : ℝ) 1 := by
    exact ⟨Complex.normSq_nonneg _, by linarith [Complex.normSq_nonneg β]⟩
  rw [poweredRadialHeight_sq hp hq hr, ← normSq_poweredProduct_on_sphere p q hs, Complex.normSq_apply]
  ring

/-- Every physical label obeys the same quotient-circle equation. -/
theorem poweredProduct_radial_circle {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x y z t : ℝ) :
    let g := poweredProductLabel p q x y z t
    poweredRadialHeight p q (Complex.normSq (rationalAlpha x y z t)) ^ 2 + g.im ^ 2 =
      poweredPeakAmplitude p q ^ 2 - g.re ^ 2 :=
  poweredSphereProduct_radial_circle hp hq (complex_rational_pair_unit x y z t)

end Qatlib.Papers.KnotLight13.TorusFamily
