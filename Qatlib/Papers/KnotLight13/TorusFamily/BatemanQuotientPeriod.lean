/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanQuotientAngle
public import Qatlib.Papers.KnotLight13.TorusFamily.PoweredSphereTori
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The period of the Bateman magnetic quotient

[Kedia2013TyingKnots], discussion of Fig. 2.
Each full normalized magnetic trajectory on a strict intermediate level
projects to a complete periodic lap of the quotient. The period is the
integral of reciprocal angular speed over a full turn and is independent
of the phase of the point in the fiber.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open scoped Interval

/-- A continuous scalar rate has a primitive starting at zero. -/
private theorem hasDerivAt_integral_from_zero {a : ℝ → ℝ} (ha : Continuous a) (s : ℝ) :
    HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, a u) (a s) s :=
  intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt

/-- Integrating the angular speed gives the exact phase of a unit-circle
trajectory. The exponential factor with opposite phase has zero derivative. -/
theorem batemanCircle_phase_integral (u : ℝ → Circle) (a : ℝ → ℝ) (ha : Continuous a)
    (hu : ∀ t, HasDerivAt (fun s => (u s : ℂ))
      (Complex.I * (a t : ℂ) * (u t : ℂ)) t) (t : ℝ) :
    u t = u 0 * Circle.exp (∫ s in (0 : ℝ)..t, a s) := by
  let A := fun t : ℝ => ∫ s in (0 : ℝ)..t, a s
  let F := fun t : ℝ => Complex.exp (-(A t : ℂ) * Complex.I) * (u t : ℂ)
  have hA (s : ℝ) : HasDerivAt A (a s) s := hasDerivAt_integral_from_zero ha s
  have hF (s : ℝ) : HasDerivAt F 0 s := by
    have hC := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hA s)
    have hg : HasDerivAt (fun t => -(A t : ℂ) * Complex.I)
        (-(a s : ℂ) * Complex.I) s := hC.neg.mul_const _
    have he := hg.cexp.mul (hu s)
    convert he using 1
    ring
  have hConst := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  have h0 : A 0 = 0 := intervalIntegral.integral_same
  change Complex.exp (-(A t : ℂ) * Complex.I) * (u t : ℂ) =
    Complex.exp (-(A 0 : ℂ) * Complex.I) * (u 0 : ℂ) at hConst
  rw [h0, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] at hConst
  apply Circle.ext
  change (u t : ℂ) = (u 0 : ℂ) * Complex.exp ((A t : ℂ) * Complex.I)
  rw [← hConst]
  calc
    _ = _ := by
      have he : Complex.exp (-(A t : ℂ) * Complex.I) * Complex.exp ((A t : ℂ) * Complex.I) = 1 := by
        rw [← Complex.exp_add, show -(A t : ℂ) * Complex.I + (A t : ℂ) * Complex.I = 0 by ring,
          Complex.exp_zero]
      linear_combination -(u t : ℂ) * he

/-- For positive continuous angular speed on the circle, the time to
return to the initial phase is one integral of reciprocal speed.
Every global trajectory is periodic with this period, reaches all
phases, and visits each phase at most once in the first half-open lap. -/
theorem batemanCircle_one_lap_of_positive_speed (u : ℝ → Circle) (ω : Circle → ℝ)
    (hω : Continuous ω) (hpos : ∀ z, 0 < ω z)
    (hu : ∀ t, HasDerivAt (fun s => (u s : ℂ))
      (Complex.I * (ω (u t) : ℂ) * (u t : ℂ)) t) :
    let T := ∫ v in (0 : ℝ)..(2 * Real.pi), (ω (u 0 * Circle.exp v))⁻¹
    0 < T ∧ Function.Periodic u T ∧ Function.Surjective u ∧ Set.InjOn u (Set.Ico 0 T) := by
  let P := 2 * Real.pi
  let a := fun t => ω (u t)
  let b := fun v => (ω (u 0 * Circle.exp v))⁻¹
  let A := fun t : ℝ => ∫ s in (0 : ℝ)..t, a s
  let B := fun v : ℝ => ∫ s in (0 : ℝ)..v, b s
  have hU : Continuous u := by
    apply continuous_induced_rng.2
    exact (show Differentiable ℝ (fun s => (u s : ℂ)) from fun s =>
      (hu s).differentiableAt).continuous
  have ha : Continuous a := hω.comp hU
  have hb : Continuous b := (hω.comp (continuous_const.mul Circle.exp.continuous)).inv₀
    (fun v => (hpos (u 0 * Circle.exp v)).ne')
  have hA (s : ℝ) : HasDerivAt A (a s) s := hasDerivAt_integral_from_zero ha s
  have hB (v : ℝ) : HasDerivAt B (b v) v := hasDerivAt_integral_from_zero hb v
  have hA₀ : A 0 = 0 := intervalIntegral.integral_same
  have hB₀ : B 0 = 0 := intervalIntegral.integral_same
  have hmono : StrictMono B :=
    strictMono_of_hasDerivAt_pos hB (fun v => inv_pos.mpr (hpos _))
  have hphase (s : ℝ) : u s = u 0 * Circle.exp (A s) :=
    batemanCircle_phase_integral u a ha hu s
  have hInverse : Function.LeftInverse B A := by
    have hD (s : ℝ) : HasDerivAt (fun t => B (A t) - t) 0 s := by
      have hs := ((hB (A s)).comp s (hA s)).fun_sub (hasDerivAt_id s)
      have hprod : b (A s) * a s = 1 := by
        change (ω (u 0 * Circle.exp (A s)))⁻¹ * ω (u s) = 1
        rw [← hphase s, inv_mul_cancel₀ (hpos _).ne']
      simpa only [Function.comp_apply, id_eq, hprod, sub_self] using hs
    intro s
    have hconst := is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
      (fun t => (hD t).deriv) s 0
    change B (A s) - s = B (A 0) - 0 at hconst
    rw [hA₀, hB₀, sub_zero, sub_eq_zero] at hconst
    exact hconst
  have hShift (v : ℝ) : B (v + P) = B v + B P := by
    have hbper : Function.Periodic b P := by
      intro x
      change (ω (u 0 * Circle.exp (x + P)))⁻¹ = _
      rw [show Circle.exp (x + P) = Circle.exp x from Circle.periodic_exp x]
    have hD (x : ℝ) : HasDerivAt (fun y => B (y + P) - B y) 0 x := by
      have h₂ := ((hB (x + P)).comp x ((hasDerivAt_id x).add_const P)).fun_sub (hB x)
      simpa only [id_eq, mul_one, Function.comp_apply, hbper x, sub_self] using h₂
    have hconst := is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
      (fun t => (hD t).deriv) v 0
    change B (v + P) - B v = B (0 + P) - B 0 at hconst
    rw [zero_add, hB₀, sub_zero] at hconst
    linarith
  have hAs (s : ℝ) : A (s + B P) = A s + P := by
    apply hmono.injective
    rw [hInverse, hShift, hInverse]
  change 0 < B P ∧ Function.Periodic u (B P) ∧ Function.Surjective u ∧ Set.InjOn u (Set.Ico 0 (B P))
  refine ⟨by simpa only [hB₀] using hmono (Real.two_pi_pos : 0 < P), ?_, ?_, ?_⟩
  · intro s
    rw [hphase (s + B P), hAs s, show Circle.exp (A s + P) = Circle.exp (A s)
      from Circle.periodic_exp (A s), ← hphase s]
  · intro z
    obtain ⟨v, hv⟩ := Circle.exp_surjective ((u 0)⁻¹ * z)
    have hAB : A (B v) = v := hmono.injective (hInverse (B v))
    refine ⟨B v, ?_⟩
    rw [hphase (B v), hAB, hv, mul_inv_cancel_left]

  · have hmonoA : StrictMono A := strictMono_of_hasDerivAt_pos hA (fun t => hpos (u t))
    have hAP : A (B P) = P := hmono.injective (hInverse (B P))
    have hmem (s : ℝ) (hs : s ∈ Set.Ico 0 (B P)) : A s ∈ Set.Ico 0 P := by
      exact ⟨hA₀ ▸ hmonoA.monotone hs.1, hAP ▸ hmonoA hs.2⟩
    intro s hs t ht hEq
    rw [hphase s, hphase t] at hEq
    apply hmonoA.injective
    exact (Circle.exp_injOn_Ico (by simp [P])) (hmem s hs) (hmem t ht) (mul_left_cancel hEq)

/-- For positive continuous angular speed on the circle, the time to
return to the initial phase is one integral of reciprocal speed.
Every global trajectory is periodic with this period and reaches
all phases. -/
theorem batemanCircle_period_of_positive_speed (u : ℝ → Circle) (ω : Circle → ℝ)
    (hω : Continuous ω) (hpos : ∀ z, 0 < ω z)
    (hu : ∀ t, HasDerivAt (fun s => (u s : ℂ))
      (Complex.I * (ω (u t) : ℂ) * (u t : ℂ)) t) :
    let T := ∫ v in (0 : ℝ)..(2 * Real.pi), (ω (u 0 * Circle.exp v))⁻¹
    0 < T ∧ Function.Periodic u T ∧ Function.Surjective u := by
  obtain ⟨hT, hp, hs, _⟩ := batemanCircle_one_lap_of_positive_speed u ω hω hpos hu
  exact ⟨hT, hp, hs⟩

/-- Integrating the reciprocal speed over a full revolution is
independent of the initial point on the circle. -/
theorem batemanCircle_period_integral_eq (ω : Circle → ℝ) (u : Circle) :
    (∫ v in (0 : ℝ)..(2 * Real.pi), (ω (u * Circle.exp v))⁻¹) =
      ∫ v in (0 : ℝ)..(2 * Real.pi), (ω (Circle.exp v))⁻¹ := by
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective u
  let b := fun v : ℝ => (ω (Circle.exp v))⁻¹
  have hp : Function.Periodic b (2 * Real.pi) := by
    intro x
    dsimp only [b]
    rw [Circle.periodic_exp x]
  calc
    _ = ∫ v in (0 : ℝ)..(2 * Real.pi), b (v + θ) := by
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only [b]
      rw [Circle.exp_add, mul_comm]
    _ = _ := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * Real.pi),
        hp.intervalIntegral_add_eq θ 0, zero_add]

/-- One full lap of the normalized magnetic quotient. The integral
uses geometric angle and is independent of the starting fiber or phase. -/
noncomputable def batemanMagneticQuotientPeriod {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) : ℝ :=
  let e := batemanMagneticOvalHomeomorph hp hq h₀ hc
  ∫ v in (0 : ℝ)..(2 * Real.pi), (batemanMagneticOvalSpeed p q (e.symm (Circle.exp v)).val)⁻¹

/-- The actual normalized sphere trajectories project periodically
onto the whole quotient oval, visiting it once per half-open lap. -/
theorem batemanMagneticQuotient_one_lap
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) {w : ℝ → ℂ × ℂ}
    (hw : ∀ t, HasDerivAt w (batemanSphereMagnetic p q (w t)) t)
    (hlevel : ∀ t, w t ∈ poweredSphereRealLevel p q c) :
    let T := batemanMagneticQuotientPeriod hp hq h₀ hc
    0 < T ∧
      Function.Periodic (fun t => batemanMagneticQuotient p q (w t)) T ∧
      Set.range (fun t => batemanMagneticQuotient p q (w t)) = batemanMagneticOval p q c ∧
      Set.InjOn (fun t => batemanMagneticQuotient p q (w t)) (Set.Ico 0 T) := by
  let e := batemanMagneticOvalHomeomorph hp hq h₀ hc
  let z := fun t => batemanMagneticQuotient p q (w t)
  have hz (t : ℝ) : z t ∈ batemanMagneticOval p q c := by
    exact (hlevel t).2 ▸ batemanMagneticQuotient_mem_oval p q (w t) (hlevel t).1
  let Z := fun t => (⟨z t, hz t⟩ : ↥(batemanMagneticOval p q c))
  let u := fun t => e (Z t)
  let ω := fun v => batemanMagneticOvalSpeed p q (e.symm v).val
  have hω : Continuous ω := (continuous_batemanMagneticOvalSpeed hp hq hc).comp e.symm.continuous
  have hpω (v : Circle) : 0 < ω v :=
    batemanMagneticOvalSpeed_pos hp hq h₀ hc (e.symm v).property
  have hSpeed (t : ℝ) : ω (u t) = batemanMagneticOvalSpeed p q (z t) := by
    change batemanMagneticOvalSpeed p q (e.symm (e (Z t))).val = _
    rw [e.symm_apply_apply]
  have hPhase (t : ℝ) :
      HasDerivAt (fun s => (u s : ℂ)) (Complex.I * (ω (u t) : ℂ) * (u t : ℂ)) t := by
    rw [hSpeed]
    exact hasDerivAt_batemanMagneticOvalPhase hp hq hc (hw t) (hlevel t).1 hz
  have h := batemanCircle_one_lap_of_positive_speed u ω hω hpω hPhase
  dsimp only at h
  rw [batemanCircle_period_integral_eq ω (u 0)] at h
  obtain ⟨hT, hper, hsurj, hinj⟩ := h
  refine ⟨hT, fun t => congrArg Subtype.val (e.injective (hper t)), ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨t, rfl⟩
      exact hz t
    · intro hv
      obtain ⟨t, ht⟩ := hsurj (e ⟨v, hv⟩)
      exact ⟨t, congrArg Subtype.val (e.injective ht)⟩
  · intro s hs t ht hEq
    exact hinj hs ht (congrArg e (Subtype.ext hEq))

/-- The actual normalized sphere trajectories project periodically
onto the whole quotient oval, with a shared positive lap time. -/
theorem batemanMagneticQuotient_periodic
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {c : ℝ}
    (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) {w : ℝ → ℂ × ℂ}
    (hw : ∀ t, HasDerivAt w (batemanSphereMagnetic p q (w t)) t)
    (hlevel : ∀ t, w t ∈ poweredSphereRealLevel p q c) :
    let T := batemanMagneticQuotientPeriod hp hq h₀ hc
    0 < T ∧
      Function.Periodic (fun t => batemanMagneticQuotient p q (w t)) T ∧
      Set.range (fun t => batemanMagneticQuotient p q (w t)) = batemanMagneticOval p q c := by
  obtain ⟨hT, hper, hrange, _⟩ := batemanMagneticQuotient_one_lap hp hq h₀ hc hw hlevel
  exact ⟨hT, hper, hrange⟩

end Qatlib.Papers.KnotLight13.TorusFamily
