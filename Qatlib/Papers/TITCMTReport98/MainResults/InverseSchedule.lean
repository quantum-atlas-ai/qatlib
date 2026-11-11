/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.GammaModulus
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Inverse-schedule amplitude and limiting weight

This module evaluates the squared norm of the explicit two-mode amplitude
`inverseScheduleAsymptoticAmplitude` from the inverse-schedule analysis of
[KadowakiNishimori1998]. The result reproduces `inverseScheduleDisplayedWeight` through its
oscillatory bracket.

It proves large-time limits for the displayed weight and complement, rewrites the leading weight
as a logistic expression, and establishes its exponential equivalent as the schedule parameter
grows.

## Main statements

* `inverseSchedule_modulus_sq_eq15`: computes the squared norm of the two-mode expression.
* `inverseSchedule_displayed_complement_tendsto`: gives the large-time complement limit.
* `inverseSchedule_logistic_tail_asymptotic`: gives the exponential equivalent of the logistic
  tail.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Complex Filter
open scoped Topology

/-- The inverse-schedule bracket containing an exponential constant, an oscillatory `1 / t`
term, and a `1 / t ^ 2` term. -/
def inverseScheduleBracket (h c t : ℝ) : ℝ :=
  Real.exp (-(Real.pi * c)) + c * Real.cos (2 * h * t) / (h * t)
    + c ^ 2 * Real.exp (Real.pi * c) / (4 * h ^ 2 * t ^ 2)

/-- The explicit sum of two oscillatory exponential terms multiplied by `inverseScheduleCoeff h
c`. -/
def inverseScheduleAsymptoticAmplitude (h c : ℝ) (t : ℝ) : ℂ :=
  inverseScheduleCoeff h c *
    (Complex.exp (-(I * (h : ℂ) * (t : ℂ)) - (Real.pi * (c : ℂ)) / 2)
      + (c : ℂ) * Complex.exp (I * (h : ℂ) * (t : ℂ) + (Real.pi * (c : ℂ)) / 2)
          / (2 * (h : ℂ) * (t : ℂ)))

/-- The square of `exp a` equals `exp (2 * a)`. -/
theorem exp_sq (a : ℝ) : Real.exp a ^ 2 = Real.exp (2 * a) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- The product `exp (-a) * exp a` equals one. -/
theorem exp_neg_mul_exp (a : ℝ) : Real.exp (-a) * Real.exp a = 1 := by
  rw [← Real.exp_add]
  simp

/-- The squared norm of `X * exp (-iθ) + Y * exp (iθ)` for real `X` and `Y` equals `X ^ 2 + Y ^
2 + 2XY * cos (2θ)`. -/
theorem twoMode_modulus_sq (X Y θ : ℝ) :
    ‖(X : ℂ) * Complex.exp (-(θ : ℂ) * I) + (Y : ℂ) * Complex.exp ((θ : ℂ) * I)‖ ^ 2
      = X ^ 2 + Y ^ 2 + 2 * X * Y * Real.cos (2 * θ) := by
  have hu : Complex.exp (-(θ : ℂ) * I)
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    rw [show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hv : Complex.exp ((θ : ℂ) * I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsplit :
      (X : ℂ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I)
        + (Y : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)
      = ((X * Real.cos θ + Y * Real.cos θ : ℝ) : ℂ)
        + ((Y * Real.sin θ - X * Real.sin θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [Complex.sq_norm, hu, hv, hsplit, Complex.normSq_add_mul_I, Real.cos_two_mul]
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have key : (X * Real.cos θ + Y * Real.cos θ) ^ 2
        + (Y * Real.sin θ - X * Real.sin θ) ^ 2
        - (X ^ 2 + Y ^ 2 + 2 * X * Y * (2 * Real.cos θ ^ 2 - 1))
      = (X ^ 2 + Y ^ 2 - 2 * X * Y) * (Real.cos θ ^ 2 + Real.sin θ ^ 2 - 1) := by
    ring
  linear_combination key + (X ^ 2 + Y ^ 2 - 2 * X * Y) * hcs

/-- Separates the real exponential amplitudes from the two oscillatory phases in the
inverse-schedule expression. -/
theorem inverseSchedule_amplitude_factor (h c t : ℝ) :
    Complex.exp (-(I * (h : ℂ) * (t : ℂ)) - (Real.pi * (c : ℂ)) / 2)
        + (c : ℂ) * Complex.exp (I * (h : ℂ) * (t : ℂ) + (Real.pi * (c : ℂ)) / 2)
            / (2 * (h : ℂ) * (t : ℂ))
      = (Real.exp (-(Real.pi * c) / 2) : ℂ) * Complex.exp (-(((h * t : ℝ)) : ℂ) * I)
        + ((c * Real.exp ((Real.pi * c) / 2) / (2 * h * t) : ℝ) : ℂ)
            * Complex.exp ((((h * t : ℝ)) : ℂ) * I) := by
  have e1 : Complex.exp (-(I * (h : ℂ) * (t : ℂ)) - (Real.pi * (c : ℂ)) / 2)
      = (Real.exp (-(Real.pi * c) / 2) : ℂ) * Complex.exp (-(((h * t : ℝ)) : ℂ) * I) := by
    rw [show -(I * (h : ℂ) * (t : ℂ)) - (Real.pi * (c : ℂ)) / 2
          = ((-(Real.pi * c) / 2 : ℝ) : ℂ) + (-(((h * t : ℝ)) : ℂ) * I) by
        push_cast
        ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
  have e2 : (c : ℂ) * Complex.exp (I * (h : ℂ) * (t : ℂ) + (Real.pi * (c : ℂ)) / 2)
        / (2 * (h : ℂ) * (t : ℂ))
      = ((c * Real.exp ((Real.pi * c) / 2) / (2 * h * t) : ℝ) : ℂ)
          * Complex.exp ((((h * t : ℝ)) : ℂ) * I) := by
    rw [show I * (h : ℂ) * (t : ℂ) + (Real.pi * (c : ℂ)) / 2
          = ((Real.pi * c / 2 : ℝ) : ℂ) + ((((h * t : ℝ)) : ℂ) * I) by
        push_cast
        ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    field_simp
  rw [e1, e2]

/-- For positive `h`, `c`, and `t`, the squared norm of the explicit asymptotic amplitude equals
`sinh (πc) / sinh (2πc)` times `inverseScheduleBracket h c t` [KadowakiNishimori1998]. -/
theorem inverseSchedule_modulus_sq_eq15 (h c t : ℝ) (hh : 0 < h) (hc : 0 < c) (ht : 0 < t) :
    ‖inverseScheduleAsymptoticAmplitude h c t‖ ^ 2
      = Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c)
          * inverseScheduleBracket h c t := by
  unfold inverseScheduleAsymptoticAmplitude
  rw [inverseSchedule_amplitude_factor h c t, norm_mul, mul_pow,
    inverseScheduleCoeff_norm_sq h c hh hc]
  congr 1
  rw [twoMode_modulus_sq]
  rw [show 2 * (h * t) = 2 * h * t by ring]
  have hX2 : Real.exp (-(Real.pi * c) / 2) ^ 2 = Real.exp (-(Real.pi * c)) := by
    rw [exp_sq]; congr 1; ring
  have hY2 : (c * Real.exp ((Real.pi * c) / 2) / (2 * h * t)) ^ 2
      = c ^ 2 * Real.exp (Real.pi * c) / (4 * h ^ 2 * t ^ 2) := by
    have hexp : Real.exp ((Real.pi * c) / 2) ^ 2 = Real.exp (Real.pi * c) := by
      rw [exp_sq]; congr 1; ring
    rw [div_pow, mul_pow, hexp]
    ring
  have hXY : 2 * Real.exp (-(Real.pi * c) / 2) * (c * Real.exp ((Real.pi * c) / 2) / (2 * h * t))
      = c / (h * t) := by
    have hmul : Real.exp (-(Real.pi * c) / 2) * Real.exp ((Real.pi * c) / 2) = 1 := by
      rw [← Real.exp_add]
      have hsum : -(Real.pi * c) / 2 + Real.pi * c / 2 = 0 := by ring
      rw [hsum, Real.exp_zero]
    calc 2 * Real.exp (-(Real.pi * c) / 2)
            * (c * Real.exp ((Real.pi * c) / 2) / (2 * h * t))
        = (Real.exp (-(Real.pi * c) / 2) * Real.exp ((Real.pi * c) / 2))
            * (c / (h * t)) := by
          field_simp
      _ = 1 * (c / (h * t)) := by rw [hmul]
      _ = c / (h * t) := by ring
  rw [hX2, hY2, hXY]
  unfold inverseScheduleBracket
  ring

/-- The displayed inverse-schedule weight equals the hyperbolic-sine prefactor times
`inverseScheduleBracket`. -/
theorem inverseScheduleDisplayedWeight_eq_bracket (h c t : ℝ) :
    inverseScheduleDisplayedWeight h c t
      = Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c)
          * inverseScheduleBracket h c t := rfl

/-- For positive `h`, the inverse-schedule bracket tends to `exp (-πc)` as time tends to
infinity. -/
theorem inverseScheduleBracket_tendsto (h c : ℝ) (hh : 0 < h) :
    Tendsto (fun t : ℝ => inverseScheduleBracket h c t) atTop
      (𝓝 (Real.exp (-(Real.pi * c)))) := by
  have hhne : h ≠ 0 := ne_of_gt hh

  have hcos : Tendsto (fun t : ℝ => c * Real.cos (2 * h * t) / (h * t)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun t : ℝ => Real.cos (2 * h * t) / t) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (f := fun t : ℝ => ‖Real.cos (2 * h * t) / t‖)
        (g := fun t : ℝ => 1 / t) ?_ ?_ ?_
      · filter_upwards with t using norm_nonneg _
      · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
        have htpos : (0 : ℝ) < t := ht
        have habs : |Real.cos (2 * h * t) / t| = |Real.cos (2 * h * t)| / t := by
          rw [abs_div]
          congr 1
          exact abs_of_pos htpos
        rw [Real.norm_eq_abs, habs]
        exact div_le_div_of_nonneg_right (Real.abs_cos_le_one (2 * h * t)) (le_of_lt htpos)
      · simpa [one_div] using (tendsto_inv_atTop_zero (𝕜 := ℝ))
    have hch : Tendsto (fun t : ℝ => (c / h) * (Real.cos (2 * h * t) / t)) atTop (𝓝 0) := by
      simpa using hbase.const_mul (c / h)
    refine Tendsto.congr' ?_ hch
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp

  have hsq : Tendsto (fun t : ℝ => c ^ 2 * Real.exp (Real.pi * c) / (4 * h ^ 2 * t ^ 2))
      atTop (𝓝 0) := by
    have hp : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have hg : Tendsto (fun t : ℝ => h ^ 2 * t ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) hp
    have hinv : Tendsto (fun t : ℝ => (h ^ 2 * t ^ 2)⁻¹) atTop (𝓝 0) := hg.inv_tendsto_atTop
    have hmul : Tendsto (fun t : ℝ => (c ^ 2 * Real.exp (Real.pi * c) / 4) * (h ^ 2 * t ^ 2)⁻¹)
        atTop (𝓝 0) := by
      simpa using hinv.const_mul (c ^ 2 * Real.exp (Real.pi * c) / 4)
    refine Tendsto.congr' ?_ hmul
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp
  have hsum := ((tendsto_const_nhds (x := Real.exp (-(Real.pi * c)))).add hcos).add hsq
  simpa [inverseScheduleBracket, add_zero] using hsum

/-- For positive `h`, the displayed inverse-schedule weight tends to `sinh (πc) / sinh (2πc) *
exp (-πc)` as time tends to infinity. -/
theorem inverseSchedule_displayed_weight_tendsto (h c : ℝ) (hh : 0 < h) :
    Tendsto (fun t : ℝ => inverseScheduleDisplayedWeight h c t) atTop
      (𝓝 (Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c) * Real.exp (-(Real.pi * c)))) := by
  have h := (inverseScheduleBracket_tendsto h c hh).const_mul
    (Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c))
  simpa [inverseScheduleDisplayedWeight_eq_bracket, mul_comm, mul_left_comm, mul_assoc] using h

/-- For positive `c`, the leading hyperbolic-sine expression equals `1 / (exp (2πc) + 1)`. -/
theorem inverseSchedule_leading_eq (c : ℝ) (hc : 0 < c) :
    Real.sinh (Real.pi * c) / Real.sinh (2 * Real.pi * c) * Real.exp (-(Real.pi * c))
      = 1 / (Real.exp (2 * Real.pi * c) + 1) := by
  have hs : Real.sinh (Real.pi * c) ≠ 0 :=
    (Real.sinh_ne_zero).mpr (ne_of_gt (by positivity))
  have hch : Real.cosh (Real.pi * c) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have he : Real.exp (Real.pi * c) ≠ 0 := (Real.exp_pos _).ne'
  have hsin2 : Real.sinh (2 * Real.pi * c) = Real.sinh (2 * (Real.pi * c)) := by
    rw [show 2 * Real.pi * c = 2 * (Real.pi * c) by ring]
  rw [hsin2, Real.sinh_two_mul, Real.cosh_eq, Real.exp_neg]
  have hexp2 : Real.exp (2 * Real.pi * c)
      = Real.exp (Real.pi * c) * Real.exp (Real.pi * c) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp2]
  field_simp

/-- For positive `h` and `c`, the displayed inverse-schedule complement tends to `1 - 1 / (exp
(2πc) + 1)` as time tends to infinity [KadowakiNishimori1998]. -/
theorem inverseSchedule_displayed_complement_tendsto (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun t : ℝ => inverseScheduleDisplayedComplement h c t) atTop
      (𝓝 (1 - 1 / (Real.exp (2 * Real.pi * c) + 1))) := by
  have hexc := inverseSchedule_displayed_weight_tendsto h c hh
  rw [inverseSchedule_leading_eq c hc] at hexc
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hexc
  simpa [inverseScheduleDisplayedComplement] using h

/-- The logistic tail `1 / (exp (2πc) + 1)` is asymptotically equivalent to `exp (-2πc)` as `c`
tends to infinity [KadowakiNishimori1998]. -/
theorem inverseSchedule_logistic_tail_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun c : ℝ => 1 / (Real.exp (2 * Real.pi * c) + 1))
      (fun c : ℝ => Real.exp (-(2 * Real.pi * c))) := by
  have hpos : ∀ᶠ c in atTop, Real.exp (-(2 * Real.pi * c)) ≠ 0 :=
    Eventually.of_forall (fun c => (Real.exp_pos _).ne')
  rw [Asymptotics.isEquivalent_iff_tendsto_one hpos]
  have hcte : Tendsto (fun c : ℝ => 2 * Real.pi * c) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr tendsto_id
  have hzero : Tendsto (fun c : ℝ => Real.exp (-(2 * Real.pi * c))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hcte
  have heq : ∀ c : ℝ, (1 / (Real.exp (2 * Real.pi * c) + 1)) / Real.exp (-(2 * Real.pi * c))
      = (1 + Real.exp (-(2 * Real.pi * c)))⁻¹ := by
    intro c
    have hE : Real.exp (2 * Real.pi * c) ≠ 0 := (Real.exp_pos _).ne'
    have hE1 : Real.exp (2 * Real.pi * c) + 1 ≠ 0 := ne_of_gt (by positivity)
    have h1E : 1 + (Real.exp (2 * Real.pi * c))⁻¹ ≠ 0 := by positivity
    rw [Real.exp_neg]
    field_simp
  have h1 : Tendsto (fun c : ℝ => 1 + Real.exp (-(2 * Real.pi * c))) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hzero
  have hq : Tendsto (fun c : ℝ => (1 + Real.exp (-(2 * Real.pi * c)))⁻¹) atTop
      (𝓝 ((1 : ℝ)⁻¹)) := by
    have hv := h1.inv₀ (by norm_num : (1 + 0 : ℝ) ≠ 0)
    simpa using hv
  have hq' : Tendsto (fun c : ℝ => (1 + Real.exp (-(2 * Real.pi * c)))⁻¹) atTop (𝓝 1) := by
    simpa using hq
  refine Tendsto.congr' ?_ hq'
  filter_upwards with c
  exact (heq c).symm

/-- As `c` tends to infinity, the logistic complement is asymptotically equivalent to `1 - exp
(-2πc)`. -/
theorem inverseSchedule_logistic_complement_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun c : ℝ => 1 - 1 / (Real.exp (2 * Real.pi * c) + 1))
      (fun c : ℝ => 1 - Real.exp (-(2 * Real.pi * c))) := by
  have hpos : ∀ᶠ c in atTop, (1 - Real.exp (-(2 * Real.pi * c))) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have h2 : 0 < 2 * Real.pi * c := mul_pos (mul_pos two_pos Real.pi_pos) hc
    have hlt : Real.exp (-(2 * Real.pi * c)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  rw [Asymptotics.isEquivalent_iff_tendsto_one hpos]
  have hcte : Tendsto (fun c : ℝ => 2 * Real.pi * c) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr tendsto_id
  have hzero : Tendsto (fun c : ℝ => Real.exp (-(2 * Real.pi * c))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hcte
  have hnum : Tendsto (fun c : ℝ => 1 - 1 / (Real.exp (2 * Real.pi * c) + 1)) atTop (𝓝 1) := by
    have hE : Tendsto (fun c : ℝ => Real.exp (2 * Real.pi * c)) atTop atTop :=
      Real.tendsto_exp_atTop.comp hcte
    have hE1 : Tendsto (fun c : ℝ => Real.exp (2 * Real.pi * c) + 1) atTop atTop :=
      tendsto_atTop_mono (fun c => by linarith [(Real.exp_pos (2 * Real.pi * c)).le]) hE
    have hinv : Tendsto (fun c : ℝ => 1 / (Real.exp (2 * Real.pi * c) + 1)) atTop (𝓝 0) :=
      hE1.const_div_atTop 1
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  have hden : Tendsto (fun c : ℝ => 1 - Real.exp (-(2 * Real.pi * c))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  have hq : Tendsto (fun c : ℝ => (1 - 1 / (Real.exp (2 * Real.pi * c) + 1))
      / (1 - Real.exp (-(2 * Real.pi * c)))) atTop (𝓝 (1 / 1)) := hnum.div hden (by norm_num)
  simpa using! hq

/-- The logistic complement `1 - 1 / (exp (2πc) + 1)` is strictly less than one for every real
`c`. -/
theorem inverseSchedule_logistic_complement_lt_one (c : ℝ) :
    1 - 1 / (Real.exp (2 * Real.pi * c) + 1) < 1 := by
  have hden : 0 < Real.exp (2 * Real.pi * c) + 1 := by positivity
  have : 0 < 1 / (Real.exp (2 * Real.pi * c) + 1) := by positivity
  linarith

end Qatlib.Papers.TITCMTReport98.MainResults
