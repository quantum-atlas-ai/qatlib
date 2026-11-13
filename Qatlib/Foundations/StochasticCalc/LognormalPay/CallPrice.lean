/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.Defs
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian evaluation of the Black-Scholes call price

This module evaluates Gaussian tail integrals and exponentially tilted tails, then applies them
to the lognormal terminal level. The exercise threshold `bsThreshold` relates the payoff region
to `d1` and `d2`, yielding the expected call payoff and its discounted Black-Scholes expression.

The mathematical background is discussed in [RebentrostGuptBromley2018].

## Main statements

* `integral_Ioi_gaussianPDFReal_exp`: evaluates an exponentially tilted Gaussian tail.
* `call_expectation_gaussian`: gives the undiscounted call expectation under a Gaussian law.
* `blackScholes_call_price`: gives the discounted call expectation for a random variable with
  that law.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.StochasticCalc.LognormalPay

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory BigOperators

/-- The standard normal density `exp (-y ^ 2 / 2) / sqrt (2 * π)`. -/
def stdpdf (y : ℝ) : ℝ := (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y ^ 2) / 2)

/-- The standard normal density is continuous. -/
lemma continuous_stdpdf : Continuous stdpdf := by
  unfold stdpdf
  fun_prop

/-- The standard normal density is an even function. -/
lemma stdpdf_even : Function.Even stdpdf := by
  intro y
  unfold stdpdf
  rw [neg_sq]

/-- The standard normal density is integrable with respect to Lebesgue measure. -/
lemma integrable_stdpdf : Integrable stdpdf := by
  unfold stdpdf
  apply Integrable.const_mul
  have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  convert h using 1
  funext y
  ring_nf

/-- The standard normal density integrates to one. -/
lemma integral_stdpdf : ∫ y, stdpdf y = 1 := by
  unfold stdpdf
  rw [integral_const_mul]
  have h' : ∫ y : ℝ, Real.exp (-(y ^ 2) / 2) = Real.sqrt (2 * Real.pi) := by
    have h := integral_gaussian (b := (1 / 2 : ℝ))
    have h2 : (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi := by ring
    rw [show (∫ y : ℝ, Real.exp (-(y ^ 2) / 2))
        = ∫ y : ℝ, Real.exp (-(1 / 2 : ℝ) * y ^ 2) by
      exact integral_congr_ae (ae_of_all _ (fun y => by ring_nf))]
    rw [h, h2]
  rw [h']
  field_simp

/-- The normal cumulative distribution function equals the integral of `stdpdf` over the closed
lower half-line. -/
lemma normalCDF_eq_setIntegral (x : ℝ) :
    normalCDF x = ∫ y in Set.Iic x, stdpdf y := by
  unfold normalCDF stdpdf
  rw [integral_const_mul]

/-- Translating the argument of the standard normal density translates the lower endpoint of its
upper-tail integral. -/
lemma integral_Ioi_stdpdf_comp_sub (c a : ℝ) :
    ∫ y in Set.Ioi a, stdpdf (y - c) = ∫ u in Set.Ioi (a - c), stdpdf u := by
  have htend : Tendsto (fun x : ℝ => x - c) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c) tendsto_id
  have h := integral_comp_mul_deriv_Ioi (f := fun x : ℝ => x - c) (f' := fun _ => (1 : ℝ))
    (g := stdpdf) (a := a)
    (by fun_prop) htend
    (fun x _ => ((hasDerivAt_id x).sub_const c).hasDerivWithinAt)
    (continuous_stdpdf.continuousOn) (integrable_stdpdf.integrableOn)
    (by simpa using (integrable_stdpdf.comp_sub_right c).integrableOn (s := Set.Ici a))
  simpa using h

/-- The upper-tail integral of the standard normal density above `a` equals `normalCDF (-a)`. -/
lemma integral_Ioi_stdpdf (a : ℝ) :
    ∫ y in Set.Ioi a, stdpdf y = normalCDF (-a) := by
  rw [normalCDF_eq_setIntegral]
  have hcompl : ∫ y in Set.Iic (-a), stdpdf y
      = (∫ y, stdpdf y) - ∫ y in Set.Ioi (-a), stdpdf y := by
    have h :=
        setIntegral_compl (μ := volume) (s := Set.Ioi (-a)) measurableSet_Ioi integrable_stdpdf
    rw [Set.compl_Ioi] at h
    simpa using h
  have hneg : ∫ y in Set.Ioi (-a), stdpdf y = ∫ y in Set.Iic a, stdpdf y := by
    conv_lhs => rw [show (fun y => stdpdf y) = fun y => stdpdf (-y) by
      funext y; exact (stdpdf_even y).symm]
    rw [integral_comp_neg_Ioi]
    simp
  have hsplit : ∫ y in Set.Ioi a, stdpdf y
      = (∫ y, stdpdf y) - ∫ y in Set.Iic a, stdpdf y := by
    have h := setIntegral_compl (μ := volume) (s := Set.Iic a) measurableSet_Iic integrable_stdpdf
    rw [Set.compl_Iic] at h
    simpa using h
  rw [hcompl, hneg, hsplit]

/-- The exponential tilt of the standard normal upper tail equals `exp (σ ^ 2 / 2) * normalCDF
(σ - a)`. -/
lemma integral_Ioi_stdpdf_exp (a σ : ℝ) :
    ∫ y in Set.Ioi a, stdpdf y * Real.exp (σ * y)
      = Real.exp (σ ^ 2 / 2) * normalCDF (σ - a) := by
  have hpoint : ∀ y : ℝ, stdpdf y * Real.exp (σ * y)
      = Real.exp (σ ^ 2 / 2) * stdpdf (y - σ) := by
    intro y
    unfold stdpdf
    calc (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y ^ 2) / 2) * Real.exp (σ * y)
        = (1 / Real.sqrt (2 * Real.pi)) * (Real.exp (-(y ^ 2) / 2) * Real.exp (σ * y)) := by
          ring
      _ = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y ^ 2) / 2 + σ * y) := by
          rw [Real.exp_add]
      _ = (1 / Real.sqrt (2 * Real.pi)) *
            Real.exp ((-(y ^ 2) / 2 + σ * y - σ ^ 2 / 2) + σ ^ 2 / 2) := by ring_nf
      _ = (1 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-((y - σ) ^ 2) / 2) * Real.exp (σ ^ 2 / 2)) := by
          rw [Real.exp_add]
          congr 2
          ring
      _ = Real.exp (σ ^ 2 / 2) *
            ((1 / Real.sqrt (2 * Real.pi)) * Real.exp (-((y - σ) ^ 2) / 2)) := by ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  rw [integral_Ioi_stdpdf_comp_sub σ a]
  rw [integral_Ioi_stdpdf]
  ring

/-- Rescaling an upper-half-line integral by the inverse square root of positive `T` rescales
its endpoint and introduces the factor `sqrt T`. -/
lemma integral_Ioi_comp_inv_sqrt (f : ℝ → ℝ) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    ∫ w in Set.Ioi a, f ((Real.sqrt T)⁻¹ * w)
      = Real.sqrt T * ∫ y in Set.Ioi (a / Real.sqrt T), f y := by
  have hb : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h := integral_comp_mul_left_Ioi (g := f) (a := a) (b := (Real.sqrt T)⁻¹) (by positivity)
  rw [show (Real.sqrt T)⁻¹ * a = a / Real.sqrt T by ring] at h
  rw [h, smul_eq_mul]
  field_simp

/-- The centered Gaussian density with positive variance `T` is the rescaled standard normal
density. -/
lemma gaussianPDFReal_eq_std {T : ℝ} (hT : 0 < T) (w : ℝ) :
    gaussianPDFReal 0 ⟨T, hT.le⟩ w = (1 / Real.sqrt T) * stdpdf (w / Real.sqrt T) := by
  unfold gaussianPDFReal stdpdf
  change (Real.sqrt (2 * Real.pi * T))⁻¹ * Real.exp (-(w - 0) ^ 2 / (2 * T))
      = (1 / Real.sqrt T) * ((1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(w / Real.sqrt T) ^ 2 / 2))
  have hden : Real.sqrt (2 * Real.pi * T) = Real.sqrt T * Real.sqrt (2 * Real.pi) := by
    rw [show 2 * Real.pi * T = T * (2 * Real.pi) by ring, Real.sqrt_mul hT.le]
  rw [hden]
  have hsq : (w / Real.sqrt T) ^ 2 = w ^ 2 / T := by
    field_simp
    rw [Real.sq_sqrt hT.le]
  rw [hsq]
  simp only [sub_zero]
  field_simp

/-- The centered Gaussian upper tail above `a` equals `normalCDF (-(a / sqrt T))` for positive
`T`. -/
lemma integral_Ioi_gaussianPDFReal {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∫ w in Set.Ioi a, gaussianPDFReal 0 ⟨T, hT.le⟩ w
      = normalCDF (-(a / Real.sqrt T)) := by
  simp_rw [gaussianPDFReal_eq_std hT]
  rw [integral_const_mul]
  rw [show (∫ w in Set.Ioi a, stdpdf (w / Real.sqrt T))
      = ∫ w in Set.Ioi a, stdpdf ((Real.sqrt T)⁻¹ * w) by
    congr 1
    funext w
    rw [div_eq_inv_mul]]
  rw [integral_Ioi_comp_inv_sqrt stdpdf a hT]
  rw [integral_Ioi_stdpdf]
  field_simp

/-- Express an exponentially tilted centered Gaussian density in standardized coordinates for
positive variance. -/
lemma gaussianPDFReal_exp_eq_std {T : ℝ} (hT : 0 < T) (σ w : ℝ) :
    gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (σ * w)
      = (1 / Real.sqrt T) *
        (stdpdf (w / Real.sqrt T) * Real.exp ((σ * Real.sqrt T) * (w / Real.sqrt T))) := by
  rw [gaussianPDFReal_eq_std hT]
  have harg : σ * w = (σ * Real.sqrt T) * (w / Real.sqrt T) := by
    field_simp
  rw [harg]
  ring

/-- For positive variance `T`, the exponentially tilted Gaussian upper tail equals `exp (σ ^ 2 *
T / 2)` times the normal CDF at `σ * sqrt T - a / sqrt T`. -/
lemma integral_Ioi_gaussianPDFReal_exp {T : ℝ} (hT : 0 < T) (a σ : ℝ) :
    ∫ w in Set.Ioi a, gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (σ * w)
      = Real.exp (σ ^ 2 * T / 2) * normalCDF (σ * Real.sqrt T - a / Real.sqrt T) := by
  simp_rw [gaussianPDFReal_exp_eq_std hT]
  rw [integral_const_mul]
  rw [show (∫ w in Set.Ioi a,
        stdpdf (w / Real.sqrt T) * Real.exp ((σ * Real.sqrt T) * (w / Real.sqrt T)))
      = ∫ w in Set.Ioi a,
        (fun y => stdpdf y * Real.exp ((σ * Real.sqrt T) * y)) ((Real.sqrt T)⁻¹ * w) by
    congr 1
    funext w
    rw [div_eq_inv_mul]]
  rw [integral_Ioi_comp_inv_sqrt (fun y => stdpdf y * Real.exp ((σ * Real.sqrt T) * y)) a hT]
  rw [integral_Ioi_stdpdf_exp]
  rw [show (σ * Real.sqrt T) ^ 2 / 2 = σ ^ 2 * T / 2 by
    rw [mul_pow, Real.sq_sqrt hT.le]]
  field_simp

/-- A centered Gaussian density with positive variance remains integrable after multiplication
by `exp (σ * w)`. -/
lemma integrable_gaussianPDFReal_exp {T : ℝ} (hT : 0 < T) (σ : ℝ) :
    Integrable (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (σ * w)) := by
  have hpoint : ∀ w, gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (σ * w)
      = Real.exp (σ ^ 2 * T / 2) * gaussianPDFReal (σ * T) ⟨T, hT.le⟩ w := by
    intro w
    unfold gaussianPDFReal
    change (Real.sqrt (2 * Real.pi * T))⁻¹ * Real.exp (-(w - 0) ^ 2 / (2 * T)) * Real.exp (σ * w)
      = Real.exp (σ ^ 2 * T / 2) *
        ((Real.sqrt (2 * Real.pi * T))⁻¹ * Real.exp (-(w - σ * T) ^ 2 / (2 * T)))
    rw [show -(w - σ * T) ^ 2 / (2 * T)
        = -(w - 0) ^ 2 / (2 * T) + σ * w + -(σ ^ 2 * T / 2) by
      field_simp [hT.ne']
      ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  simp_rw [hpoint]
  exact (integrable_gaussianPDFReal (σ * T) ⟨T, hT.le⟩).const_mul _

/-- The Gaussian input threshold `(log (K / S0) - (r - σ ^ 2 / 2) * T) / σ` for the call
exercise region. -/
def bsThreshold (S0 K r σ T : ℝ) : ℝ :=
  (Real.log (K / S0) - (r - σ ^ 2 / 2) * T) / σ

/-- For positive initial level, strike, and volatility, the terminal level is at least the
strike exactly when the Gaussian input is at least `bsThreshold`. -/
lemma terminalLevel_ge_iff_threshold {S0 K r σ T w : ℝ} (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ) :
    K ≤ terminalLevel S0 r σ w T ↔ bsThreshold S0 K r σ T ≤ w := by
  unfold terminalLevel bsThreshold
  rw [show K ≤ S0 * Real.exp (σ * w + (r - σ ^ 2 / 2) * T)
      ↔ K / S0 ≤ Real.exp (σ * w + (r - σ ^ 2 / 2) * T) by
    rw [div_le_iff₀ hS0]
    constructor <;> intro h <;> linarith]
  rw [← Real.log_le_iff_le_exp (by positivity : 0 < K / S0)]
  rw [div_le_iff₀ hσ]
  constructor <;> intro h <;> linarith

/-- For positive maturity, `d2` is the negative exercise threshold divided by `sqrt T`. -/
lemma d2_eq_neg_threshold {S0 K r σ T : ℝ} (hT : 0 < T) :
    d2 S0 K r σ T = -(bsThreshold S0 K r σ T / Real.sqrt T) := by
  unfold d2 d1 bsThreshold
  have hlog : Real.log (S0 / K) = - Real.log (K / S0) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  field_simp
  rw [hlog, Real.sq_sqrt hT.le]
  ring

/-- For positive maturity, `d1` equals the volatility shift `σ * sqrt T` minus the standardized
exercise threshold. -/
lemma d1_eq_tilt_threshold {S0 K r σ T : ℝ} (hT : 0 < T) :
    d1 S0 K r σ T = σ * Real.sqrt T - bsThreshold S0 K r σ T / Real.sqrt T := by
  unfold d1 bsThreshold
  have hsqrt : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  have hlog : Real.log (S0 / K) = - Real.log (K / S0) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  field_simp
  rw [hlog, Real.sq_sqrt hT.le]
  ring

/-- For positive maturity, initial level, strike, and volatility, the Gaussian call expectation
is `S0 * exp (r * T) * normalCDF d1 - K * normalCDF d2`. -/
lemma call_expectation_gaussian {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ) :
    ∫ w, callPayoff K (terminalLevel S0 r σ w T) ∂(gaussianReal 0 ⟨T, hT.le⟩)
      = S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T) - K * normalCDF (d2 S0 K r σ T) := by
  have hv : (⟨T, hT.le⟩ : NNReal) ≠ 0 := by
    intro h
    exact hT.ne' (congrArg (fun x : NNReal => (x : ℝ)) h)
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := ⟨T, hT.le⟩) hv]
  simp only [smul_eq_mul]
  set w0 : ℝ := bsThreshold S0 K r σ T with hw0
  have hsplit : ∀ w, gaussianPDFReal 0 ⟨T, hT.le⟩ w * callPayoff K (terminalLevel S0 r σ w T)
      = if w0 ≤ w then gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K) else 0 := by
    intro w
    by_cases h : w0 ≤ w
    · have hge : K ≤ terminalLevel S0 r σ w T :=
        (terminalLevel_ge_iff_threshold hS0 hK hσ).mpr h
      have hnonneg : 0 ≤ terminalLevel S0 r σ w T - K := by linarith
      simp only [h, if_true, callPayoff]
      rw [max_eq_left hnonneg]
    · have hlt : ¬ K ≤ terminalLevel S0 r σ w T :=
        fun hge => h ((terminalLevel_ge_iff_threshold hS0 hK hσ).mp hge)
      have hnonpos : terminalLevel S0 r σ w T - K ≤ 0 := by
        have := not_le.mp hlt
        linarith
      simp only [h, if_false, callPayoff]
      rw [max_eq_right hnonpos]
      ring
  simp_rw [hsplit]
  have hind : (∫ w, if w0 ≤ w then
        gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K) else 0)
      = ∫ w in Set.Ici w0, gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K) := by
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with w
    by_cases h : w0 ≤ w <;> simp [Set.indicator, h]
  rw [hind]
  have hgbm : ∀ w, terminalLevel S0 r σ w T
      = S0 * Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * w) := by
    intro w
    unfold terminalLevel
    rw [Real.exp_add]
    ring
  have hI1 : ∫ w in Set.Ici w0, gaussianPDFReal 0 ⟨T, hT.le⟩ w
      = normalCDF (d2 S0 K r σ T) := by
    rw [integral_Ici_eq_integral_Ioi]
    rw [integral_Ioi_gaussianPDFReal hT]
    rw [d2_eq_neg_threshold hT]
  have hI2 : ∫ w in Set.Ici w0, gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T
      = S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T) := by
    rw [integral_Ici_eq_integral_Ioi]
    simp_rw [hgbm]
    rw [show (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w *
          (S0 * Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * w)))
        = fun w => (S0 * Real.exp ((r - σ ^ 2 / 2) * T)) *
          (gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (σ * w)) by
      funext w
      ring]
    rw [integral_const_mul]
    rw [integral_Ioi_gaussianPDFReal_exp hT]
    rw [d1_eq_tilt_threshold hT]
    have hexp : Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ ^ 2 * T / 2)
        = Real.exp (r * T) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show S0 * Real.exp ((r - σ ^ 2 / 2) * T) *
          (Real.exp (σ ^ 2 * T / 2) * normalCDF (σ * Real.sqrt T - w0 / Real.sqrt T))
        = S0 * (Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ ^ 2 * T / 2)) *
          normalCDF (σ * Real.sqrt T - w0 / Real.sqrt T) by ring]
    rw [hexp]
  have hlin : ∫ w in Set.Ici w0, gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K)
      = (∫ w in Set.Ici w0, gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T)
        - K * (∫ w in Set.Ici w0, gaussianPDFReal 0 ⟨T, hT.le⟩ w) := by
    have hInt1 : IntegrableOn
        (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T) (Set.Ici w0) := by
      simp_rw [hgbm]
      rw [show (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w *
            (S0 * Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * w)))
          = fun w => (S0 * Real.exp ((r - σ ^ 2 / 2) * T)) *
            (gaussianPDFReal 0 ⟨T, hT.le⟩ w * Real.exp (σ * w)) by
        funext w
        ring]
      exact ((integrable_gaussianPDFReal_exp hT σ).const_mul _).integrableOn
    have hInt2 : IntegrableOn (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w) (Set.Ici w0) :=
      (integrable_gaussianPDFReal 0 ⟨T, hT.le⟩).integrableOn
    rw [show (fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * (terminalLevel S0 r σ w T - K))
        = fun w => gaussianPDFReal 0 ⟨T, hT.le⟩ w * terminalLevel S0 r σ w T
          - K * gaussianPDFReal 0 ⟨T, hT.le⟩ w by
      funext w
      ring]
    rw [integral_sub hInt1 (hInt2.const_mul K)]
    rw [integral_const_mul]
  rw [hlin, hI2, hI1]

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}

/-- Under the stated centered Gaussian law and positive maturity, initial level, strike, and
volatility, the discounted call expectation is `S0 * normalCDF d1 - K * exp (-r * T) *
normalCDF d2`. -/
theorem blackScholes_call_price
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT.le⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    Real.exp (-(r * T)) * ∫ ω, callPayoff K (terminalLevel S0 r σ (W ω) T) ∂Q
      = S0 * normalCDF (d1 S0 K r σ T)
          - K * Real.exp (-(r * T)) * normalCDF (d2 S0 K r σ T) := by
  have hfm : AEStronglyMeasurable
      (fun w => callPayoff K (terminalLevel S0 r σ w T)) (Q.map W) := by
    rw [hW]
    exact (by
      unfold callPayoff terminalLevel
      fun_prop : Continuous fun w => callPayoff K (terminalLevel S0 r σ w T)).aestronglyMeasurable
  rw [← integral_map hWm hfm, hW, call_expectation_gaussian hT hS0 hK hσ]
  have hEr : Real.exp (-(r * T)) * Real.exp (r * T) = 1 := by
    rw [← Real.exp_add, show -(r * T) + r * T = 0 by ring, Real.exp_zero]
  calc Real.exp (-(r * T)) *
        (S0 * Real.exp (r * T) * normalCDF (d1 S0 K r σ T)
          - K * normalCDF (d2 S0 K r σ T))
      = S0 * normalCDF (d1 S0 K r σ T) * (Real.exp (-(r * T)) * Real.exp (r * T))
          - K * Real.exp (-(r * T)) * normalCDF (d2 S0 K r σ T) := by ring
    _ = S0 * normalCDF (d1 S0 K r σ T)
          - K * Real.exp (-(r * T)) * normalCDF (d2 S0 K r σ T) := by
      rw [hEr]
      ring

end

end Qatlib.Foundations.StochasticCalc.LognormalPay
