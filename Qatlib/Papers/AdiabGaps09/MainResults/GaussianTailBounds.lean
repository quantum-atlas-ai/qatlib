/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Bounds for an unnormalized Gaussian tail

This module defines the weight `gaussWeight x = exp(-x²)` and its upper-tail integral
`upperTail`. It proves integrability, positivity, monotonicity, and explicit exponential upper
and lower estimates used as analytic tools in the probabilistic context of [FarhiEtAl2011].

## Main statements

* `upperTail_pos` and `upperTail_antitone`: positivity and monotonicity of the tail.
* `upperTail_ge_exp`: the lower bound `exp(-(a + 1)²)` for nonnegative `a`.
* `upperTail_le_exp_div`: the upper bound `exp(-a²) / (2a)` for positive `a`.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Qatlib.Papers.AdiabGaps09.MainResults.GaussianTail

/-- The unnormalized Gaussian weight `exp(-x²)`. -/
def gaussWeight (x : ℝ) : ℝ := Real.exp (-(x ^ 2))

/-- The Gaussian weight `gaussWeight x` is strictly positive for every real `x`. -/
theorem gaussWeight_pos (x : ℝ) : 0 < gaussWeight x := Real.exp_pos _

/-- The Gaussian weight is nonzero at every real argument. -/
theorem gaussWeight_ne_zero (x : ℝ) : gaussWeight x ≠ 0 := (gaussWeight_pos x).ne'

/-- The Gaussian weight `exp(-x²)` is Lebesgue integrable on the real line. -/
theorem integrable_gaussWeight : Integrable gaussWeight := by
  have h : Integrable (fun x : ℝ => x ^ (0 : ℝ) * Real.exp (-(1 : ℝ) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one (s := 0) (by norm_num)
  refine h.congr ?_
  filter_upwards with x
  simp [gaussWeight]

/-- The integral of `exp(-x²)` over the open ray `(a, ∞)`. -/
def upperTail (a : ℝ) : ℝ := ∫ x in Ioi a, gaussWeight x

/-- The Gaussian weight is integrable over every open upper ray. -/
theorem integrableOn_upperTail (a : ℝ) : IntegrableOn gaussWeight (Ioi a) :=
  integrable_gaussWeight.integrableOn

/-- The Gaussian weight is nonnegative almost everywhere with respect to Lebesgue measure. -/
theorem ae_nonneg_gaussWeight : ∀ᵐ x ∂(volume : Measure ℝ), 0 ≤ gaussWeight x :=
  Filter.Eventually.of_forall (fun x => (gaussWeight_pos x).le)

/-- The upper-tail integral of the Gaussian weight is strictly positive at every real threshold. -/
theorem upperTail_pos (a : ℝ) : 0 < upperTail a := by
  unfold upperTail
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsup : Function.support gaussWeight = univ := by
      ext x
      simp [Function.mem_support, gaussWeight_ne_zero x]
    rw [hsup, univ_inter, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · exact ae_nonneg_gaussWeight.filter_mono (ae_mono Measure.restrict_le_self)
  · exact integrableOn_upperTail a

/-- Increasing the lower threshold decreases the Gaussian upper-tail integral. -/
theorem upperTail_antitone {a b : ℝ} (hab : a ≤ b) : upperTail b ≤ upperTail a := by
  unfold upperTail
  refine setIntegral_mono_set (integrableOn_upperTail a)
    (ae_nonneg_gaussWeight.filter_mono (ae_mono Measure.restrict_le_self)) ?_
  exact Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt hab hx)

/-- For nonnegative `a`, the Gaussian upper-tail integral is at least `exp(-(a + 1)²)`. See
[FarhiEtAl2011]. -/
theorem upperTail_ge_exp (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-((a + 1) ^ 2)) ≤ upperTail a := by
  have hfin : (volume : Measure ℝ) (Ioc a (a + 1)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; simp
  have hsub : ∫ x in Ioc a (a + 1), gaussWeight x ≤ upperTail a := by
    unfold upperTail
    refine setIntegral_mono_set (integrableOn_upperTail a)
      (ae_nonneg_gaussWeight.filter_mono (ae_mono Measure.restrict_le_self)) ?_
    exact Filter.Eventually.of_forall (fun x hx => hx.1)
  have hle : ∀ x ∈ Ioc a (a + 1), Real.exp (-((a + 1) ^ 2)) ≤ gaussWeight x := by
    intro x hx
    have hxle : x ≤ a + 1 := hx.2
    have hxge : a ≤ x := le_of_lt hx.1
    have hxnn : 0 ≤ x := le_trans ha hxge
    have hsq : x ^ 2 ≤ (a + 1) ^ 2 := pow_le_pow_left₀ hxnn hxle 2
    have hneg : -((a + 1) ^ 2) ≤ -(x ^ 2) := neg_le_neg hsq
    unfold gaussWeight
    exact Real.exp_le_exp.mpr hneg
  have hmono : ∫ x in Ioc a (a + 1), (fun _ : ℝ => Real.exp (-((a + 1) ^ 2))) x
      ≤ ∫ x in Ioc a (a + 1), gaussWeight x :=
    setIntegral_mono_on (integrableOn_const hfin) (integrable_gaussWeight.integrableOn)
      measurableSet_Ioc hle
  have hval : ∫ x in Ioc a (a + 1), (fun _ : ℝ => Real.exp (-((a + 1) ^ 2))) x
      = Real.exp (-((a + 1) ^ 2)) := by
    rw [setIntegral_const]
    have hv : (volume : Measure ℝ).real (Ioc a (a + 1)) = 1 := by
      rw [Measure.real, Real.volume_Ioc]
      norm_num
    rw [hv, one_smul]
  rw [hval] at hmono
  exact hmono.trans hsub

/-- For positive `a`, the Gaussian upper-tail integral is at most `exp(-a²) / (2 * a)`. See
[FarhiEtAl2011]. -/
theorem upperTail_le_exp_div (a : ℝ) (ha : 0 < a) :
    upperTail a ≤ Real.exp (-(a ^ 2)) / (2 * a) := by
  have hmajint : Integrable (fun x : ℝ => (x / a) * gaussWeight x) := by
    have hx : Integrable (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 : ℝ) * x ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one (s := 1) (by norm_num)
    have := hx.const_mul (a)⁻¹
    refine this.congr ?_
    filter_upwards with x
    simp only [gaussWeight, Real.rpow_one]
    ring
  have hdom : ∫ x in Ioi a, gaussWeight x
      ≤ ∫ x in Ioi a, (x / a) * gaussWeight x := by
    refine setIntegral_mono_on (integrableOn_upperTail a) hmajint.integrableOn
      measurableSet_Ioi ?_
    intro x hx
    have hxa : a ≤ x := le_of_lt hx
    have hg : 0 ≤ gaussWeight x := (gaussWeight_pos x).le
    have : 1 ≤ x / a := (one_le_div ha).mpr hxa
    calc gaussWeight x = 1 * gaussWeight x := (one_mul _).symm
      _ ≤ (x / a) * gaussWeight x := by gcongr
  have hIntval : ∫ x in Ioi a, (x / a) * gaussWeight x
      = Real.exp (-(a ^ 2)) / (2 * a) := by
    have hkey : (fun x : ℝ => (x / a) * gaussWeight x)
        = fun x : ℝ => a⁻¹ * (x * Real.exp (-(x ^ 2))) := by
      funext x; unfold gaussWeight; ring
    rw [hkey, integral_const_mul]
    have hderiv : ∀ x ∈ Ioi a,
        HasDerivAt (fun y : ℝ => -(2⁻¹ : ℝ) * Real.exp (-(y ^ 2)))
          (x * Real.exp (-(x ^ 2))) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x := by
        have := (hasDerivAt_id x).pow 2
        simpa using! this.neg
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
          (Real.exp (-(x ^ 2)) * (-(2 * x))) x := h1.exp
      have h3 := h2.const_mul (-(2⁻¹ : ℝ))
      convert! h3 using 1
      ring
    have hcont : ContinuousWithinAt (fun y : ℝ => -(2⁻¹ : ℝ) * Real.exp (-(y ^ 2)))
        (Ici a) a := by fun_prop
    have hfint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2))) (Ioi a) := by
      have hx : Integrable (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 : ℝ) * x ^ 2)) :=
        integrable_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one (s := 1) (by norm_num)
      refine (hx.integrableOn).congr ?_
      filter_upwards with x
      simp only [Real.rpow_one]
      ring
    have hlim : Tendsto (fun y : ℝ => -(2⁻¹ : ℝ) * Real.exp (-(y ^ 2))) atTop (𝓝 0) := by
      have hsq : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
        Filter.tendsto_pow_atTop (n := 2) (by norm_num)
      have hneg : Tendsto (fun y : ℝ => -(y ^ 2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp hsq
      have hexp : Tendsto (fun y : ℝ => Real.exp (-(y ^ 2))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hneg
      simpa using hexp.const_mul (-(2⁻¹ : ℝ))
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto (a := a)
      (f := fun y : ℝ => -(2⁻¹ : ℝ) * Real.exp (-(y ^ 2)))
      (f' := fun x : ℝ => x * Real.exp (-(x ^ 2))) hcont hderiv hfint hlim
    have hzero : (0 : ℝ) - (-(2⁻¹ : ℝ) * Real.exp (-(a ^ 2))) = Real.exp (-(a ^ 2)) / 2 := by
      ring
    rw [hftc, hzero]
    field_simp
  calc upperTail a = ∫ x in Ioi a, gaussWeight x := rfl
    _ ≤ ∫ x in Ioi a, (x / a) * gaussWeight x := hdom
    _ = Real.exp (-(a ^ 2)) / (2 * a) := hIntval

end Qatlib.Papers.AdiabGaps09.MainResults.GaussianTail
