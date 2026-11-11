/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Moment bounds from Gaussian-decay tails

This module integrates a tail estimate of the form D exp(-t²/8) into bounds for all natural
moments of a nonnegative random variable on a probability space. The constants `momentCap` and
`shiftedConstant` also control shifted moments, providing moment estimates relevant to
Gaussian-based approximation settings [TranEtAl2026].

## Main statements

* `momentCap_ne_top`: The Gaussian tail moment cap is finite for nonnegative D.
* `moment_from_tail`: The tail estimate implies integrability and a bound for every natural
  moment.
* `shifted_moment_from_tail`: The same estimate controls moments of 1 + f.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments

/-- The extended nonnegative moment cap obtained from the tail envelope D exp(-t²/8) by
layer-cake integration, with value one for the zeroth moment. -/
def momentCap (D : ℝ) (p : ℕ) : ℝ≥0∞ :=
  if p=0 then 1 else ENNReal.ofReal (p:ℝ)*
    ∫⁻ t in Ioi (0:ℝ),ENNReal.ofReal (D*Real.exp (-t^2/8)*t^((p:ℝ)-1))

/-- For nonnegative `D`, the cap `momentCap D p` is finite for every natural exponent `p`. -/
theorem momentCap_ne_top (D : ℝ) (hD : 0≤D) (p : ℕ) : momentCap D p≠∞ := by
  by_cases hp : p=0
  · simp [momentCap,hp]
  · have hp' : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp
    have hi := (integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/8)
      (show -1<(p:ℝ)-1 by linarith)).const_mul D
    have he : (fun t:ℝ=>D*(t^((p:ℝ)-1)*Real.exp (-(1/8)*t^2)))=
        (fun t:ℝ=>D*Real.exp (-t^2/8)*t^((p:ℝ)-1)) := by
      funext t
      rw [show -(1/8:ℝ)*t^2= -t^2/8 by ring]
      ring
    rw [he] at hi
    have hn : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun t:ℝ=>D*Real.exp (-t^2/8)*t^((p:ℝ)-1)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg (mul_nonneg hD (Real.exp_nonneg _)) (Real.rpow_nonneg (mem_Ioi.mp ht).le _)
    have hh := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hn).mpr hi
    simpa only [momentCap,hp,if_false] using ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh
variable {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- A measurable nonnegative function on a probability space with tail at most D exp(-t²/8) has
integrable p-th power and p-th moment at most `(momentCap D p).toReal` for every natural
`p`. -/
theorem moment_from_tail (f : α→ℝ) (hf : Measurable f) (hn : ∀ x,0≤f x)
    (D : ℝ) (hD : 0≤D)
    (htail : ∀ t:ℝ,0≤t→μ.real {x | t<f x}≤D*Real.exp (-t^2/8)) (p : ℕ) :
    Integrable (fun x=>(f x)^p) μ ∧
      (∫ x,(f x)^p ∂μ)≤(momentCap D p).toReal := by
  by_cases hp : p=0
  · subst p
    exact ⟨by simpa only [pow_zero] using integrable_const (1:ℝ),by simp [momentCap]⟩
  have hp' : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hl := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hn) hf.aemeasurable hp'
  simp only [Real.rpow_natCast] at hl
  have hb : (∫⁻ x,ENNReal.ofReal ((f x)^p) ∂μ)≤momentCap D p := by
    rw [hl]
    simp only [momentCap,hp,if_false]
    apply mul_le_mul_right
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht' : 0≤t := (mem_Ioi.mp ht).le
    have hm : μ {x | t<f x}≤ENNReal.ofReal (D*Real.exp (-t^2/8)) := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (htail t ht')
    calc
      _ ≤ ENNReal.ofReal (D*Real.exp (-t^2/8))*ENNReal.ofReal (t^((p:ℝ)-1)) := mul_le_mul_left hm _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hfinite : (∫⁻ x,ENNReal.ofReal ((f x)^p) ∂μ)≠∞ :=
    ne_top_of_le_ne_top (momentCap_ne_top D hD p) hb
  have hfi : Integrable (fun x=>(f x)^p) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x=>pow_nonneg (hn x) p))).mp hfinite
  refine ⟨hfi,?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hfi
    (Filter.Eventually.of_forall (fun x=>pow_nonneg (hn x) p))
  rw [← he] at hb
  have hreal := ENNReal.toReal_mono (momentCap_ne_top D hD p) hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x=>pow_nonneg (hn x) p))] using hreal

/-- The real shifted-moment bound `2 ^ (p - 1) * (1 + (momentCap D p).toReal)`, with subtraction
in the natural exponent. -/
def shiftedConstant (D : ℝ) (p : ℕ) : ℝ := 2^(p-1)*(1+(momentCap D p).toReal)

/-- A measurable nonnegative function on a probability space with the stated Gaussian-decay tail
has integrable `(1 + f) ^ p` and its integral is at most `shiftedConstant D p`. -/
theorem shifted_moment_from_tail (f : α→ℝ) (hf : Measurable f) (hn : ∀ x,0≤f x)
    (D : ℝ) (hD : 0≤D)
    (htail : ∀ t:ℝ,0≤t→μ.real {x | t<f x}≤D*Real.exp (-t^2/8)) (p : ℕ) :
    Integrable (fun x=>(1+f x)^p) μ ∧
      (∫ x,(1+f x)^p ∂μ)≤shiftedConstant D p := by
  obtain ⟨hfi,hbound⟩ := moment_from_tail μ f hf hn D hD htail p
  have hdom : Integrable (fun x=>2^(p-1)*(1+(f x)^p)) μ :=
      ((integrable_const 1).add hfi).const_mul _
  have hpoint (x:α) : (1+f x)^p≤2^(p-1)*(1+(f x)^p) := by
    simpa only [one_pow] using add_pow_le (by norm_num : (0:ℝ)≤1) (hn x) p
  have htarget : Integrable (fun x=>(1+f x)^p) μ := by
    apply hdom.mono' ((measurable_const.add hf).pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x=>by
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (add_nonneg zero_le_one (hn x)) p)]
      exact hpoint x
  refine ⟨htarget,?_⟩
  have h := integral_mono htarget hdom hpoint
  rw [integral_const_mul,integral_add (integrable_const 1) hfi] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  exact h.trans
      (mul_le_mul_of_nonneg_left (show 1+(∫ x,(f x)^p ∂μ)≤1+(momentCap D p).toReal by linarith) (by positivity))
end Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments
