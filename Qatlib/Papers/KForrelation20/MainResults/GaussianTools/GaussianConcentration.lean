/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option backward.isDefEq.respectTransparency false

/-!
# Gaussian concentration tools

Bansal–Sinha, *$k$-Forrelation optimally separates quantum and classical query
complexity*, fixed arXiv:2008.07003v3, §2.1 (page 12).

The paper fixes the standard normal density `γ(s) = (2π)^{-1/2} e^{-s²/2}` and the
cumulative distribution `Φ(a) = ∫_{-∞}^a γ`.  Proposition 2.1 states the truncation
estimate `1 − Φ(a) ≤ ½ e^{-a²/2}` for every `a > 0`; it is used in the proof of
Lemma 4.6 to control the probability that a standard Gaussian lies outside
`[0, c]`, and hence is a load-bearing input of the `(δ, k)`-Forrelation lower
bound.

This file proves Proposition 2.1 by the paper's own route: translate the tail to
the half line, bound `e^{-(a+x)²/2} ≤ e^{-a²/2} e^{-x²/2}` for `x ≥ 0`, and evaluate
the Gaussian integral on `[0, ∞)`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Real

namespace Qatlib.Papers.KForrelation20.MainResults

/-- The standard normal density `γ(s) = (2π)^{-1/2} e^{-s²/2}` of §2.1. -/
def gaussDensity (s : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(s ^ 2) / 2)

/-- The standard normal cumulative distribution `Φ(a) = ∫_{-∞}^a γ` of §2.1. -/
def gaussCdf (a : ℝ) : ℝ := ∫ s in Set.Iic a, gaussDensity s

/-- The upper tail `1 − Φ(a) = ∫_a^∞ γ` of §2.1. -/
def gaussTail (a : ℝ) : ℝ := ∫ s in Set.Ioi a, gaussDensity s

/-- Helper: the paper's exponent `−(s²)/2` is `(−1/2) * s²`, the shape accepted by
Mathlib's Gaussian integral. -/
theorem neg_sq_div_two_eq (s : ℝ) : -(s ^ 2) / 2 = (-(1 / 2 : ℝ)) * s ^ 2 := by ring

/-- The Gaussian integral `∫ e^{-s²/2} ds = √(2π)` behind the normalisation of `γ`. -/
theorem integral_exp_neg_sq_div_two :
    ∫ s : ℝ, Real.exp (-(s ^ 2) / 2) = Real.sqrt (2 * Real.pi) := by
  have hcongr : ∫ s : ℝ, Real.exp (-(s ^ 2) / 2)
      = ∫ s : ℝ, Real.exp ((-(1 / 2 : ℝ)) * s ^ 2) := by
    apply integral_congr_ae
    filter_upwards with s
    congr 1
    ring
  rw [hcongr, integral_gaussian]
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by field_simp]

/-- The Gaussian `s ↦ e^{-s²/2}` is integrable, the integrability input used for the
normalisation and monotonicity steps below. -/
theorem integrable_exp_neg_sq_div_two : Integrable (fun s : ℝ => Real.exp (-(s ^ 2) / 2)) := by
  have h : Integrable (fun s : ℝ => Real.exp ((-(1 / 2 : ℝ)) * s ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro s
  beta_reduce
  congr 1
  ring

/-- The standard normal density is integrable on `ℝ`. -/
theorem integrable_gaussDensity : Integrable (fun s : ℝ => gaussDensity s) := by
  unfold gaussDensity
  exact integrable_exp_neg_sq_div_two.const_mul _

/-- The density `γ` has total mass one, as required for a probability density. -/
theorem gaussDensity_integral_eq_one : ∫ s : ℝ, gaussDensity s = 1 := by
  unfold gaussDensity
  rw [integral_const_mul, integral_exp_neg_sq_div_two]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

/-- The density is nonnegative, so the half-line integral is a probability. -/
theorem gaussDensity_nonneg (s : ℝ) : 0 ≤ gaussDensity s := by
  unfold gaussDensity
  positivity

/-- `Φ` and the upper tail partition the unit mass: `Φ(a) + (1 − Φ(a)) = 1`. -/
theorem gaussCdf_add_gaussTail (a : ℝ) : gaussCdf a + gaussTail a = 1 := by
  have hcompl := integral_add_compl (μ := volume) (s := Set.Iic a)
    measurableSet_Iic integrable_gaussDensity
  have hcomp : (Set.Iic a)ᶜ = Set.Ioi a := by
    ext x
    simp [Set.mem_Ioi]
  rw [hcomp, gaussDensity_integral_eq_one] at hcompl
  unfold gaussCdf gaussTail
  linarith

/-- Translation form of the upper tail: `∫_a^∞ γ = ∫_0^∞ γ(a + x) dx`, the change of
variables used in the proof of Proposition 2.1. -/
theorem gaussTail_eq_setIntegral_shift (a : ℝ) :
    gaussTail a = ∫ x in Set.Ioi (0 : ℝ), gaussDensity (a + x) := by
  have hmem : ∀ x : ℝ, a + x ∈ Set.Ioi a ↔ x ∈ Set.Ioi (0 : ℝ) := by
    intro x
    simp only [Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hind : gaussTail a = ∫ x : ℝ, (Set.Ioi a).indicator gaussDensity x := by
    unfold gaussTail
    rw [integral_indicator measurableSet_Ioi]
  rw [hind]
  have hshift : ∫ x : ℝ, (Set.Ioi a).indicator gaussDensity x
      = ∫ x : ℝ, (Set.Ioi a).indicator gaussDensity (a + x) := by
    conv_lhs => rw [← integral_add_left_eq_self ((Set.Ioi a).indicator gaussDensity) a]
  rw [hshift]
  have hfun : (fun x : ℝ => (Set.Ioi a).indicator gaussDensity (a + x))
      = (Set.Ioi (0 : ℝ)).indicator (fun x => gaussDensity (a + x)) := by
    funext x
    by_cases hx : x ∈ Set.Ioi (0 : ℝ)
    · have hx' : a + x ∈ Set.Ioi a := (hmem x).mpr hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : a + x ∉ Set.Ioi a := by
        rw [hmem]; exact hx
      simp [Set.indicator, hx, hx']
  rw [hfun, integral_indicator measurableSet_Ioi]

/-- The key exponential comparison behind Proposition 2.1: for `a, x > 0`,
`e^{-(a+x)²/2} ≤ e^{-a²/2} e^{-x²/2}`, i.e. `(a + x)² ≥ a² + x²`. -/
theorem exp_neg_add_sq_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.exp (-(a + x) ^ 2 / 2) ≤ Real.exp (-(a ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_pos ha hx]

/-- The shifted density is dominated by `e^{-a²/2} γ` on the positive half line. -/
theorem gaussDensity_shift_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    gaussDensity (a + x) ≤ Real.exp (-(a ^ 2) / 2) * gaussDensity x := by
  unfold gaussDensity
  have h := exp_neg_add_sq_le ha hx
  have hp : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a + x) ^ 2 / 2)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-(a ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_left h hp
    _ = Real.exp (-(a ^ 2) / 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) := by ring

/-- For every `a` the shifted density satisfies
`e^{-(a+x)²/2} ≤ e^{a²/2} e^{-x²/4}`, because `(2a + x)² ≥ 0`; in particular it is
integrable on the whole real line. -/
theorem integrable_gaussDensity_shift (a : ℝ) :
    Integrable (fun x : ℝ => gaussDensity (a + x)) := by
  have hcont : Continuous (fun x : ℝ => gaussDensity (a + x)) := by
    unfold gaussDensity
    fun_prop
  have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hdom : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * x ^ 2))) := by
    have h1 : Integrable (fun x : ℝ =>
        Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) :=
      hbase.const_mul _
    exact h1.const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussDensity_nonneg _)]
  unfold gaussDensity
  have hexp : Real.exp (-(a + x) ^ 2 / 2) ≤
      Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (2 * a + x)]
  have hp : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(a + x) ^ 2 / 2)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * x ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hp
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (a ^ 2 / 2) *
          Real.exp (-(1 / 4 : ℝ) * x ^ 2)) := rfl

/-- The half-line Gaussian integral `∫_0^∞ γ = 1/2`. -/
theorem integral_Ioi_zero_gaussDensity :
    ∫ x in Set.Ioi (0 : ℝ), gaussDensity x = 1 / 2 := by
  have hcongr : ∫ x in Set.Ioi (0 : ℝ), gaussDensity x
      = (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x in Set.Ioi (0 : ℝ), Real.exp ((-(1 / 2 : ℝ)) * x ^ 2) := by
    unfold gaussDensity
    rw [integral_const_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    beta_reduce
    congr 1
    ring
  rw [hcongr, integral_gaussian_Ioi]
  rw [show Real.sqrt (Real.pi / (1 / 2 : ℝ)) = Real.sqrt (2 * Real.pi) by
    congr 1
    field_simp]
  field_simp

/-- Proposition 2.1 (Gaussian concentration), page 12: for every `a > 0` the upper
tail of the standard normal satisfies `1 − Φ(a) ≤ ½ e^{-a²/2}`.

The proof is the paper's: translate the tail to `[0, ∞)`, bound the shifted density
by `e^{-a²/2} γ`, and use `∫_0^∞ γ = 1/2`. -/
theorem gaussianConcentration {a : ℝ} (ha : 0 < a) :
    1 - gaussCdf a ≤ 2⁻¹ * Real.exp (-(a ^ 2) / 2) := by
  have htail : 1 - gaussCdf a = gaussTail a := by
    have h := gaussCdf_add_gaussTail a
    linarith
  rw [htail, gaussTail_eq_setIntegral_shift a]
  have hmono : ∫ x in Set.Ioi (0 : ℝ), gaussDensity (a + x)
      ≤ ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(a ^ 2) / 2) * gaussDensity x := by
    apply setIntegral_mono_on (integrable_gaussDensity_shift a).integrableOn
    · exact (integrable_gaussDensity.const_mul (Real.exp (-(a ^ 2) / 2))).integrableOn
    · exact measurableSet_Ioi
    · intro x hx
      exact gaussDensity_shift_le ha hx
  have hcompute : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(a ^ 2) / 2) * gaussDensity x
      = Real.exp (-(a ^ 2) / 2) * (1 / 2) := by
    rw [integral_const_mul, integral_Ioi_zero_gaussDensity]
  calc ∫ x in Set.Ioi (0 : ℝ), gaussDensity (a + x)
      ≤ ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(a ^ 2) / 2) * gaussDensity x := hmono
    _ = 2⁻¹ * Real.exp (-(a ^ 2) / 2) := by rw [hcompute]; ring

end Qatlib.Papers.KForrelation20.MainResults
