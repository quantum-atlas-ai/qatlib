/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineRegulator

/-!
# Cosine sample coefficients and residue weights

This module identifies `cosineSampleCoefficient` with the inverse derivative of the contour
denominator at a sample pole. An exact norm formula gives harmonic and inverse-cubic bounds,
which control finite weight sums and tails in the cosine sampling construction of
[WangEtAl2026].

## Main statements

* `cosineSampleCoefficient_eq_deriv_inv`: sample coefficients are inverse denominator
  derivatives.
* `cosineSampleCoefficient_norm`: computes the coefficient norm exactly.
* `cosineSampleCoefficient_norm_le_cubic`: gives the inverse-cubic tail bound for positive
  parameters.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex

/-- For every real `s`, the complex number `1 + I * s` is nonzero. -/
theorem cosine_one_add_scale_ne_zero (s : ℝ) : (1 : ℂ) + I * (s : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

/-- For positive `γ` and `τ`, the contour denominator has nonzero derivative at every cosine
sample pole. -/
theorem cosineContourDenominator_deriv_sample_ne_zero {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    deriv (cosineContourDenominator γ τ) (cosineSamplePole γ τ k) ≠ 0 := by
  rw [cosineContourDenominator_deriv_sample hγ hτ]
  apply mul_ne_zero _ (cosine_one_add_scale_ne_zero _)
  apply div_ne_zero _ (by norm_num)
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact_mod_cast (cosineSampleAngle_pos k).ne'

/-- For positive `γ` and `τ`, the sample coefficient is the inverse derivative of the contour
denominator at the corresponding sample pole. -/
theorem cosineSampleCoefficient_eq_deriv_inv {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    cosineSampleCoefficient γ τ k =
      (deriv (cosineContourDenominator γ τ) (cosineSamplePole γ τ k))⁻¹ := by
  rw [cosineContourDenominator_deriv_sample hγ hτ]
  simp only [cosineSampleCoefficient, div_eq_mul_inv, mul_inv_rev,
    inv_inv, ← inv_pow, inv_neg, inv_one]
  ring

/-- The sample coefficient norm is `2 / (cosineSampleAngle k * ‖1 + I * cosineSampleScale γ τ
k‖)`. -/
theorem cosineSampleCoefficient_norm (γ τ : ℝ) (k : ℕ) :
    ‖cosineSampleCoefficient γ τ k‖ =
      2 / (cosineSampleAngle k * ‖(1 : ℂ) + I * (cosineSampleScale γ τ k : ℂ)‖) := by
  simp only [cosineSampleCoefficient, norm_div, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, mul_one, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cosineSampleAngle_pos k)]

/-- Every cosine sample coefficient has norm at most `2 / (π * (k + 1 / 2))`. -/
theorem cosineSampleCoefficient_norm_le_harmonic (γ τ : ℝ) (k : ℕ) :
    ‖cosineSampleCoefficient γ τ k‖ ≤ 2 / (Real.pi * ((k : ℝ) + 1 / 2)) := by
  have hn : 1 ≤ ‖(1 : ℂ) + I * (cosineSampleScale γ τ k : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm ((1 : ℂ) + I * (cosineSampleScale γ τ k : ℂ))
  rw [cosineSampleCoefficient_norm]
  have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (cosineSampleAngle_pos k)
    (le_mul_of_one_le_right (cosineSampleAngle_pos k).le hn)
  simpa only [cosineSampleAngle, mul_comm] using h

/-- For positive `γ` and `τ`, the sample coefficient norm is at most `2 * γ * τ ^ 2 / (π ^ 3 *
(k + 1 / 2) ^ 3)`. -/
theorem cosineSampleCoefficient_norm_le_cubic {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    ‖cosineSampleCoefficient γ τ k‖ ≤
      2 * γ * τ ^ 2 / (Real.pi ^ 3 * ((k : ℝ) + 1 / 2) ^ 3) := by
  have hn : cosineSampleScale γ τ k ≤
      ‖(1 : ℂ) + I * (cosineSampleScale γ τ k : ℂ)‖ := by
    simpa using Complex.im_le_norm ((1 : ℂ) + I * (cosineSampleScale γ τ k : ℂ))
  rw [cosineSampleCoefficient_norm]
  calc
    _ ≤ 2 / (cosineSampleAngle k * cosineSampleScale γ τ k) :=
      div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (cosineSampleAngle_pos k) (cosineSampleScale_pos hγ hτ k))
        (mul_le_mul_of_nonneg_left hn (cosineSampleAngle_pos k).le)
    _ = _ := by
      unfold cosineSampleScale cosineSampleAngle
      have hk : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
      field_simp

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
