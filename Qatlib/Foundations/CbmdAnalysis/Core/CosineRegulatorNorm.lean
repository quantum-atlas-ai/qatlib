/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineRegulator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Norm bounds for the cosine regulator

This module bounds complex cosine by the exponential of the absolute imaginary part and
evaluates `cosineRegulator` at the target point one. The resulting estimate `exp (τ * sqrt (γ /
2))` controls the normalization factor in the cosine sampling formulas of [WangEtAl2026].

## Main statements

* `complex_cos_norm_le_exp_abs_im`: an exponential upper bound for complex cosine.
* `cosineRegulator_one_eq_cos`: an explicit complex cosine formula at the target.
* `cosineRegulator_one_norm_le`: bounds the target regulator norm for positive parameters.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex

/-- The norm of complex cosine is at most `exp |q.im|`. -/
theorem complex_cos_norm_le_exp_abs_im (q : ℂ) :
    ‖Complex.cos q‖ ≤ Real.exp |q.im| := by
  have h := norm_add_le (Complex.exp (q * I)) (Complex.exp (-q * I))
  rw [← Complex.two_cos, norm_mul, Complex.norm_ofNat, Complex.norm_exp, Complex.norm_exp] at h
  have hp : Real.exp q.im ≤ Real.exp |q.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hm : Real.exp (-q.im) ≤ Real.exp |q.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
    zero_sub, Complex.neg_im, neg_neg] at h
  linarith

/-- For positive `γ` and `τ`, the regulator at one equals `cos ((τ * sqrt (γ / 2)) * (1 + I))`. -/
theorem cosineRegulator_one_eq_cos {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) :
    cosineRegulator γ τ 1 =
      Complex.cos (((τ * Real.sqrt (γ / 2) : ℝ) : ℂ) * (1 + I)) := by
  have hs : ((Real.sqrt (γ / 2) : ℝ) : ℂ) ^ 2 = (γ : ℂ) / 2 := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ γ / 2 by positivity)
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hp : (-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) *
      ((((τ * Real.sqrt (γ / 2) : ℝ) : ℂ) * (1 + I)) ^ 2) = 1 := by
    push_cast
    rw [mul_pow, mul_pow, hs]
    field_simp
    ring_nf
    simp [I_sq]
  simpa only [hp] using cosineRegulator_quadratic hγ.ne' hτ.ne'
    ((((τ * Real.sqrt (γ / 2) : ℝ) : ℂ) * (1 + I)))

/-- For positive `γ` and `τ`, the regulator norm at one is at most `exp (τ * sqrt (γ / 2))`. -/
theorem cosineRegulator_one_norm_le {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) :
    ‖cosineRegulator γ τ 1‖ ≤ Real.exp (τ * Real.sqrt (γ / 2)) := by
  rw [cosineRegulator_one_eq_cos hγ hτ]
  have h := complex_cos_norm_le_exp_abs_im
    ((((τ * Real.sqrt (γ / 2) : ℝ) : ℂ) * (1 + I)))
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.add_im, Complex.one_im,
    Complex.I_im, zero_add, mul_one, Complex.ofReal_im, zero_mul, add_zero,
    abs_of_nonneg (mul_nonneg hτ.le (Real.sqrt_nonneg _))] using h

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
