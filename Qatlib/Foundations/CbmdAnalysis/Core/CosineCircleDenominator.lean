/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineFiniteCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Lower bounds for the cosine regulator on circles

This module bounds the norm of complex cosine on circles of radius `n * π` and transfers the
estimates to `cosineRegulator`. A quadratic-root identity rewrites the exponential factor
intrinsically in terms of `‖z‖ + z.im`, yielding the denominator control used by the contour
arguments in [WangEtAl2026].

## Main statements

* `complex_cos_norm_lower_on_nat_pi_circle`: an exponential lower bound for complex cosine on an
  integer-π circle.
* `cosineRegulator_circle_norm_lower_of_sq`: transfers the bound through a quadratic root.
* `cosineRegulator_circle_norm_lower_intrinsic`: expresses the bound directly in terms of the
  contour point.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex Metric Set

/-- The squared norm of complex cosine equals `cos (q.re) ^ 2 + sinh (q.im) ^ 2`. -/
theorem complex_cos_norm_sq (q : ℂ) :
    ‖Complex.cos q‖ ^ 2 = Real.cos q.re ^ 2 + Real.sinh q.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.cos_eq]
  simp only [Complex.sub_re, Complex.mul_re, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_re, Complex.cos_ofReal_im, Complex.cosh_ofReal_im,
    Complex.sin_ofReal_re, Complex.sinh_ofReal_re, Complex.sin_ofReal_im,
    Complex.sinh_ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
    Complex.mul_im, mul_zero, zero_mul, sub_zero, zero_sub, add_zero,
    mul_one]
  have h := Real.sin_sq_add_cos_sq q.re
  have hh := Real.cosh_sq q.im
  nlinarith [sq_nonneg (Real.cos q.re),
    congrArg (fun t : ℝ => t * Real.sinh q.im ^ 2) h]

/-- The absolute value of the cosine of the real part is bounded by the norm of complex cosine. -/
theorem abs_real_cos_re_le_complex_cos_norm (q : ℂ) :
    |Real.cos q.re| ≤ ‖Complex.cos q‖ := by
  have h := complex_cos_norm_sq q
  have hn := norm_nonneg (Complex.cos q)
  nlinarith [sq_abs (Real.cos q.re), sq_nonneg (Real.sinh q.im), abs_nonneg (Real.cos q.re)]

/-- When `|q.im| ≥ 1`, the exponential `exp |q.im|` is at most four times `‖cos q‖`. -/
theorem exp_abs_im_le_four_mul_cos_norm {q : ℂ} (hy : 1 ≤ |q.im|) :
    Real.exp |q.im| ≤ 4 * ‖Complex.cos q‖ := by
  have hplus := norm_sub_norm_le (Complex.exp (q * I)) (-Complex.exp (-q * I))
  have hminus := norm_sub_norm_le (Complex.exp (-q * I)) (-Complex.exp (q * I))
  simp only [sub_neg_eq_add, norm_neg] at hplus hminus
  rw [← Complex.two_cos, norm_mul, Complex.norm_ofNat] at hplus
  rw [add_comm, ← Complex.two_cos, norm_mul, Complex.norm_ofNat] at hminus
  simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im,
    mul_one, zero_sub, Complex.neg_im, neg_neg] at hplus hminus
  have he : 2 ≤ Real.exp |q.im| := by
    linarith [Real.add_one_le_exp |q.im|]
  have hm : Real.exp (-|q.im|) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg q.im))
  rcases le_total 0 q.im with h | h
  · rw [abs_of_nonneg h] at he hm ⊢
    linarith
  · rw [abs_of_nonpos h] at he hm ⊢
    simpa only [neg_neg] using (show Real.exp (-q.im) ≤ 4 * ‖cos q‖ by
      simp only [neg_neg] at hm
      linarith)

/-- On a circle of radius `n * π` with `n ≥ 1`, points with `|q.im| ≤ 1` satisfy `1 / 2 ≤ ‖cos
q‖`. -/
theorem half_le_cos_norm_on_nat_pi_circle {q : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hq : ‖q‖ = (n : ℝ) * Real.pi) (hy : |q.im| ≤ 1) :
    (1 : ℝ) / 2 ≤ ‖Complex.cos q‖ := by
  let r : ℝ := (n : ℝ) * Real.pi
  have hr : 1 ≤ r := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [r]
    nlinarith [Real.two_le_pi]
  have hx : |q.re| ≤ r := by simpa only [r, ← hq] using Complex.abs_re_le_norm q
  have hs : q.re ^ 2 + q.im ^ 2 = r ^ 2 := by
    have he := Complex.sq_norm q
    rw [hq] at he
    simpa only [r, Complex.normSq_apply, pow_two] using he.symm
  have hd0 : 0 ≤ r - |q.re| := sub_nonneg.mpr hx
  have hd1 : r - |q.re| ≤ 1 := by
    have hy2 : q.im ^ 2 ≤ 1 := by nlinarith [sq_abs q.im, abs_nonneg q.im]
    have ha := abs_nonneg q.re
    have hsq := sq_abs q.re
    nlinarith [mul_nonneg hd0 (show 0 ≤ r + |q.re| - 1 by linarith)]
  have hcos : (1 : ℝ) / 2 ≤ Real.cos (r - |q.re|) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := r - |q.re|)
    nlinarith [sq_nonneg (r - |q.re|), mul_nonneg hd0 (sub_nonneg.mpr hd1)]
  have habs : |Real.cos (r - |q.re|)| = |Real.cos q.re| := by
    dsimp [r]
    rw [Real.cos_nat_mul_pi_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Real.cos_abs]
  calc
    (1 : ℝ) / 2 ≤ |Real.cos (r - |q.re|)| := hcos.trans (le_abs_self _)
    _ = |Real.cos q.re| := habs
    _ ≤ ‖Complex.cos q‖ := abs_real_cos_re_le_complex_cos_norm q

/-- On a circle of radius `n * π` with `n ≥ 1`, the complex cosine norm is at least `exp |q.im|
/ (4 * exp 1)`. -/
theorem complex_cos_norm_lower_on_nat_pi_circle {q : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hq : ‖q‖ = (n : ℝ) * Real.pi) :
    Real.exp |q.im| / (4 * Real.exp 1) ≤ ‖Complex.cos q‖ := by
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [div_le_iff₀ (by positivity : 0 < 4 * Real.exp 1)]
  by_cases hy : |q.im| ≤ 1
  · have hc := half_le_cos_norm_on_nat_pi_circle hn hq hy
    have he := Real.exp_le_exp.mpr hy
    nlinarith [Real.exp_pos (1 : ℝ)]
  · have hc := exp_abs_im_le_four_mul_cos_norm (le_of_not_ge hy)
    nlinarith [mul_nonneg (norm_nonneg (Complex.cos q)) (sub_nonneg.mpr he1)]

/-- For positive `γ` and `τ`, a root satisfying `q ^ 2 = I * γ * τ ^ 2 * z` over the `n`th
cosine circle has norm `n * π`. -/
theorem cosineCircle_root_norm {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (n : ℕ) {z q : ℂ} (hz : ‖z‖ = cosineCircleRadius γ τ n)
    (hq : q ^ 2 = I * (γ : ℂ) * (τ : ℂ) ^ 2 * z) :
    ‖q‖ = (n : ℝ) * Real.pi := by
  have hnorm := congrArg norm hq
  simp only [norm_pow, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hγ, abs_of_pos hτ, one_mul] at hnorm
  rw [hz, cosineCircleRadius] at hnorm
  have hden : γ * τ ^ 2 ≠ 0 := ne_of_gt (mul_pos hγ (sq_pos_of_pos hτ))
  have hs : ‖q‖ ^ 2 = ((n : ℝ) * Real.pi) ^ 2 := by
    rw [hnorm]
    field_simp
  exact (sq_eq_sq₀ (norm_nonneg q) (by positivity)).mp hs

/-- For positive parameters and `n ≥ 1`, the cosine regulator norm on the `n`th circle is at
least `exp |q.im| / (4 * exp 1)` for any corresponding quadratic root `q`. -/
theorem cosineRegulator_circle_norm_lower_of_sq {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) {n : ℕ} (hn : 1 ≤ n)
    {z q : ℂ} (hz : ‖z‖ = cosineCircleRadius γ τ n)
    (hq : q ^ 2 = I * (γ : ℂ) * (τ : ℂ) ^ 2 * z) :
    Real.exp |q.im| / (4 * Real.exp 1) ≤ ‖cosineRegulator γ τ z‖ := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hrec : z = (-I / ((γ : ℂ) * (τ : ℂ) ^ 2)) * q ^ 2 := by
    rw [hq]
    field_simp
    simp [I_sq]
  have he : cosineRegulator γ τ z = cos q := by
    rw [hrec, cosineRegulator_quadratic hγ.ne' hτ.ne']
  rw [he]
  exact complex_cos_norm_lower_on_nat_pi_circle hn (cosineCircle_root_norm hγ hτ n hz hq)

/-- For positive parameters and `n ≥ 1`, the regulator norm on the `n`th cosine circle is
bounded below by the exponential of the absolute imaginary part of its principal quadratic
root, divided by `4 * exp 1`. -/
theorem cosineRegulator_circle_norm_lower {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) {n : ℕ} (hn : 1 ≤ n)
    {z : ℂ} (hz : ‖z‖ = cosineCircleRadius γ τ n) :
    Real.exp |(Complex.sqrt (I * (γ : ℂ) * (τ : ℂ) ^ 2 * z)).im| /
      (4 * Real.exp 1) ≤ ‖cosineRegulator γ τ z‖ :=
  cosineRegulator_circle_norm_lower_of_sq hγ hτ hn hz (Complex.cpow_ofNat_inv_pow _ 2)

/-- For positive `γ` and `τ`, any root of `q ^ 2 = I * γ * τ ^ 2 * z` satisfies `|q.im| = sqrt
(γ * τ ^ 2 * (‖z‖ + z.im) / 2)`. -/
theorem cosineRoot_abs_im {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    {z q : ℂ} (hq : q ^ 2 = I * (γ : ℂ) * (τ : ℂ) ^ 2 * z) :
    |q.im| = Real.sqrt (γ * τ ^ 2 * (‖z‖ + z.im) / 2) := by
  have hnorm := congrArg norm hq
  simp only [norm_pow, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hγ, abs_of_pos hτ, one_mul] at hnorm
  have hre := congrArg Complex.re hq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_sub, one_mul,
    zero_add, sub_zero, add_zero] at hre
  have hs := Complex.sq_norm q
  simp only [Complex.normSq_apply] at hs
  have him : q.im ^ 2 = γ * τ ^ 2 * (‖z‖ + z.im) / 2 := by nlinarith
  rw [← him, Real.sqrt_sq_eq_abs]

/-- For positive parameters and `n ≥ 1`, the regulator norm on the `n`th cosine circle is at
least `exp (sqrt (γ * τ ^ 2 * (‖z‖ + z.im) / 2)) / (4 * exp 1)`. -/
theorem cosineRegulator_circle_norm_lower_intrinsic {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) {n : ℕ} (hn : 1 ≤ n)
    {z : ℂ} (hz : ‖z‖ = cosineCircleRadius γ τ n) :
    Real.exp (Real.sqrt (γ * τ ^ 2 * (‖z‖ + z.im) / 2)) /
      (4 * Real.exp 1) ≤ ‖cosineRegulator γ τ z‖ := by
  have h := cosineRegulator_circle_norm_lower hγ hτ hn hz
  rw [cosineRoot_abs_im hγ hτ (q := Complex.sqrt (I * (γ : ℂ) * (τ : ℂ) ^ 2 * z))
    (Complex.cpow_ofNat_inv_pow _ 2)] at h
  exact h

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
