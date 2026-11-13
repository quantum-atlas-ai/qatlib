/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianCore
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Laplace weights for vector normalization

The inverse norm of a nonzero vector is represented using the scalar Laplace weight `weight`.
The two-parameter function `weightedDot` extends this representation to normalized inner
products, including pairs with a zero vector. See [CrostaSaubanereHuber2026].

## Main statements

* `weight_integral`: evaluates the scalar Laplace integral as `√π / r` for positive `r`.
* `weightedDot_integral`: recovers π times the normalized inner product.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

/-- Lebesgue measure restricted to the positive real half-line. -/
abbrev positiveLine : Measure ℝ := volume.restrict (Ioi 0)

/-- The scalar Laplace weight `a^(-1/2) * exp (-(r² * a))`. -/
def weight (r a : ℝ) : ℝ := a ^ (-(1/2:ℝ)) * Real.exp (-(r^2*a))

/-- The Laplace weight is nonnegative whenever its parameter `a` is nonnegative. -/
theorem weight_nonneg (r : ℝ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ weight r a :=
  mul_nonneg (Real.rpow_nonneg ha _) (Real.exp_pos _).le

/-- For positive `r`, the Laplace weight is integrable over the positive half-line. -/
theorem weight_integrable {r : ℝ} (hr : 0 < r) : Integrable (weight r) positiveLine := by
  simpa only [weight,Real.rpow_one,neg_mul] using!
    integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=-(1/2:ℝ))
      (by norm_num) (by norm_num) (sq_pos_of_pos hr)

/-- For positive `r`, the positive-half-line integral of the Laplace weight equals `√π / r`. -/
theorem weight_integral {r : ℝ} (hr : 0 < r) :
    (∫ a,weight r a ∂positiveLine)=Real.sqrt Real.pi/r := by
  have hpow : (1/r^2)^(1/2:ℝ)=r⁻¹ := by
    rw [← Real.sqrt_eq_rpow,Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_sq hr.le]
    simp
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=(1/2:ℝ))
    (r:=r^2) (by norm_num) (sq_pos_of_pos hr)
  have he : (∫ a,weight r a ∂positiveLine)=(1/r^2)^(1/2:ℝ)*Real.Gamma (1/2:ℝ) := by
    simpa only [weight,positiveLine,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num] using h
  rw [he,hpow,Real.Gamma_one_half_eq]
  ring

/-- The inner product of `x` and `y`, multiplied by the Laplace weights of their norms at the
two parameters. -/
def weightedDot (x y : V) (ab : ℝ×ℝ) : ℝ :=
  inner ℝ x y * weight ‖x‖ ab.1 * weight ‖y‖ ab.2

/-- The weighted inner product is integrable over the two positive Laplace parameters for every
pair of vectors. -/
theorem weightedDot_integrable (x y : V) :
    Integrable (weightedDot x y) (positiveLine.prod positiveLine) := by
  change Integrable (fun ab : ℝ×ℝ => inner ℝ x y*weight ‖x‖ ab.1*weight ‖y‖ ab.2) _
  by_cases hx : x=0
  · simp [hx]
  by_cases hy : y=0
  · simp [hy]
  have hi := (weight_integrable (norm_pos_iff.mpr hx)).mul_prod
    (weight_integrable (norm_pos_iff.mpr hy))
  simpa only [mul_assoc] using hi.const_mul (inner ℝ x y)

/-- The integral of the weighted inner product over both positive parameters equals π times the
inner product of the normalized vectors. -/
theorem weightedDot_integral (x y : V) :
    (∫ ab,weightedDot x y ab ∂positiveLine.prod positiveLine)=
      Real.pi*inner ℝ (unitVector x) (unitVector y) := by
  by_cases hx : x=0
  · simp [weightedDot,hx,unitVector_zero]
  by_cases hy : y=0
  · simp [weightedDot,hy,unitVector_zero]
  have hx' := norm_pos_iff.mpr hx
  have hy' := norm_pos_iff.mpr hy
  have he : weightedDot x y =fun ab => inner ℝ x y*(weight ‖x‖ ab.1*weight ‖y‖ ab.2) := by
    funext ab
    simp [weightedDot,mul_assoc]
  rw [he,integral_const_mul,integral_prod_mul,weight_integral hx',weight_integral hy']
  simp only [unitVector,inner_smul_left,inner_smul_right,conj_trivial]
  have hp := Real.sq_sqrt Real.pi_pos.le
  field_simp
  rw [hp]

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
