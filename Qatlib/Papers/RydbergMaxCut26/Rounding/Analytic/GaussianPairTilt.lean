/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.Gaussian

/-!
# Pairwise Gaussian tilted moments

`pairTiltZero` and `pairTiltCross` are iterated standard Gaussian integrals for the correlated
pair `(x, t*x+s*z)` with a quadratic exponential weight. Completion of the square gives
`outerPrecision`, an explicit zeroth moment, and a cross-moment formula with factor
`t/(4*noisePrecision*outerPrecision)`.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `pairTiltZero_eval`: evaluates the quadratic tilt normalization.
* `pairTiltCross_eval`: evaluates the tilted cross moment.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

/-- The outer quadratic coefficient `1/2 + a + remainingRate t b s` after integrating the noise
variable. -/
def outerPrecision (t s a b : ℝ) : ℝ := 1/2+a+remainingRate t b s

/-- For `b ≥ 0`, the residual coefficient `remainingRate t b s` is nonnegative. -/
theorem remainingRate_nonneg (t s b : ℝ) (hb : 0≤b) : 0≤remainingRate t b s := by
  unfold remainingRate
  positivity

/-- For nonnegative `a` and `b`, the outer Gaussian precision is strictly positive. -/
theorem outerPrecision_pos (t s a b : ℝ) (ha : 0≤a) (hb : 0≤b) : 0<outerPrecision t s a b := by
  unfold outerPrecision
  linarith [remainingRate_nonneg t s b hb]

/-- For `b ≥ 0`, the conditional linear factor simplifies to `t*x / (2*noisePrecision b s)`. -/
theorem conditional_mean_factor (t s b x : ℝ) (hb : 0≤b) :
    t*x+s*noiseShift t b s x=t*x/(2*noisePrecision b s) := by
  have hA := (noisePrecision_pos hb s).ne'
  unfold noiseShift
  field_simp
  unfold noisePrecision
  ring

/-- The iterated standard Gaussian integral of `exp (-(a*x^2+b*(t*x+s*z)^2))`. -/
def pairTiltZero (t s a b : ℝ) : ℝ :=
  ∫ x : ℝ,∫ z : ℝ,Real.exp (-(a*x^2+b*(t*x+s*z)^2)) ∂standard1 ∂standard1

/-- The iterated standard Gaussian integral of `x*(t*x+s*z)` weighted by `exp
(-(a*x^2+b*(t*x+s*z)^2))`. -/
def pairTiltCross (t s a b : ℝ) : ℝ :=
  ∫ x : ℝ,∫ z : ℝ,x*(t*x+s*z)*Real.exp (-(a*x^2+b*(t*x+s*z)^2)) ∂standard1 ∂standard1

/-- For `b ≥ 0`, `pairTiltZero` equals `(sqrt (2*π))⁻² * sqrt (π/noisePrecision b s) * sqrt
(π/outerPrecision t s a b)` in the total integral convention. -/
theorem pairTiltZero_eval (t s a b : ℝ) (hb : 0≤b) :
    pairTiltZero t s a b=
      (Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b s)*
        Real.sqrt (Real.pi/outerPrecision t s a b) := by
  have he (x : ℝ) : (∫ z : ℝ,Real.exp (-(a*x^2+b*(t*x+s*z)^2)) ∂standard1)=
      Real.exp (-a*x^2)*(Real.sqrt (2*Real.pi))⁻¹*
        Real.exp (-remainingRate t b s*x^2)*Real.sqrt (Real.pi/noisePrecision b s) := by
    simp_rw [neg_add,Real.exp_add,← neg_mul]
    rw [integral_const_mul,conditional_tilt_zero t b s x hb]
    ring
  rw [pairTiltZero]
  simp_rw [he]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  have he' (x : ℝ) : gaussianPDFReal 0 1 x •
      (Real.exp (-a*x^2)*(Real.sqrt (2*Real.pi))⁻¹*
        Real.exp (-remainingRate t b s*x^2)*Real.sqrt (Real.pi/noisePrecision b s))=
      ((Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b s))*
        Real.exp (-outerPrecision t s a b*x^2) := by
    simp only [gaussianPDFReal_def,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
    have hexp : Real.exp (-(x^2/2))*Real.exp (-a*x^2)*Real.exp (-remainingRate t b s*x^2)=
        Real.exp (-outerPrecision t s a b*x^2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      unfold outerPrecision
      ring
    calc
      _ = ((Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b s))*
          (Real.exp (-(x^2/2))*Real.exp (-a*x^2)*Real.exp (-remainingRate t b s*x^2)) := by ring
      _ = _ := by rw [hexp]
  simp_rw [he']
  rw [integral_const_mul,integral_gaussian]

/-- For nonnegative `a` and `b`, `pairTiltCross` equals the explicit zeroth-moment normalization
times `t/(4*noisePrecision b s*outerPrecision t s a b)`. -/
theorem pairTiltCross_eval (t s a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    pairTiltCross t s a b=
      ((Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b s)*
        Real.sqrt (Real.pi/outerPrecision t s a b))*
          (t/(4*noisePrecision b s*outerPrecision t s a b)) := by
  have he (x : ℝ) : (∫ z : ℝ,x*(t*x+s*z)*Real.exp (-(a*x^2+b*(t*x+s*z)^2)) ∂standard1)=
      (x*Real.exp (-a*x^2))*((Real.sqrt (2*Real.pi))⁻¹*
        Real.exp (-remainingRate t b s*x^2)*Real.sqrt (Real.pi/noisePrecision b s)*
          (t*x/(2*noisePrecision b s))) := by
    have he' (z : ℝ) : x*(t*x+s*z)*Real.exp (-(a*x^2+b*(t*x+s*z)^2))=
        (x*Real.exp (-a*x^2))*((t*x+s*z)*Real.exp (-b*(t*x+s*z)^2)) := by
      rw [neg_add,Real.exp_add]
      ring
    simp_rw [he']
    rw [integral_const_mul,conditional_tilt_linear t b s x hb,conditional_mean_factor t s b x hb]
  rw [pairTiltCross]
  simp_rw [he]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)]
  have he' (x : ℝ) : gaussianPDFReal 0 1 x •
      ((x*Real.exp (-a*x^2))*((Real.sqrt (2*Real.pi))⁻¹*
        Real.exp (-remainingRate t b s*x^2)*Real.sqrt (Real.pi/noisePrecision b s)*
          (t*x/(2*noisePrecision b s))))=
      ((Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b s)*
        (t/(2*noisePrecision b s)))*(Real.exp (-outerPrecision t s a b*x^2)*x^2) := by
    simp only [gaussianPDFReal_def,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
    have hexp : Real.exp (-(x^2/2))*Real.exp (-a*x^2)*Real.exp (-remainingRate t b s*x^2)=
        Real.exp (-outerPrecision t s a b*x^2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      unfold outerPrecision
      ring
    calc
      _ = ((Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b s)*
          (t/(2*noisePrecision b s)))*
          ((Real.exp (-(x^2/2))*Real.exp (-a*x^2)*Real.exp (-remainingRate t b s*x^2))*x^2) := by ring
      _ = _ := by rw [hexp]
  simp_rw [he']
  rw [integral_const_mul,integral_square_quadratic _ (outerPrecision_pos t s a b ha hb)]
  ring

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
