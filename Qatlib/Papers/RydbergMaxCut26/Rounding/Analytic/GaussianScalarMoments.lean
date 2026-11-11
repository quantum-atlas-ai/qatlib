/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Scalar Gaussian moments at fixed precision

`precisionVariance` converts a positive quadratic precision `A` to variance `1/(2*A)`. Its
density formula relates Gaussian expectations to real-volume integrals with weight `exp
(-A*(x-m)^2)`, yielding explicit linear and centered quadratic moments.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `integral_precision_density`: converts between the Gaussian and volume integrals.
* `integral_linear_quadratic` and `integral_square_quadratic`: evaluate the weighted moments.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

/-- The nonnegative variance `1/(2*A)` associated with a positive quadratic precision `A`. -/
def precisionVariance (A : ℝ) (hA : 0<A) : ℝ≥0 := ⟨1/(2*A),by positivity⟩

/-- The variance associated with a positive precision is nonzero. -/
theorem precisionVariance_ne_zero (A : ℝ) (hA : 0<A) : precisionVariance A hA≠0 := by
  have hp : 0<(precisionVariance A hA:ℝ) := by
    change 0<1/(2*A)
    positivity
  exact_mod_cast hp.ne'

/-- For positive `A`, the Gaussian density with mean `m` and variance `1/(2*A)` is `exp
(-A*(x-m)^2) / sqrt (π/A)`. -/
theorem precision_density (A m x : ℝ) (hA : 0<A) :
    gaussianPDFReal m (precisionVariance A hA) x=
      (Real.sqrt (Real.pi/A))⁻¹*Real.exp (-A*(x-m)^2) := by
  rw [gaussianPDFReal_def]
  change (Real.sqrt (2*Real.pi*(1/(2*A))))⁻¹*Real.exp (-(x-m)^2/(2*(1/(2*A))))=_
  have h1 : 2*Real.pi*(1/(2*A))=Real.pi/A := by field_simp
  have h2 : -(x-m)^2/(2*(1/(2*A)))= -A*(x-m)^2 := by field_simp
  rw [h1,h2]

/-- For positive `A`, integration against the Gaussian of mean `m` and variance `1/(2*A)` equals
the volume integral weighted by `exp (-A*(x-m)^2) / sqrt (π/A)`. -/
theorem integral_precision_density (A m : ℝ) (hA : 0<A) (f : ℝ→ℝ) :
    (∫ x,f x ∂gaussianReal m (precisionVariance A hA))=
      (Real.sqrt (Real.pi/A))⁻¹*∫ x,Real.exp (-A*(x-m)^2)*f x := by
  rw [integral_gaussianReal_eq_integral_smul (precisionVariance_ne_zero A hA)]
  simp_rw [precision_density A m _ hA,smul_eq_mul,mul_assoc]
  rw [integral_const_mul]

/-- For positive `A`, the volume integral of `x*exp (-A*(x-m)^2)` is `m*sqrt (π/A)`. -/
theorem integral_linear_quadratic (A m : ℝ) (hA : 0<A) :
    (∫ x,Real.exp (-A*(x-m)^2)*x)=m*Real.sqrt (Real.pi/A) := by
  have h := integral_precision_density A m hA (fun x=>x)
  rw [integral_id_gaussianReal] at h
  have hp : Real.sqrt (Real.pi/A)≠0 := (Real.sqrt_pos.2 (div_pos Real.pi_pos hA)).ne'
  field_simp at h ⊢
  nlinarith

/-- For positive `A`, the volume integral of `x^2*exp (-A*x^2)` is `sqrt (π/A)/(2*A)`. -/
theorem integral_square_quadratic (A : ℝ) (hA : 0<A) :
    (∫ x,Real.exp (-A*x^2)*x^2)=(1/(2*A))*Real.sqrt (Real.pi/A) := by
  have hv : (∫ x,x^2 ∂gaussianReal 0 (precisionVariance A hA))=(precisionVariance A hA:ℝ) := by
    have h := variance_id_gaussianReal (μ:=0) (v:=precisionVariance A hA)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa using h
  have h := integral_precision_density A 0 hA (fun x=>x^2)
  simp only [sub_zero] at h
  rw [hv] at h
  change 1/(2*A)=(Real.sqrt (Real.pi/A))⁻¹*_ at h
  have hp : Real.sqrt (Real.pi/A)≠0 := (Real.sqrt_pos.2 (div_pos Real.pi_pos hA)).ne'
  field_simp at h ⊢
  nlinarith

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
