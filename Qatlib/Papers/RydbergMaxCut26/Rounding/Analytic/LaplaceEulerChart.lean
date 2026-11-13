/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.PositiveChart
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Euler substitution for the Laplace kernel

The function `eulerLaplace` is the one-dimensional integrand arising in the Gaussian rounding
calculation. The substitution `positiveChart (1/2)` transforms its integral over the positive
half-line into an Euler integral on the unit interval. See [CrostaSaubanereHuber2026].

## Main statements

* `eulerLaplace_chart`: evaluates the transformed integrand including its Jacobian.
* `eulerLaplace_integral`: identifies the positive-half-line integral with the Euler integral.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
open MeasureTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

/-- The Laplace integrand `1 / (√b * √(2 + 4 * (1 - t²) * b) * (1 + 2 * b)²)`. -/
def eulerLaplace (t b : ℝ) : ℝ :=
  1/(Real.sqrt b*Real.sqrt (2+4*(1-t^2)*b)*(1+2*b)^2)

/-- For `t² < 1` and `0 < u < 1`, the substitution `positiveChart (1/2) u`, including its
derivative, transforms `eulerLaplace` into `(1 - u²) / √(1 - t² * u²)`. -/
theorem eulerLaplace_chart (t u : ℝ) (ht : t^2<1) (hu : u∈Ioo (0:ℝ) 1) :
    (2*(1/2:ℝ)*u/(1-u^2)^2)*eulerLaplace t (positiveChart (1/2) u)=
      (1-u^2)/Real.sqrt (1-t^2*u^2) := by
  have hq := chart_den_pos hu
  have hu2 : u^2<1 := by linarith [hq]
  have htu : 0<1-t^2*u^2 := by
    have hh := mul_le_mul_of_nonneg_left hu2.le (sq_nonneg t)
    nlinarith
  have hb : Real.sqrt (positiveChart (1/2) u)=u/(Real.sqrt 2*Real.sqrt (1-u^2)) := by
    rw [positiveChart,Real.sqrt_div (mul_nonneg (by norm_num) (sq_nonneg u)),
      Real.sqrt_mul (by norm_num),Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_sq hu.1.le]
    ring
  have h1 : 1+2*positiveChart (1/2) u=1/(1-u^2) := by
    unfold positiveChart
    field_simp
    ring
  have h2 : 2+4*(1-t^2)*positiveChart (1/2) u=2*(1-t^2*u^2)/(1-u^2) := by
    unfold positiveChart
    field_simp
    ring
  rw [eulerLaplace,hb,h1,h2,Real.sqrt_div (mul_nonneg (by norm_num) htu.le),
    Real.sqrt_mul (by norm_num)]
  have hs2 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hsQ := (Real.sqrt_pos.mpr hq).ne'
  have hsT := (Real.sqrt_pos.mpr htu).ne'
  field_simp [hu.1.ne']
  rw [Real.sq_sqrt hq.le]

/-- For `t² < 1`, the integral of `eulerLaplace t` over the positive half-line equals the
integral of `(1 - u²) / √(1 - t² * u²)` from zero to one. -/
theorem eulerLaplace_integral (t : ℝ) (ht : t^2<1) :
    (∫ b in Ioi (0:ℝ),eulerLaplace t b)=
      ∫ u in (0:ℝ)..1,(1-u^2)/Real.sqrt (1-t^2*u^2) := by
  rw [positiveChart_integral (by norm_num : (0:ℝ)<1/2)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo (fun u hu => eulerLaplace_chart t u ht hu)

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
