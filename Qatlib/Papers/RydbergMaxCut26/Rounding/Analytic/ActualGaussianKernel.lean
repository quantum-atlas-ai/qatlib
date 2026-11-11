/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceMomentBound
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceAffineIntegral
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceEulerChart
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.TiltedSource
import Qatlib.Papers.RydbergMaxCut26.RatioBounds.EulerIntegral

/-!
# From Gaussian Laplace moments to the rounding kernel

This module rewrites `weightedMoment` using `halfAffine`, evaluates one positive-line integral,
and transforms the remaining Laplace integral into an Euler integral. `actualKernel_hypergeom`
then derives the rank-three normalized Gaussian kernel formula for correlations with absolute
value less than one.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `weightedMoment_first_integral`: performs the first Laplace integration.
* `actualKernel_euler`: identifies the Euler integral.
* `actualKernel_hypergeom`: obtains the interior hypergeometric formula.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
open Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedClosed
open Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedSource

/-- For `|t| < 1` and nonnegative Laplace parameters, the weighted Gaussian moment is `(3*t/sqrt
b)` times `halfAffine (1+2*b) (2+4*(1-t^2)*b) a`. -/
theorem weightedMoment_affine (t a b : ℝ) (ht : |t|<1) (ha : 0≤a) (hb : 0≤b) :
    weightedMoment t (a,b)=(3*t/Real.sqrt b)*halfAffine (1+2*b) (2+4*(1-t^2)*b) a := by
  have hpa : a^(-(1/2:ℝ))=1/Real.sqrt a := (inverse_sqrt_rpow a ha).symm
  have hpb : b^(-(1/2:ℝ))=1/Real.sqrt b := (inverse_sqrt_rpow b hb).symm
  have hd : determinant t a b=(1+2*b)+(2+4*(1-t^2)*b)*a := by
    unfold determinant
    ring
  rw [weightedMoment,actual_tilted_closed t a b ht ha hb,hpa,hpb,hd,halfAffine]
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- For `|t| < 1` and `b > 0`, integrating `weightedMoment t (a, b)` over the positive `a` line
gives `4*t*eulerLaplace t b`. -/
theorem weightedMoment_first_integral (t b : ℝ) (ht : |t|<1) (hb : 0<b) :
    (∫ a,weightedMoment t (a,b) ∂positiveLine)=4*t*eulerLaplace t b := by
  have hs : 0≤1-t^2 := by rw [← noise_square t ht];positivity
  have hA : 0<1+2*b := by linarith
  have hB : 0<2+4*(1-t^2)*b := by positivity
  have he : (∫ a,weightedMoment t (a,b) ∂positiveLine)=
      (3*t/Real.sqrt b)*∫ a,halfAffine (1+2*b) (2+4*(1-t^2)*b) a ∂positiveLine := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    exact weightedMoment_affine t a b ht ha.le hb.le
  rw [he,halfAffine_integral _ _ hA hB,eulerLaplace]
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- For `|t| < 1`, the actual Gaussian rounding kernel is `(4*t/π)` times the integral of
`(1-u^2)/sqrt (1-t^2*u^2)` from zero to one. -/
theorem actualKernel_euler (t : ℝ) (ht : |t|<1) :
    actualKernel t=(4*t/Real.pi)*∫ u in (0:ℝ)..1,(1-u^2)/Real.sqrt (1-t^2*u^2) := by
  have hh := abs_lt.mp ht
  have ht2 : t^2<1 := by nlinarith [sq_nonneg (t+1),sq_nonneg (t-1)]
  calc
    actualKernel t=Real.pi⁻¹*∫ ab,weightedMoment t ab ∂positiveLine.prod positiveLine := actualKernel_laplace t
    _ = Real.pi⁻¹*∫ b,∫ a,weightedMoment t (a,b) ∂positiveLine ∂positiveLine := by
      rw [integral_prod_symm _ (weightedMoment_integrable t)]
    _ = Real.pi⁻¹*∫ b,4*t*eulerLaplace t b ∂positiveLine := by
      congr 1
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with b hb
      exact weightedMoment_first_integral t b ht hb
    _ = _ := by
      rw [integral_const_mul,eulerLaplace_integral t ht2]
      ring

/-- For `|t| < 1`, the actual rank-three Gaussian rounding kernel equals `(8/(3*π))*t*₂F₁(1/2,
1/2; 5/2; t^2)`, giving the interior kernel formula used in [CrostaSaubanereHuber2026]. -/
theorem actualKernel_hypergeom (t : ℝ) (ht : |t|<1) :
    actualKernel t=(8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2) := by
  have hh := abs_lt.mp ht
  have ht2 : t^2<1 := by nlinarith [sq_nonneg (t+1),sq_nonneg (t-1)]
  rw [actualKernel_euler t ht,Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler.euler_integral (sq_nonneg t) ht2.le]
  unfold Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler.kernel
  ring

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
