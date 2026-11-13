/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.ActualGaussianKernel
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianSymmetry

/-!
# The Gaussian rounding kernel on the closed interval

`actualKernel_hypergeom_closed` extends the interior hypergeometric formula to correlations of
absolute value one by using the exact endpoint kernel and hypergeometric values.
`roundedLaw_hypergeom` expresses the expected inner product under the actual rounded-pair law by
this formula for every correlation in [−1, 1].

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `actualKernel_hypergeom_closed`: evaluates the kernel on the closed correlation interval.
* `roundedLaw_hypergeom`: evaluates the rounded-law expected inner product.

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

/-- For `|t| ≤ 1`, the actual rank-three Gaussian kernel equals `(8/(3*π))*t*₂F₁(1/2, 1/2; 5/2;
t^2)`, including both endpoints. This is the closed-interval rank-three specialization of
the kernel in [Crosta et al., Lemma 5][CrostaSaubanereHuber2026]. -/
theorem actualKernel_hypergeom_closed (t : ℝ) (ht : |t|≤1) :
    actualKernel t=(8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2) := by
  by_cases hi : |t|<1
  · exact actualKernel_hypergeom t hi
  have he : |t|=1 := le_antisymm ht (le_of_not_gt hi)
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp he with h|h
  · subst t
    rw [actualKernel_one]
    norm_num only [one_pow,Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler.gauss_endpoint_one]
    field_simp
  · subst t
    rw [actualKernel_neg_one]
    norm_num only [neg_sq,one_pow,Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler.gauss_endpoint_one]
    field_simp

/-- For `|t| ≤ 1`, the expected inner product under `roundedLaw t` equals `(8/(3*π))*t*₂F₁(1/2,
1/2; 5/2; t^2)`. -/
theorem roundedLaw_hypergeom (t : ℝ) (ht : |t|≤1) :
    (∫ p,inner ℝ p.1 p.2 ∂roundedLaw t)=
      (8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2) := by
  rw [roundedLaw_expect,actualKernel_hypergeom_closed t ht]

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
