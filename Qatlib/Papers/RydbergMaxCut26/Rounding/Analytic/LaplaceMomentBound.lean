/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceFubini

/-!
# Integrability of the weighted tilted moment

The function `weightedMoment` combines the tilted Gaussian inner-product moment with the two
inverse square-root Laplace weights. Its identification with an integral against `correlatedLaw`
yields integrability over the positive parameters. See [CrostaSaubanereHuber2026].

## Main statements

* `weightedMoment_eq`: rewrites the weighted moment using `weightedDot` and `correlatedLaw`.
* `weightedMoment_integrable`: establishes integrability over both positive parameters.

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

/-- The tilted moment multiplied by the Laplace weights `a^(-1/2) * b^(-1/2)`. -/
def weightedMoment (t : ℝ) (ab : ℝ×ℝ) : ℝ :=
  ab.1^(-(1/2:ℝ))*ab.2^(-(1/2:ℝ))*tiltedMoment t ab.1 ab.2

/-- The weighted tilted moment equals the integral of `weightedDot` against the correlated
Gaussian law. -/
theorem weightedMoment_eq (t : ℝ) (ab : ℝ×ℝ) :
    weightedMoment t ab=∫ w,weightedDot w.1 w.2 ab ∂correlatedLaw t := by
  have hmw : Measurable (fun w : V×V => weightedDot w.1 w.2 ab) := by
    unfold weightedDot weight
    fun_prop
  rw [correlatedLaw,integral_map (pairLinear t).measurable.aemeasurable hmw.aestronglyMeasurable]
  change weightedMoment t ab=(∫ w : V×V,weightedDot w.1 (correlated t w) ab ∂sourceLaw)
  rw [weightedMoment,tiltedMoment,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  simp only [weightedDot,weight,neg_add,Real.exp_add]
  rw [show -(‖w.1‖^2*ab.1)= -(ab.1*‖w.1‖^2) by ring,
    show -(‖correlated t w‖^2*ab.2)= -(ab.2*‖correlated t w‖^2) by ring]
  ring

/-- For every real correlation parameter, `weightedMoment` is integrable over the product of the
positive-half-line measures. -/
theorem weightedMoment_integrable (t : ℝ) : Integrable (weightedMoment t) (positiveLine.prod positiveLine) := by
  have hi := (weightedDot_joint_integrable (correlatedLaw t)).integral_prod_right
  exact hi.congr (Filter.Eventually.of_forall (fun ab => (weightedMoment_eq t ab).symm))

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
