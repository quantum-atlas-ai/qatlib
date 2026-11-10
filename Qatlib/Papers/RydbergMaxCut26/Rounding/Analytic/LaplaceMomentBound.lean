/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceFubini
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

def weightedMoment (t : ℝ) (ab : ℝ×ℝ) : ℝ :=
  ab.1^(-(1/2:ℝ))*ab.2^(-(1/2:ℝ))*tiltedMoment t ab.1 ab.2

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

theorem weightedMoment_integrable (t : ℝ) : Integrable (weightedMoment t) (positiveLine.prod positiveLine) := by
  have hi := (weightedDot_joint_integrable (correlatedLaw t)).integral_prod_right
  exact hi.congr (Filter.Eventually.of_forall (fun ab => (weightedMoment_eq t ab).symm))

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
