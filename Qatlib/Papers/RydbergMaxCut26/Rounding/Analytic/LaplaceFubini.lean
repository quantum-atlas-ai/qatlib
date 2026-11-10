/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceNorm
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

theorem positiveParameters_ae :
    ∀ᵐ ab ∂positiveLine.prod positiveLine,0≤ab.1 ∧ 0≤ab.2 := by
  rw [positiveLine,Measure.prod_restrict]
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi.prod measurableSet_Ioi)] with ab hab
  exact ⟨hab.1.le,hab.2.le⟩

theorem weightedDot_norm_integral (x y : V) :
    (∫ ab,‖weightedDot x y ab‖ ∂positiveLine.prod positiveLine)=
      Real.pi*|inner ℝ (unitVector x) (unitVector y)| := by
  have he : (∫ ab,‖weightedDot x y ab‖ ∂positiveLine.prod positiveLine)=
      |∫ ab,weightedDot x y ab ∂positiveLine.prod positiveLine| := by
    rcases le_total 0 (inner ℝ x y) with h|h
    · have hs : ∀ᵐ ab ∂positiveLine.prod positiveLine,0≤weightedDot x y ab := by
        filter_upwards [positiveParameters_ae] with ab hab
        exact mul_nonneg (mul_nonneg h (weight_nonneg _ hab.1)) (weight_nonneg _ hab.2)
      rw [abs_of_nonneg (integral_nonneg_of_ae hs)]
      exact integral_congr_ae (hs.mono (fun _ ha => Real.norm_of_nonneg ha))
    · have hs : ∀ᵐ ab ∂positiveLine.prod positiveLine,weightedDot x y ab≤0 := by
        filter_upwards [positiveParameters_ae] with ab hab
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg h (weight_nonneg _ hab.1)) (weight_nonneg _ hab.2)
      rw [abs_of_nonpos (integral_nonpos_of_ae hs),← integral_neg]
      exact integral_congr_ae (hs.mono (fun _ ha => Real.norm_of_nonpos ha))
  rw [he,weightedDot_integral,abs_mul,abs_of_pos Real.pi_pos]

theorem weightedDot_measurable :
    Measurable (fun p : (V×V)×(ℝ×ℝ) => weightedDot p.1.1 p.1.2 p.2) := by
  unfold weightedDot weight
  fun_prop

theorem weightedDot_joint_integrable (μ : Measure (V×V)) [IsProbabilityMeasure μ] :
    Integrable (fun p : (V×V)×(ℝ×ℝ) => weightedDot p.1.1 p.1.2 p.2)
      (μ.prod (positiveLine.prod positiveLine)) := by
  apply (integrable_prod_iff weightedDot_measurable.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun w => weightedDot_integrable w.1 w.2)
  · have hm : Measurable (fun w : V×V =>
        Real.pi*|inner ℝ (unitVector w.1) (unitVector w.2)|) := by
      unfold unitVector
      fun_prop
    have hi : Integrable (fun w : V×V =>
        Real.pi*|inner ℝ (unitVector w.1) (unitVector w.2)|) μ := by
      apply (integrable_const Real.pi).mono' hm.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro w
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos,abs_abs]
      exact mul_le_of_le_one_right Real.pi_pos.le (unit_inner_bound _ _)
    exact hi.congr (Filter.Eventually.of_forall (fun w => (weightedDot_norm_integral w.1 w.2).symm))

theorem normalized_dot_laplace (μ : Measure (V×V)) [IsProbabilityMeasure μ] :
    (∫ w,inner ℝ (unitVector w.1) (unitVector w.2) ∂μ)=
      Real.pi⁻¹*∫ ab,∫ w,weightedDot w.1 w.2 ab ∂μ ∂positiveLine.prod positiveLine := by
  have h := integral_integral_swap (μ:=μ) (ν:=positiveLine.prod positiveLine)
    (f:=fun (w : V×V) (ab : ℝ×ℝ) => weightedDot w.1 w.2 ab) (weightedDot_joint_integrable μ)
  change (∫ w,∫ ab,weightedDot w.1 w.2 ab ∂positiveLine.prod positiveLine ∂μ)=_ at h
  simp_rw [weightedDot_integral] at h
  rw [integral_const_mul] at h
  rw [← h]
  exact (inv_mul_cancel_left₀ Real.pi_ne_zero _).symm

def tiltedMoment (t a b : ℝ) : ℝ :=
  ∫ w : V×V,inner ℝ w.1 (correlated t w)*
    Real.exp (-(a*‖w.1‖^2+b*‖correlated t w‖^2)) ∂sourceLaw

theorem actualKernel_laplace (t : ℝ) :
    actualKernel t=Real.pi⁻¹*∫ ab : ℝ×ℝ,
      ab.1^(-(1/2:ℝ))*ab.2^(-(1/2:ℝ))*tiltedMoment t ab.1 ab.2 ∂positiveLine.prod positiveLine := by
  have hm : Measurable (fun w : V×V => inner ℝ (unitVector w.1) (unitVector w.2)) := by
    unfold unitVector
    fun_prop
  have hmap : (∫ w,inner ℝ (unitVector w.1) (unitVector w.2) ∂correlatedLaw t)=actualKernel t := by
    rw [correlatedLaw,integral_map (pairLinear t).measurable.aemeasurable hm.aestronglyMeasurable]
    rfl
  rw [← hmap,normalized_dot_laplace]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ab
  have hmw : Measurable (fun w : V×V => weightedDot w.1 w.2 ab) := by
    unfold weightedDot weight
    fun_prop
  (try dsimp only)
  rw [correlatedLaw,integral_map (pairLinear t).measurable.aemeasurable hmw.aestronglyMeasurable]
  change (∫ w : V×V,weightedDot w.1 (correlated t w) ab ∂sourceLaw)=_
  rw [tiltedMoment,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  simp only [weightedDot,weight,neg_add,Real.exp_add]
  rw [show -(‖w.1‖^2*ab.1)= -(ab.1*‖w.1‖^2) by ring,
    show -(‖correlated t w‖^2*ab.2)= -(ab.2*‖correlated t w‖^2) by ring]
  ring

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
