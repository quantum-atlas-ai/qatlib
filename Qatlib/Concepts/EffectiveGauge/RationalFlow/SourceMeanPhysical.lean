/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanPlan
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanBound
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanInterval

set_option backward.isDefEq.respectTransparency false

/-!
# Source Mean Physical

Rational Flow constructions for Effective Gauge.
Defines `sourceMeanUnitBudget`, `sourceMeanPhysicalExecution`.
Proves `sourceMeanUnitBudget_nonneg`, `sourceMeanUnitBudget_le`, `sourceMeanPhysicalExecution_zero`.
-/


set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of source Mean Unit Budget in the Rational Flow construction. -/
def sourceMeanUnitBudget (m1 m2 tolerance : ℚ) : ℚ :=
  3*sourceMeanDerivativeBudget m1 m2/(sourceMeanMesh m1 m2 tolerance : ℚ)+
    2*(2^sourceMeanSampleBits m1 tolerance : ℚ)⁻¹*(7*m1+1)^2

/-- Original `sourceMeanUnitBudget_nonneg` guarantee for the `SourceMeanPhysical` construction; the complete source hypotheses are retained. -/
theorem sourceMeanUnitBudget_nonneg (m1 m2 tolerance : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) :
    0 ≤ sourceMeanUnitBudget m1 m2 tolerance := by
  dsimp [sourceMeanUnitBudget,sourceMeanDerivativeBudget]
  positivity

/-- Original `sourceMeanUnitBudget_le` guarantee for the `SourceMeanPhysical` construction; the complete source hypotheses are retained. -/
theorem sourceMeanUnitBudget_le (m1 m2 tolerance : ℚ) (ht : 0<tolerance) :
    sourceMeanUnitBudget m1 m2 tolerance ≤ tolerance/2 := by
  have hq := sourceMeanMesh_budget m1 m2 tolerance ht
  have hs := (sourceMeanSampleBits_budget m1 tolerance ht).2
  dsimp only [sourceMeanUnitBudget]
  linarith

/-- Definition of source Mean Physical Execution in the Rational Flow construction. -/
def sourceMeanPhysicalExecution (source : RationalJetSource) (m1 m2 tolerance : ℚ) :
    Option (Fin 3 → RationalMeanInterval) :=
  if m1=0 then some (fun _ => ⟨0,0⟩) else
  let error := sourceMeanUnitBudget m1 m2 tolerance
  let ell := sourceMeanLengthBits m1 tolerance
  let length := periodLower ell
  let width := (2^ell : ℚ)⁻¹
  (sourceMeanPlannedUnitExecution source m1 m2 tolerance).map
    (fun values j => meanIntervalQuotient (values j) error length width)

/-- The exact-zero branch evaluates neither the source nor a period routine. -/
theorem sourceMeanPhysicalExecution_zero (source : RationalJetSource) (m2 tolerance : ℚ) :
    sourceMeanPhysicalExecution source 0 m2 tolerance=some (fun _ => ⟨0,0⟩) := rfl

/-- Finite structural execution succeeds independently of the real-source
accuracy assumptions, which are used only for the subsequent error theorem. -/
theorem sourceMeanPhysicalExecution_success (source : RationalJetSource) (m1 m2 tolerance : ℚ) :
    ∃ intervals, sourceMeanPhysicalExecution source m1 m2 tolerance=some intervals := by
  by_cases h : m1=0
  · subst m1
    exact ⟨_,sourceMeanPhysicalExecution_zero source m2 tolerance⟩
  · rw [sourceMeanPhysicalExecution,if_neg h,sourceMeanPlannedUnitExecution,
      sourceMeanUnitExecution_eq source m1 m2 _ _ (sourceMeanMesh_pos m1 m2 tolerance),Option.map_some]
    exact ⟨_,rfl⟩

noncomputable section
open scoped ContDiff

/-- Original `sourceMeanPhysical_radius` guarantee for the `SourceMeanPhysical` construction; the complete source hypotheses are retained. -/
theorem sourceMeanPhysical_radius (a m1 m2 tolerance : ℚ)
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (ha : |a| ≤ (7*m1)^2/2+sourceMeanUnitBudget m1 m2 tolerance) :
    ((meanIntervalQuotient a (sourceMeanUnitBudget m1 m2 tolerance)
      (periodLower (sourceMeanLengthBits m1 tolerance))
      (2^sourceMeanLengthBits m1 tolerance : ℚ)⁻¹).radius : ℝ) ≤ (tolerance : ℝ) := by
  let E := sourceMeanUnitBudget m1 m2 tolerance
  let ell := sourceMeanLengthBits m1 tolerance
  have hE := sourceMeanUnitBudget_le m1 m2 tolerance ht
  have hE0 := sourceMeanUnitBudget_nonneg m1 m2 tolerance hm1 hm2
  have hl := periodLower_spec ell
  have hlQ : (6 : ℚ) ≤ periodLower ell := by exact_mod_cast hl.1.le
  have hrad := meanIntervalQuotient_radius_bound a E (periodLower ell) ((2^ell : ℚ)⁻¹)
    hE0 hlQ (by positivity)
  have hlen := sourceMeanLengthBits_budget m1 tolerance ht
  have hlenR : ((7*(m1 : ℝ))^2+1)*(2^ell : ℝ)⁻¹ ≤ (tolerance : ℝ)/64 := by
    simpa only [ell,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,Rat.cast_inv,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr hlen
  have hER : (E : ℝ) ≤ (tolerance : ℝ)/2 := by exact_mod_cast hE
  have haR : |(a : ℝ)| ≤ (7*(m1 : ℝ))^2/2+(E : ℝ) := by exact_mod_cast ha
  have htR : (tolerance : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hB : |(a : ℝ)|+(E : ℝ) ≤ (7*(m1 : ℝ))^2+1 := by nlinarith [sq_nonneg (7*(m1 : ℝ))]
  have hnum := (mul_le_mul_of_nonneg_right hB (by positivity : (0 : ℝ) ≤ (2^ell : ℝ)⁻¹)).trans hlenR
  push_cast at hrad
  change _ ≤ (tolerance : ℝ)
  have htpos : (0 : ℝ)<tolerance := by exact_mod_cast ht
  linarith

/-- Original `sourceMeanPhysicalExecution_correct` guarantee for the `SourceMeanPhysical` construction; the complete source hypotheses are retained. -/
theorem sourceMeanPhysicalExecution_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 tolerance : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (ht : 0<tolerance) (ht1 : tolerance ≤ 1)
    (hb : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ)) :
    ∃ intervals, sourceMeanPhysicalExecution source m1 m2 tolerance=some intervals ∧ ∀ j,
      let mean := -unitCubeIntegral (sourceCurvatureMoment (unitCoordinateSpin v) (sourceMeanMomentAxis j) j)/physicalPeriod
      ((intervals j).lower : ℝ) ≤ mean ∧ mean ≤ ((intervals j).upper : ℝ) ∧
        ((intervals j).radius : ℝ) ≤ (tolerance : ℝ) ∧
        |mean-((intervals j).midpoint : ℝ)| ≤ (tolerance : ℝ) := by
  by_cases hz : m1=0
  · subst m1
    refine ⟨fun _ => ⟨0,0⟩,rfl,?_⟩
    intro j
    have hzero := unitSourceMoment_integral_zero v hv hu
      (by simpa only [Rat.cast_zero,sourcePhysicalPartial] using hb.1) (sourceMeanMomentAxis j) j
    simpa only [hzero,neg_zero,zero_div,RationalMeanInterval.radius,RationalMeanInterval.midpoint,
      sub_self,zero_add,Rat.cast_zero,sub_zero,abs_zero,le_refl,true_and,and_self] using
      (Rat.cast_pos.mpr ht).le
  ·
    let N := sourceMeanMesh m1 m2 tolerance
    let b := sourceMeanSampleBits m1 tolerance
    let E := sourceMeanUnitBudget m1 m2 tolerance
    let ell := sourceMeanLengthBits m1 tolerance
    let length := periodLower ell
    let width := (2^ell : ℚ)⁻¹
    have hprec : (2^b : ℝ)⁻¹ ≤ 1/64 := by
      simpa only [b,Rat.cast_inv,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
        (Rat.cast_le (K := ℝ)).mpr (sourceMeanSampleBits_budget m1 tolerance ht).1
    obtain ⟨values,hex,herr⟩ := sourceMeanUnitExecution_error v hv hu source hs m1 m2 hm1 hm2 hb N b
      (sourceMeanMesh_pos m1 m2 tolerance) hprec
    have hplan : sourceMeanPlannedUnitExecution source m1 m2 tolerance=some values := hex
    let intervals := fun j => meanIntervalQuotient (values j) E length width
    refine ⟨intervals,?_,?_⟩
    · rw [sourceMeanPhysicalExecution,if_neg hz,hplan]
      rfl
    · intro j
      let J := unitCubeIntegral (sourceCurvatureMoment (unitCoordinateSpin v) (sourceMeanMomentAxis j) j)
      have herror : |(values j : ℝ)+J| ≤ (E : ℝ) := by
        simpa only [E,sourceMeanUnitBudget,sourceMeanDerivativeBudget,Rat.cast_add,Rat.cast_div,
          Rat.cast_mul,Rat.cast_pow,Rat.cast_inv,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one] using herr j
      have hnum : |-J-(values j : ℝ)| ≤ (E : ℝ) := by
        rw [show -J-(values j : ℝ)=-((values j : ℝ)+J) by ring,abs_neg]
        exact herror
      have hp := periodLower_spec ell
      have hperiod : (length : ℝ) ≤ physicalPeriod ∧ physicalPeriod ≤ (length+width : ℚ) := by
        constructor
        · exact hp.2.1
        · simpa only [length,width,Rat.cast_add,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat,add_comm] using
            sub_le_iff_le_add.mp hp.2.2.1
      have hsound := meanIntervalQuotient_sound (values j) E length width (-J) physicalPeriod
        (by linarith [hp.1]) hnum hperiod
      have hJ : |J| ≤ (7*(m1 : ℝ))^2/2 :=
        unitSourceMoment_integral_bound v hv hu (m1 : ℝ) (by exact_mod_cast hm1) hb.1 (sourceMeanMomentAxis j) j
      have htri := abs_sub_le (values j : ℝ) (-J) 0
      simp only [sub_zero,sub_neg_eq_add,abs_neg] at htri
      have hvalue : |values j| ≤ (7*m1)^2/2+E := by
        have hR : |(values j : ℝ)| ≤ (7*(m1 : ℝ))^2/2+(E : ℝ) := by linarith
        exact_mod_cast hR
      have hradius := sourceMeanPhysical_radius (values j) m1 m2 tolerance hm1 hm2 ht ht1 hvalue
      have hmid := rationalMeanInterval_midpoint_error (intervals j) (-J/physicalPeriod) hsound
      exact ⟨hsound.1,hsound.2,hradius,hmid.trans hradius⟩
end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
