/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorLiftConnection
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanBound
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Regular

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Mean Sign

Coded Floor constructions for Effective Gauge.
Defines `floorSinEnergy`, `floorMeanCandidate`.
Proves `floorSinEnergy_continuous`, `floorSinEnergy_nonneg`, `floorSinEnergy_le`.
-/

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Sin Energy in the Coded Floor construction. -/
def floorSinEnergy (a : ℝ) (X : SpatialPoint) : ℝ := (Real.sin (a*floorInteriorBump X))^2

/-- Definition of floor Mean Candidate in the Coded Floor construction. -/
def floorMeanCandidate (a : ℝ) : ℝ := -physicalCubeMean (floorSinEnergy a)

/-- Original `floorSinEnergy_continuous` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorSinEnergy_continuous (a : ℝ) : Continuous (floorSinEnergy a) :=
  (((contDiff_const.mul contDiff_floorInteriorBump).sin).pow 2).continuous

/-- Original `floorSinEnergy_nonneg` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorSinEnergy_nonneg (a : ℝ) (X : SpatialPoint) : 0 ≤ floorSinEnergy a X := sq_nonneg _

/-- Original `floorSinEnergy_le` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorSinEnergy_le (a : ℝ) (ha : 0 ≤ a) (X : SpatialPoint) : floorSinEnergy a X ≤ a^2 := by
  have ht : 0 ≤ a*floorInteriorBump X := mul_nonneg ha (floorInteriorBump_nonneg X)
  have hle : a*floorInteriorBump X ≤ a := by nlinarith [floorInteriorBump_le_one X]
  have hsin : |Real.sin (a*floorInteriorBump X)| ≤ a :=
    (Real.abs_sin_le_abs).trans (by rw [abs_of_nonneg ht]; exact hle)
  simpa only [floorSinEnergy,sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr hsin

/-- Original `floorSinEnergy_compactSupport` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorSinEnergy_compactSupport (a : ℝ) : HasCompactSupport (floorSinEnergy a) := by
  apply HasCompactSupport.intro (isCompact_closedBall floorFamilyCenter 1)
  intro X hX
  have hnorm : 1<‖X-floorFamilyCenter‖ := by
    have h : 1<dist X floorFamilyCenter := lt_of_not_ge (fun h => hX (mem_closedBall.mpr h))
    simpa only [dist_eq_norm] using h
  simp only [floorSinEnergy,floorInteriorBump_off_ball X hnorm.le,mul_zero,Real.sin_zero,zero_pow (by decide : 2≠0)]

/-- Original `floorSinEnergy_pos_on_ball` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorSinEnergy_pos_on_ball (a : ℝ) (ha : 0<a) (ha1 : a ≤ 1/16)
    (X : SpatialPoint) (hX : X∈ball floorFamilyCenter 1) : 0<floorSinEnergy a X := by
  have hnorm : ‖X-floorFamilyCenter‖<1 := by simpa only [dist_eq_norm] using (mem_ball.mp hX)
  have hp : 0<floorBumpArgument X := by
    rw [floorBumpArgument_eq_norm]
    nlinarith [norm_nonneg (X-floorFamilyCenter)]
  have hpos : 0<floorInteriorBump X := expNegInvGlue.pos_of_pos hp
  have htheta : a*floorInteriorBump X< Real.pi := by
    have hle : a*floorInteriorBump X ≤ a := by nlinarith [floorInteriorBump_le_one X]
    linarith [Real.pi_gt_three]
  exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos ha hpos) htheta)

/-- Original `floorSinEnergy_physicalIntegral_pos` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorSinEnergy_physicalIntegral_pos (a : ℝ) (ha : 0<a) (ha1 : a ≤ 1/16) :
    0<physicalCubeIntegral (floorSinEnergy a) := by
  let cube := {X : SpatialPoint | InFundamentalCube X}
  have hg := floorSinEnergy_continuous a
  have hi : Integrable (floorSinEnergy a) (volume : Measure SpatialPoint) :=
    hg.integrable_of_hasCompactSupport (floorSinEnergy_compactSupport a)
  have hs : MeasurableSet (Function.support (floorSinEnergy a)) :=
    (isOpen_ne_fun hg (continuous_const : Continuous (fun _ : SpatialPoint => (0 : ℝ)))).measurableSet
  have hsubset : ball floorFamilyCenter 1 ⊆ Function.support (floorSinEnergy a) ∩ cube := by
    intro X hX
    exact ⟨(floorSinEnergy_pos_on_ball a ha ha1 X hX).ne',floorFamilyBall_in_cube X (ball_subset_closedBall hX)⟩
  have hm : 0<(volume.restrict cube) (Function.support (floorSinEnergy a)) := by
    rw [Measure.restrict_apply hs]
    exact (measure_ball_pos (volume : Measure SpatialPoint) floorFamilyCenter (by norm_num : (0 : ℝ)<1)).trans_le
      (measure_mono hsubset)
  rw [physicalCubeIntegral_eq_volume]
  exact (integral_pos_iff_support_of_nonneg (floorSinEnergy_nonneg a) hi.integrableOn).mpr hm

/-- Original `floorMeanCandidate_neg` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorMeanCandidate_neg (a : ℝ) (ha : 0<a) (ha1 : a ≤ 1/16) : floorMeanCandidate a<0 := by
  have h : 0<physicalCubeMean (floorSinEnergy a) :=
    div_pos (floorSinEnergy_physicalIntegral_pos a ha ha1) (pow_pos physicalPeriod_pos 3)
  exact neg_neg_of_pos h

/-- Original `floorMeanCandidate_abs_le` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorMeanCandidate_abs_le (a : ℝ) (ha : 0 ≤ a) : |floorMeanCandidate a| ≤ a^2 := by
  rw [floorMeanCandidate,abs_neg,physicalCubeMean_scale]
  apply unitCubeIntegral_abs_le
  intro u _
  rw [abs_of_nonneg (floorSinEnergy_nonneg a _)]
  exact floorSinEnergy_le a ha _

/-- Original `floorMeanCandidate_floor_of_pos` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorMeanCandidate_floor_of_pos (a : ℝ) (ha : 0<a) (ha1 : a ≤ 1/16) :
    ⌊floorMeanCandidate a⌋=(-1 : ℤ) := by
  have hm := floorMeanCandidate_neg a ha ha1
  have habs := floorMeanCandidate_abs_le a ha.le
  have hsq : a^2 ≤ (1/16 : ℝ)^2 := (sq_le_sq₀ ha.le (by norm_num)).mpr ha1
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num
  · have h := (abs_le.mp habs).1
    nlinarith
  · exact hm

/-- Original `floorMeanCandidate_zero` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorMeanCandidate_zero : floorMeanCandidate 0=0 := by
  have heq : floorSinEnergy 0=fun _ : SpatialPoint => (0 : ℝ) := by
    funext X
    simp [floorSinEnergy]
  rw [floorMeanCandidate,heq,physicalCubeMean_const,neg_zero]

/-- Original `floorMeanCandidate_floor_zero` guarantee for the `FloorMeanSign` construction; the complete source hypotheses are retained. -/
theorem floorMeanCandidate_floor_zero : ⌊floorMeanCandidate 0⌋=(0 : ℤ) := by rw [floorMeanCandidate_zero]; norm_num

end Qatlib.Concepts.EffectiveGauge.CodedFloor
