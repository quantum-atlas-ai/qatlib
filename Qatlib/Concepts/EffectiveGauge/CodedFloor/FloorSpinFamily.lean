/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCubeJets
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Spin Family

Coded Floor constructions for Effective Gauge.
Defines `quaternionSpinProjection`, `floorPeriodicSpin`, `floorRawSpin`.
Proves `spinOfVector_quaternionSpinProjection`, `contDiff_hopf_field`, `floorPeriodicSpin_contDiff`.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Definition of quaternion Spin Projection in the Coded Floor construction. -/
def quaternionSpinProjection : ℍ →L[ℝ] SpatialPoint :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 => quaternionCoordinateCLM ⟨i.val+1,by omega⟩))

/-- Projecting a quaternion of real part zero to its imaginary coordinates and embedding the
resulting vector as a spin recovers the quaternion. -/
theorem spinOfVector_quaternionSpinProjection (q : ℍ) (hq : q.re=0) :
    spinOfVector (quaternionSpinProjection q)=q := by
  apply Quaternion.ext
  · exact hq.symm
  · rfl
  · rfl
  · rfl

/-- Definition of floor Periodic Spin in the Coded Floor construction. -/
def floorPeriodicSpin (a : ℝ) (X : SpatialPoint) : SpatialPoint :=
  quaternionSpinProjection (hopf (floorPeriodicLift a X))

/-- Definition of floor Raw Spin in the Coded Floor construction. -/
def floorRawSpin (a : ℝ) (X : SpatialPoint) : SpatialPoint :=
  quaternionSpinProjection (hopf (floorRawLift a X))

/-- The pointwise Hopf map of any smooth quaternion field is a smooth quaternion field. -/
theorem contDiff_hopf_field (q : QuaternionField) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun X => hopf (q X)) :=
  (((starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.contDiff.comp hq).mul contDiff_const).mul hq

/-- The periodic spin is smooth as a function of position, for each amplitude. -/
theorem floorPeriodicSpin_contDiff (a : ℝ) : ContDiff ℝ ∞ (floorPeriodicSpin a) :=
  quaternionSpinProjection.contDiff.comp (contDiff_hopf_field _ (floorPeriodicLift_contDiff a))

/-- The raw spin is smooth on the full spatial domain, for each amplitude. -/
theorem floorRawSpin_contDiff (a : ℝ) : ContDiff ℝ ∞ (floorRawSpin a) :=
  quaternionSpinProjection.contDiff.comp (contDiff_hopf_field _ (contDiff_floorRawLift a))

/-- The Hopf image of the periodic lift is the pure quaternion corresponding to the periodic spin
vector. -/
theorem floorPeriodicLift_hopf (a : ℝ) (X : SpatialPoint) :
    hopf (floorPeriodicLift a X)=spinOfVector (floorPeriodicSpin a X) :=
  (spinOfVector_quaternionSpinProjection _ (hopf_re _)).symm

/-- The periodic spin is a unit vector at every spatial point. -/
theorem floorPeriodicSpin_norm (a : ℝ) (X : SpatialPoint) : ‖floorPeriodicSpin a X‖=1 := by
  rw [← spinOfVector_norm,← floorPeriodicLift_hopf,hopf_norm,floorPeriodicLift_norm]
  norm_num

/-- The periodic spin is invariant under the period translations. -/
theorem floorPeriodicSpin_periodic (a : ℝ) : IsPeriodicField (floorPeriodicSpin a) := by
  intro X n
  change quaternionSpinProjection (hopf (floorPeriodicLift a (X+latticeShift n)))=
    quaternionSpinProjection (hopf (floorPeriodicLift a X))
  rw [floorPeriodicLift_periodic]

/-- At any point of the fundamental cube, the periodic spin equals the raw spin. -/
theorem floorPeriodicSpin_eq_raw_on_cube (a : ℝ) (X : SpatialPoint) (hX : InFundamentalCube X) :
    floorPeriodicSpin a X=floorRawSpin a X := by
  change quaternionSpinProjection (hopf (floorPeriodicLift a X))=
    quaternionSpinProjection (hopf (floorRawLift a X))
  rw [floorPeriodicLift_eq_raw_on_cube a X hX]

/-- The periodic and raw spins have the same derivatives along every coordinate word at each point
of the fundamental cube. -/
theorem floorPeriodicSpin_word_eq_raw (a : ℝ) (w : List (Fin 3)) (X : SpatialPoint)
    (hX : InFundamentalCube X) :
    spatialWordPartial (floorPeriodicSpin a) w X=spatialWordPartial (floorRawSpin a) w X :=
  spatialWordPartial_eq_on_closedPhysicalCube _ _ (floorPeriodicSpin_contDiff a) (floorRawSpin_contDiff a)
    (floorPeriodicSpin_eq_raw_on_cube a) w X hX

/-- Each coordinate of a point in the family's closed unit ball lies in the interval `[2, 4]`. -/
theorem floorFamilyBall_coordinates (X : SpatialPoint) (hX : X∈closedBall floorFamilyCenter 1) (i : Fin 3) :
    2 ≤ X i ∧ X i ≤ 4 := by
  have hnorm : ‖X-floorFamilyCenter‖ ≤ 1 := by simpa only [dist_eq_norm] using (mem_closedBall.mp hX)
  have hcoord := (PiLp.norm_apply_le (X-floorFamilyCenter) i).trans hnorm
  change ‖X i-3‖ ≤ 1 at hcoord
  rw [Real.norm_eq_abs] at hcoord
  have h := abs_le.mp hcoord
  constructor <;> linarith

/-- The closed unit ball centered at the family center is contained in the fundamental cube. -/
theorem floorFamilyBall_in_cube : ∀ X∈closedBall floorFamilyCenter 1, InFundamentalCube X := by
  intro X hX i
  have h := floorFamilyBall_coordinates X hX i
  have hL : 6<physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  exact ⟨by linarith,by linarith⟩

/-- Every point of the family's closed unit ball is at distance at least one from every point of
the cube boundary. -/
theorem floorFamilyBall_gap : ∀ X∈closedBall floorFamilyCenter 1, ∀ Y, OnCubeBoundary Y → 1 ≤ ‖X-Y‖ := by
  intro X hX Y hY
  obtain ⟨i,hi⟩ := hY.2
  have hx := floorFamilyBall_coordinates X hX i
  have hcoord := PiLp.norm_apply_le (X-Y) i
  change ‖X i-Y i‖ ≤ ‖X-Y‖ at hcoord
  rw [Real.norm_eq_abs] at hcoord
  have hL : 6<physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  rcases hi with hi|hi
  · rw [hi,sub_zero,abs_of_nonneg (by linarith : 0 ≤ X i)] at hcoord
    linarith
  · rw [hi,abs_of_nonpos (by linarith : X i-physicalPeriod ≤ 0)] at hcoord
    linarith

/-- Inside the fundamental cube and outside the family's closed unit ball, the periodic lift
equals the unit quaternion. -/
theorem floorPeriodicLift_one_off_ball (a : ℝ) (X : SpatialPoint) (hX : InFundamentalCube X)
    (hx : X∉closedBall floorFamilyCenter 1) : floorPeriodicLift a X=1 := by
  rw [floorPeriodicLift_eq_raw_on_cube a X hX]
  apply floorRawLift_one_of_bump_zero
  apply floorInteriorBump_off_ball
  have h : 1<dist X floorFamilyCenter := lt_of_not_ge (fun h => hx (mem_closedBall.mpr h))
  simpa only [dist_eq_norm] using h.le

/-- The periodic spin has the same value at any two fundamental-cube points outside the family's
closed unit ball. -/
theorem floorPeriodicSpin_constant_off_ball (a : ℝ) (X Y : SpatialPoint)
    (hX : InFundamentalCube X) (hY : InFundamentalCube Y)
    (hx : X∉closedBall floorFamilyCenter 1) (hy : Y∉closedBall floorFamilyCenter 1) :
    floorPeriodicSpin a X=floorPeriodicSpin a Y := by
  change quaternionSpinProjection (hopf (floorPeriodicLift a X))=
    quaternionSpinProjection (hopf (floorPeriodicLift a Y))
  rw [floorPeriodicLift_one_off_ball a X hX hx,floorPeriodicLift_one_off_ball a Y hY hy]

/-- Every coordinate of the periodic lift's connection vanishes on the cube boundary. -/
theorem floorPeriodicLift_connection_boundary (a : ℝ) (X : SpatialPoint) (hX : OnCubeBoundary X) (i : Fin 3) :
    connection (floorPeriodicLift a) X i=0 := by
  have hseam : ∃ j, wrapCoordinate (X j)=0 := by
    obtain ⟨j,hj⟩ := hX.2
    refine ⟨j,?_⟩
    rcases hj with hj|hj <;> rw [hj]
    · simp [wrapCoordinate]
    · simp [wrapCoordinate,physicalPeriod_pos.ne']
  have heq := periodicExtension_eventually_constant_of_seam _ (1/2) (by norm_num)
    (by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]) 1 (floorRawLift_collar a) X hseam
  have hd : fderiv ℝ (floorPeriodicLift a) X=0 := by simpa only [floorPeriodicLift,fderiv_const_apply] using heq.fderiv_eq (𝕜 := ℝ)
  simp [connection,spatialPartial,connectionValue,hd]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
