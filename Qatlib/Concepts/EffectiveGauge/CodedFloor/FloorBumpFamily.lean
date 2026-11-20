/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactPolynomial
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicExtension
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffPolynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Bump Family

Coded Floor constructions for Effective Gauge.
Defines `floorFamilyCenter`, `floorBumpArgument`, `floorInteriorBump`.
Proves `contDiff_floorInteriorBump`, `floorInteriorBump_nonneg`, `floorInteriorBump_le_one`.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Family Center in the Coded Floor construction. -/
def floorFamilyCenter : SpatialPoint := WithLp.toLp 2 (fun _ => (3 : ℝ))

/-- Definition of floor Bump Argument in the Coded Floor construction. -/
def floorBumpArgument (X : SpatialPoint) : ℝ := 1-∑ i : Fin 3, (X i-3)^2

/-- Definition of floor Interior Bump in the Coded Floor construction. -/
def floorInteriorBump (X : SpatialPoint) : ℝ := expNegInvGlue (floorBumpArgument X)

/-- The interior bump is smooth on the entire real three-dimensional spatial domain. -/
theorem contDiff_floorInteriorBump : ContDiff ℝ ∞ floorInteriorBump := by
  have hp : ContDiff ℝ ∞ floorBumpArgument :=
    contDiff_const.sub (ContDiff.sum (s := Finset.univ) (fun i _ =>
      ((EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).contDiff.sub contDiff_const).pow 2))
  exact expNegInvGlue.contDiff.comp hp

/-- The interior bump is nonnegative at every spatial point. -/
theorem floorInteriorBump_nonneg (X : SpatialPoint) : 0 ≤ floorInteriorBump X :=
  expNegInvGlue.nonneg _

/-- The interior bump never exceeds one. -/
theorem floorInteriorBump_le_one (X : SpatialPoint) : floorInteriorBump X ≤ 1 := by
  by_cases hp : floorBumpArgument X ≤ 0
  · simp only [floorInteriorBump,expNegInvGlue.zero_of_nonpos hp]
    norm_num
  · change expNegInvGlue (floorBumpArgument X) ≤ 1
    rw [expNegInvGlue,ite_eq_right hp]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (not_le.mp hp).le))

/-- The bump argument is one minus the squared distance from the family center. -/
theorem floorBumpArgument_eq_norm (X : SpatialPoint) :
    floorBumpArgument X=1-‖X-floorFamilyCenter‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The interior bump vanishes at distance at least one from the family center. -/
theorem floorInteriorBump_off_ball (X : SpatialPoint) (hx : 1 ≤ ‖X-floorFamilyCenter‖) :
    floorInteriorBump X=0 := by
  apply expNegInvGlue.zero_of_nonpos
  rw [floorBumpArgument_eq_norm]
  nlinarith [norm_nonneg (X-floorFamilyCenter)]

/-- The bump has strictly positive value at the family center. -/
theorem floorInteriorBump_center_pos : 0<floorInteriorBump floorFamilyCenter := by
  apply expNegInvGlue.pos_of_pos
  norm_num [floorBumpArgument,floorFamilyCenter]

/-- Definition of floor Raw Lift in the Coded Floor construction. -/
def floorRawLift (a : ℝ) (X : SpatialPoint) : ℍ :=
  let theta := a*floorInteriorBump X
  let phi := -X 1
  quaternionTupleCLM ![Real.cos theta,0,Real.sin theta*Real.cos phi,Real.sin theta*Real.sin phi]

/-- The raw lift has real component the cosine of the bump-scaled parameter and zero first
imaginary component. Its other two components multiply the corresponding sine by the cosine and
sine of `-X 1`. -/
theorem floorRawLift_mk (a : ℝ) (X : SpatialPoint) :
    floorRawLift a X=⟨Real.cos (a*floorInteriorBump X),0,
      Real.sin (a*floorInteriorBump X)*Real.cos (-X 1),Real.sin (a*floorInteriorBump X)*Real.sin (-X 1)⟩ := rfl

/-- For any real parameter, the raw quaternion lift is smooth as a function of position. -/
theorem contDiff_floorRawLift (a : ℝ) : ContDiff ℝ ∞ (floorRawLift a) := by
  have ht : ContDiff ℝ ∞ (fun X => a*floorInteriorBump X) := contDiff_const.mul contDiff_floorInteriorBump
  have hp : ContDiff ℝ ∞ (fun X : SpatialPoint => -X 1) :=
    (EuclideanSpace.proj (1 : Fin 3) : SpatialPoint →L[ℝ] ℝ).contDiff.neg
  apply quaternionTupleCLM.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact ht.cos
  · exact contDiff_const
  · exact ht.sin.mul hp.cos
  · exact ht.sin.mul hp.sin

/-- The raw quaternion lift has norm one at every point for any real parameter. -/
theorem floorRawLift_norm (a : ℝ) (X : SpatialPoint) : ‖floorRawLift a X‖=1 := by
  have ht := Real.sin_sq_add_cos_sq (a*floorInteriorBump X)
  have hp := Real.sin_sq_add_cos_sq (-X 1)
  have hmul := congrArg (fun t : ℝ => (Real.sin (a*floorInteriorBump X))^2*t) hp
  have hs : Quaternion.normSq (floorRawLift a X)=1 := by
    rw [Quaternion.normSq_def',floorRawLift_mk]
    simp only
    nlinarith
  have h := Quaternion.normSq_eq_norm_mul_self (floorRawLift a X)
  rw [hs] at h
  nlinarith [norm_nonneg (floorRawLift a X)]

/-- The raw lift is the unit quaternion at every point where the interior bump vanishes. -/
theorem floorRawLift_one_of_bump_zero (a : ℝ) (X : SpatialPoint) (hx : floorInteriorBump X=0) :
    floorRawLift a X=1 := by
  rw [floorRawLift_mk,hx]
  ext <;> simp

/-- On the width- `1/2` collar of the fundamental cube, the raw lift equals the unit quaternion
for every real parameter. -/
theorem floorRawLift_collar (a : ℝ) : HasConstantCollar (floorRawLift a) (1/2) 1 := by
  intro X _ hface
  obtain ⟨j,hj⟩ := hface
  apply floorRawLift_one_of_bump_zero
  apply expNegInvGlue.zero_of_nonpos
  have hterm : (X j-3)^2 ≤ ∑ i : Fin 3, (X i-3)^2 :=
    Finset.single_le_sum (f := fun i : Fin 3 => (X i-3)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hL : 6<physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  rcases hj with hj|hj <;> dsimp only [floorBumpArgument] <;> nlinarith [sq_nonneg (X j-3)]

/-- Definition of floor Periodic Lift in the Coded Floor construction. -/
def floorPeriodicLift (a : ℝ) : QuaternionField := periodicExtension (floorRawLift a)

/-- The periodic lift is smooth in space for each real family parameter. -/
theorem floorPeriodicLift_contDiff (a : ℝ) : ContDiff ℝ ∞ (floorPeriodicLift a) :=
  contDiff_periodicExtension _ (contDiff_floorRawLift a) (1/2) (by norm_num)
    (by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]) 1 (floorRawLift_collar a)

/-- The periodic lift is invariant under the period translations defining `IsPeriodicField`. -/
theorem floorPeriodicLift_periodic (a : ℝ) : IsPeriodicField (floorPeriodicLift a) :=
  periodicExtension_periodic _

/-- The periodic lift has quaternion norm one at every spatial point. -/
theorem floorPeriodicLift_norm (a : ℝ) (X : SpatialPoint) : ‖floorPeriodicLift a X‖=1 :=
  floorRawLift_norm a (wrapPoint X)

/-- On the entire fundamental cube, the periodic lift agrees with the raw lift at the same
parameter. -/
theorem floorPeriodicLift_eq_raw_on_cube (a : ℝ) (X : SpatialPoint) (hX : InFundamentalCube X) :
    floorPeriodicLift a X=floorRawLift a X :=
  periodicExtension_eq_on_cube _ (1/2) (by norm_num) 1 (floorRawLift_collar a) X hX

end Qatlib.Concepts.EffectiveGauge.CodedFloor
