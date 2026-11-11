/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSpinFamily

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Lift Connection

Coded Floor constructions for Effective Gauge.
Proves `floorRawLift_connection_formula`, `floorRawLift_connection`, `floorPeriodicLift_connection`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `floorRawLift_connection_formula` guarantee for the `FloorLiftConnection` construction; the complete source hypotheses are retained. -/
theorem floorRawLift_connection_formula (a : ℝ) (X : SpatialPoint) (i : Fin 3) :
    connection (floorRawLift a) X i=(Real.sin (a*floorInteriorBump X))^2*
      fderiv ℝ (fun Y : SpatialPoint => -Y 1) X (EuclideanSpace.single i 1) := by
  let theta := fun Y => a*floorInteriorBump Y
  let phi := fun Y : SpatialPoint => -Y 1
  let e := EuclideanSpace.single i (1 : ℝ)
  let V := fderiv ℝ (floorRawLift a) X e
  let T := fderiv ℝ theta X e
  let P := fderiv ℝ phi X e
  have htheta : ContDiff ℝ ∞ theta := contDiff_const.mul contDiff_floorInteriorBump
  have hphi : ContDiff ℝ ∞ phi := (EuclideanSpace.proj (1 : Fin 3) : SpatialPoint →L[ℝ] ℝ).contDiff.neg
  have ht := (htheta.differentiable (by simp) X).hasFDerivAt
  have hp := (hphi.differentiable (by simp) X).hasFDerivAt
  have hI := congrFun (spatialWordPartial_clm (quaternionCoordinateCLM 1) (floorRawLift a)
    (contDiff_floorRawLift a) [i]) X
  change fderiv ℝ (fun _ : SpatialPoint => (0 : ℝ)) X e=V.imI at hI
  have hI0 : V.imI=0 := by simpa only [fderiv_const_apply,ContinuousLinearMap.zero_apply] using hI.symm
  have hJ := congrFun (spatialWordPartial_clm (quaternionCoordinateCLM 2) (floorRawLift a)
    (contDiff_floorRawLift a) [i]) X
  change fderiv ℝ (fun Y => Real.sin (theta Y)*Real.cos (phi Y)) X e=V.imJ at hJ
  have hdJ := ht.sin.mul hp.cos
  change HasFDerivAt (fun Y => Real.sin (theta Y)*Real.cos (phi Y)) _ X at hdJ
  have hJV : V.imJ=Real.cos (theta X)*T*Real.cos (phi X)-Real.sin (theta X)*Real.sin (phi X)*P := by
    rw [← hJ,hdJ.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    dsimp only [T,P]
    ring
  have hK := congrFun (spatialWordPartial_clm (quaternionCoordinateCLM 3) (floorRawLift a)
    (contDiff_floorRawLift a) [i]) X
  change fderiv ℝ (fun Y => Real.sin (theta Y)*Real.sin (phi Y)) X e=V.imK at hK
  have hdK := ht.sin.mul hp.sin
  change HasFDerivAt (fun Y => Real.sin (theta Y)*Real.sin (phi Y)) _ X at hdK
  have hKV : V.imK=Real.cos (theta X)*T*Real.sin (phi X)+Real.sin (theta X)*Real.cos (phi X)*P := by
    rw [← hK,hdK.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    dsimp only [T,P]
    ring
  change connectionValue (floorRawLift a X) V=(Real.sin (theta X))^2*P
  rw [connectionValue_eq,floorRawLift_mk]
  change Real.cos (theta X)*V.imI-0*V.re+
    (Real.sin (theta X)*Real.cos (phi X))*V.imK-
    (Real.sin (theta X)*Real.sin (phi X))*V.imJ=(Real.sin (theta X))^2*P
  rw [hI0,hJV,hKV]
  have hphase := Real.sin_sq_add_cos_sq (phi X)
  have hmul := congrArg (fun t : ℝ => (Real.sin (theta X))^2*P*t) hphase
  nlinarith

/-- Original `floorRawLift_connection` guarantee for the `FloorLiftConnection` construction; the complete source hypotheses are retained. -/
theorem floorRawLift_connection (a : ℝ) (X : SpatialPoint) (i : Fin 3) :
    connection (floorRawLift a) X i=if i=1 then -(Real.sin (a*floorInteriorBump X))^2 else 0 := by
  rw [floorRawLift_connection_formula]
  have hd : HasFDerivAt (fun Y : SpatialPoint => -Y 1)
      (-(EuclideanSpace.proj (1 : Fin 3) : SpatialPoint →L[ℝ] ℝ)) X :=
    (EuclideanSpace.proj (1 : Fin 3) : SpatialPoint →L[ℝ] ℝ).hasFDerivAt.neg
  rw [hd.fderiv]
  fin_cases i <;> simp

/-- Original `floorPeriodicLift_connection` guarantee for the `FloorLiftConnection` construction; the complete source hypotheses are retained. -/
theorem floorPeriodicLift_connection (a : ℝ) (X : SpatialPoint) (hX : InFundamentalCube X) (i : Fin 3) :
    connection (floorPeriodicLift a) X i=if i=1 then -(Real.sin (a*floorInteriorBump X))^2 else 0 := by
  change connectionValue (floorPeriodicLift a X) (spatialWordPartial (floorPeriodicLift a) [i] X)=_
  rw [floorPeriodicLift_eq_raw_on_cube a X hX,floorPeriodicLift_word_eq_raw a [i] X hX]
  exact floorRawLift_connection a X i

end Qatlib.Concepts.EffectiveGauge.CodedFloor
