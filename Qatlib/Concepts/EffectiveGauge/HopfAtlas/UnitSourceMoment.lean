/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceMoment
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz

set_option backward.isDefEq.respectTransparency false

/-!
# The original physical source bounds determine the actual mean mesh

Both derivatives of the normalized source are computed by the chain rule at
the fixed exact physical point. No normalized-source modulus or reference
derivative bound is supplied as additional input.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `contDiff_unitCoordinateSpin` guarantee for the `UnitSourceMoment` construction; the complete source hypotheses are retained. -/
theorem contDiff_unitCoordinateSpin (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (unitCoordinateSpin v) := by
  change ContDiff ℝ ∞ (fun u : SpatialPoint => v (physicalPeriod • u))
  exact hv.comp ((contDiff_id : ContDiff ℝ ∞ (fun u : SpatialPoint => u)).const_smul physicalPeriod)

/-- Original `sourcePhysicalPartial_unitCoordinateSpin` guarantee for the `UnitSourceMoment` construction; the complete source hypotheses are retained. -/
theorem sourcePhysicalPartial_unitCoordinateSpin (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (u : SpatialPoint) (i : Fin 3) :
    sourcePhysicalPartial (unitCoordinateSpin v) i u=
      physicalPeriod • sourcePhysicalPartial v i (physicalPeriod • u) := by
  have hd := (hv.differentiable (by simp) (physicalPeriod • u)).hasFDerivAt.comp u
    ((hasFDerivAt_id u).const_smul physicalPeriod)
  change HasFDerivAt (unitCoordinateSpin v) _ u at hd
  rw [sourcePhysicalPartial,hd.fderiv]
  simp [sourcePhysicalPartial]

/-- Original `sourcePhysicalSecond_unitCoordinateSpin` guarantee for the `UnitSourceMoment` construction; the complete source hypotheses are retained. -/
theorem sourcePhysicalSecond_unitCoordinateSpin (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (u : SpatialPoint) (i k : Fin 3) :
    fderiv ℝ (sourcePhysicalPartial (unitCoordinateSpin v) i) u (EuclideanSpace.single k 1)=
      (physicalPeriod*physicalPeriod) •
        fderiv ℝ (sourcePhysicalPartial v i) (physicalPeriod • u) (EuclideanSpace.single k 1) := by
  have heq : sourcePhysicalPartial (unitCoordinateSpin v) i=
      (fun y => physicalPeriod • sourcePhysicalPartial v i (physicalPeriod • y)) :=
    funext (fun y => sourcePhysicalPartial_unitCoordinateSpin v hv y i)
  have hc : ContDiff ℝ ∞ (sourcePhysicalPartial v i) :=
    (hv.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const
  have hd := ((hc.differentiable (by simp) (physicalPeriod • u)).hasFDerivAt.comp u
    ((hasFDerivAt_id u).const_smul physicalPeriod)).const_smul physicalPeriod
  change HasFDerivAt (fun y => physicalPeriod • sourcePhysicalPartial v i (physicalPeriod • y)) _ u at hd
  rw [heq,hd.fderiv]
  simp [smul_smul]

/-- Original `unitCube_scale_physical` guarantee for the `UnitSourceMoment` construction; the complete source hypotheses are retained. -/
theorem unitCube_scale_physical (u : SpatialPoint) (hu : InUnitCube u) :
    InFundamentalCube (physicalPeriod • u) := by
  intro k
  change 0 ≤ physicalPeriod*u k ∧ physicalPeriod*u k ≤ physicalPeriod
  exact ⟨mul_nonneg physicalPeriod_pos.le (hu k).1,
    (mul_le_mul_of_nonneg_left (hu k).2 physicalPeriod_pos.le).trans_eq (mul_one _)⟩

/-- The explicit normalized derivative bounds used in the original mesh
follow from all ordered physical partial bounds. -/
theorem unitCoordinateSpin_partial_bounds (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (m1 m2 : ℝ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceAllRescalingBounds v m1 m2) (u : SpatialPoint) (hu : InUnitCube u) :
    (∀ i, ‖sourcePhysicalPartial (unitCoordinateSpin v) i u‖ ≤ 7*m1) ∧
    (∀ i k, ‖fderiv ℝ (sourcePhysicalPartial (unitCoordinateSpin v) i) u
      (EuclideanSpace.single k 1)‖ ≤ 49*m2) := by
  have hp : physicalPeriod ≤ 7 := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  have hu' := unitCube_scale_physical u hu
  constructor
  · intro i
    rw [sourcePhysicalPartial_unitCoordinateSpin v hv,norm_smul,Real.norm_eq_abs,
      abs_of_pos physicalPeriod_pos]
    exact (mul_le_mul_of_nonneg_left (hb.1 _ hu' i) physicalPeriod_pos.le).trans
      (mul_le_mul_of_nonneg_right hp hm1)
  · intro i k
    rw [sourcePhysicalSecond_unitCoordinateSpin v hv,norm_smul,Real.norm_eq_abs,
      abs_of_pos (mul_pos physicalPeriod_pos physicalPeriod_pos)]
    apply (mul_le_mul_of_nonneg_left (hb.2 i _ hu' k)
      (mul_nonneg physicalPeriod_pos.le physicalPeriod_pos.le)).trans
    have hp2 : physicalPeriod*physicalPeriod ≤ 49 :=
      (mul_le_mul hp hp physicalPeriod_pos.le (by norm_num)).trans_eq (by norm_num)
    exact mul_le_mul_of_nonneg_right hp2 hm2

/-- The actual source moment has precisely the modulus used by the finite
producer. Unit tangency, second derivatives and physical scaling are proved. -/
theorem unitSourceMoment_lipschitz (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (m1 m2 : ℝ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceAllRescalingBounds v m1 m2) (i j : Fin 3)
    (p q : MeanTensorPoint) (hp : meanTensorInCube p) (hq : meanTensorInCube q) :
    |sourceCurvatureMoment (unitCoordinateSpin v) i j (meanTensorSpatial p)-
      sourceCurvatureMoment (unitCoordinateSpin v) i j (meanTensorSpatial q)| ≤
        ((7*m1)^2/2+(7*m1)*(49*m2))*meanTensorDistance p q := by
  have hv' := contDiff_unitCoordinateSpin v hv
  have hu' (x : SpatialPoint) : ‖unitCoordinateSpin v x‖=1 := hu _
  apply unitCube_partial_lipschitz _ (contDiff_sourceCurvatureMoment _ hv' i j) _
    (by positivity) ?_ p q hp hq
  intro x hx k
  have hx' := unitCoordinateSpin_partial_bounds v hv m1 m2 hm1 hm2 hb x hx
  exact sourceCurvatureMoment_partial_bound _ hv' hu' x i j k (hx i)
    (7*m1) (49*m2) (by positivity) (by positivity) hx'.1 (fun l => hx'.2 l k)

/-- Genuine quadrature error for the exact source moment in the previously
proved same-reference mean identity. The finite noisy-node error is separate. -/
theorem unitSourceMoment_quadrature_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1)
    (m1 m2 : ℝ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hb : SourceAllRescalingBounds v m1 m2) (i j : Fin 3) (N : ℕ) (hN : 0<N) :
    |unitCubeIntegral (sourceCurvatureMoment (unitCoordinateSpin v) i j)-
      meanTensorLeftSum N (fun p => sourceCurvatureMoment (unitCoordinateSpin v) i j
        (meanTensorSpatial p))| ≤ 3*((7*m1)^2/2+(7*m1)*(49*m2))/(N : ℝ) := by
  exact unitCubeIntegral_tensor_error N hN _
    (contDiff_sourceCurvatureMoment _ (contDiff_unitCoordinateSpin v hv) i j).continuous
    _ (by positivity) (unitSourceMoment_lipschitz v hv hu m1 m2 hm1 hm2 hb i j)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
