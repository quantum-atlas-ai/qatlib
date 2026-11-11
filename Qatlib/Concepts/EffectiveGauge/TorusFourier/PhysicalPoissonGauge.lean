/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.ConnectionPoisson
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Gauge
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicIntegral

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Poisson Gauge

Torus Fourier constructions for Effective Gauge.
Defines `physicalPoissonPhase`, `poissonCorrectedLift`.
Proves `physicalPoissonPhase_contDiff`, `physicalPoissonPhase_word`, `unitNormalize_latticeShift`.
-/


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of physical Poisson Phase in the Torus Fourier construction. -/
def physicalPoissonPhase (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (x : SpatialPoint) : ℝ :=
  normalizedConnectionPoisson q hq hp (physicalPeriod⁻¹ • x)-normalizedConnectionPoisson q hq hp 0

/-- Original `physicalPoissonPhase_contDiff` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonPhase_contDiff (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) : ContDiff ℝ ∞ (physicalPoissonPhase q hq hp) :=
  (((normalizedConnectionPoisson_spec q hq hp).1).comp
    (contDiff_id.const_smul physicalPeriod⁻¹)).sub contDiff_const

/-- Original `physicalPoissonPhase_word` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonPhase_word (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (w : List (Fin 3)) (hw : w≠[]) :
    spatialWordPartial (physicalPoissonPhase q hq hp) w=fun x =>
      physicalPeriod⁻¹^w.length*spatialWordPartial (normalizedConnectionPoisson q hq hp) w
        (physicalPeriod⁻¹ • x) := by
  let chi := normalizedConnectionPoisson q hq hp
  have hc : ContDiff ℝ ∞ chi := (normalizedConnectionPoisson_spec q hq hp).1
  change spatialWordPartial (fun x => chi (physicalPeriod⁻¹ • x)+(-chi 0)) w=_
  rw [spatialWordPartial_add (fun x => chi (physicalPeriod⁻¹ • x)) (fun _ => -chi 0)
      (hc.comp (contDiff_id.const_smul physicalPeriod⁻¹)) contDiff_const w,
    spatialWordPartial_const,spatialWordPartial_scale chi hc physicalPeriod⁻¹]
  simp only [hw,ite_false,add_zero,smul_eq_mul]
  rfl

/-- Original `unitNormalize_latticeShift` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem unitNormalize_latticeShift (x : SpatialPoint) (n : SpatialFrequency) :
    physicalPeriod⁻¹ • (x+latticeShift n)=physicalPeriod⁻¹ • x+unitIntegerShift n := by
  ext j
  change physicalPeriod⁻¹*(x j+physicalPeriod*(n j : ℝ))=
    physicalPeriod⁻¹*x j+(n j : ℝ)
  field_simp [physicalPeriod_pos.ne']

/-- Original `physicalPoissonPhase_periodic` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonPhase_periodic (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) : IsPeriodicField (physicalPoissonPhase q hq hp) := by
  intro x n
  unfold physicalPoissonPhase
  rw [unitNormalize_latticeShift,(normalizedConnectionPoisson_spec q hq hp).2.1]

/-- Definition of poisson Corrected Lift in the Torus Fourier construction. -/
def poissonCorrectedLift (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q) : QuaternionField :=
  fun x => phase (physicalPoissonPhase q hq hp x)*q x

/-- Original `poissonCorrectedLift_contDiff` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_contDiff (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) : ContDiff ℝ ∞ (poissonCorrectedLift q hq hp) :=
  (contDiff_phase.comp (physicalPoissonPhase_contDiff q hq hp)).mul hq

/-- Original `poissonCorrectedLift_norm` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_norm (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (x : SpatialPoint) :
    ‖poissonCorrectedLift q hq hp x‖=1 := by
  simp [poissonCorrectedLift,norm_mul,hu]

/-- Original `poissonCorrectedLift_hopf` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_hopf (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (x : SpatialPoint) : hopf (poissonCorrectedLift q hq hp x)=hopf (q x) :=
  hopf_phase _ _

/-- Original `poissonCorrectedLift_origin` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_origin (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) : poissonCorrectedLift q hq hp 0=q 0 := by
  simp [poissonCorrectedLift,physicalPoissonPhase,phase]

/-- Original `poissonCorrectedLift_periodic` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_periodic (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) : IsPeriodicField (poissonCorrectedLift q hq hp) := by
  intro x n
  unfold poissonCorrectedLift
  rw [physicalPoissonPhase_periodic q hq hp x n,hp x n]

/-- Original `poissonCorrectedLift_connection` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_connection (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (j : Fin 3) (x : SpatialPoint) :
    connection (poissonCorrectedLift q hq hp) x j=
      connection q x j+physicalPeriod⁻¹*
        spatialWordPartial (normalizedConnectionPoisson q hq hp) [j] (physicalPeriod⁻¹ • x) := by
  have h := connection_gauge_unit (hq.differentiable (by simp) x)
    ((physicalPoissonPhase_contDiff q hq hp).differentiable (by simp) x) (hu x) j
  change connection (poissonCorrectedLift q hq hp) x j=
    connection q x j+spatialWordPartial (physicalPoissonPhase q hq hp) [j] x at h
  rw [physicalPoissonPhase_word q hq hp [j] (by simp)] at h
  simpa only [List.length_singleton,pow_one] using h

/-- Original `normalizedConnectionReal_word` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem normalizedConnectionReal_word (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (j : Fin 3) (w : List (Fin 3)) :
    spatialWordPartial (normalizedConnectionReal q j) w=fun u =>
      physicalPeriod^(w.length+1)*spatialWordPartial (fun x => connection q x j) w (physicalPeriod • u) := by
  have hA := contDiff_connection q hq j
  change spatialWordPartial (fun u => physicalPeriod • connection q (physicalPeriod • u) j) w=_
  rw [spatialWordPartial_const_smul (fun u => connection q (physicalPeriod • u) j)
      (hA.comp (contDiff_id.const_smul physicalPeriod)) physicalPeriod w,
    spatialWordPartial_scale _ hA physicalPeriod]
  funext u
  simp only [smul_eq_mul,pow_succ]
  ring

/-- Original `physicalPoissonPhase_laplacian` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonPhase_laplacian (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (x : SpatialPoint) :
    (∑ j : Fin 3, spatialWordPartial (physicalPoissonPhase q hq hp) [j,j] x)=
      -∑ j : Fin 3, spatialWordPartial (fun y => connection q y j) [j] x := by
  let chi := normalizedConnectionPoisson q hq hp
  have hPDE := (normalizedConnectionPoisson_spec q hq hp).2.2 (physicalPeriod⁻¹ • x)
  have hLx : physicalPeriod • (physicalPeriod⁻¹ • x)=x := by
    simp only [smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul]
  have hC : (∑ j : Fin 3, spatialWordPartial (normalizedConnectionReal q j) [j] (physicalPeriod⁻¹ • x))=
      physicalPeriod^2*(∑ j : Fin 3, spatialWordPartial (fun y => connection q y j) [j] x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [normalizedConnectionReal_word q hq j [j]]
    simp only [List.length_singleton,hLx]
  rw [hC] at hPDE
  calc
    _ = physicalPeriod⁻¹^2*(∑ j : Fin 3, spatialWordPartial chi [j,j] (physicalPeriod⁻¹ • x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [physicalPoissonPhase_word q hq hp [j,j] (by simp)]
      rfl
    _ = _ := by
      rw [hPDE]
      field_simp [physicalPeriod_pos.ne']

/-- Original `poissonCorrectedLift_solenoidal` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem poissonCorrectedLift_solenoidal (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) : IsSolenoidal (poissonCorrectedLift q hq hp) := by
  intro x
  let theta := physicalPoissonPhase q hq hp
  have ht : ContDiff ℝ ∞ theta := physicalPoissonPhase_contDiff q hq hp
  have hfun (j : Fin 3) : (fun y => connection (poissonCorrectedLift q hq hp) y j)=
      fun y => connection q y j+spatialWordPartial theta [j] y := by
    funext y
    exact connection_gauge_unit (hq.differentiable (by simp) y)
      (ht.differentiable (by simp) y) (hu y) j
  change (∑ j : Fin 3, fderiv ℝ (fun y => (1 : ℝ)*connection (poissonCorrectedLift q hq hp) y j) x
    (EuclideanSpace.single j 1))=0
  simp only [one_mul]
  have heach (j : Fin 3) :
      fderiv ℝ (fun y => connection (poissonCorrectedLift q hq hp) y j) x (EuclideanSpace.single j 1)=
      spatialWordPartial (fun y => connection q y j) [j] x+spatialWordPartial theta [j,j] x := by
    rw [hfun]
    have h := congrFun (spatialWordPartial_add (fun y => connection q y j) (spatialWordPartial theta [j])
      (contDiff_connection q hq j) (contDiff_spatialWordPartial theta ht [j]) [j]) x
    exact h
  simp_rw [heach]
  rw [Finset.sum_add_distrib,physicalPoissonPhase_laplacian q hq hp x,add_neg_cancel]

/-- Original `physicalCubeMean_add` guarantee for the `PhysicalPoissonGauge` construction; the complete source hypotheses are retained. -/
theorem physicalCubeMean_add (f g : SpatialPoint → ℝ) (hf : Continuous f) (hg : Continuous g) :
    physicalCubeMean (fun x => f x+g x)=physicalCubeMean f+physicalCubeMean g := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hF : IntegrableOn (fun u : Fin 3 → ℝ => f (WithLp.toLp 2 u))
      (Set.Icc 0 (fun _ => physicalPeriod)) := (hf.comp e.continuous).integrableOn_Icc
  have hG : IntegrableOn (fun u : Fin 3 → ℝ => g (WithLp.toLp 2 u))
      (Set.Icc 0 (fun _ => physicalPeriod)) := (hg.comp e.continuous).integrableOn_Icc
  unfold physicalCubeMean physicalCubeIntegral
  change (∫ u : Fin 3 → ℝ in Set.Icc 0 (fun _ => physicalPeriod), f (WithLp.toLp 2 u)+g (WithLp.toLp 2 u))/
      physicalPeriod^3=(∫ u : Fin 3 → ℝ in Set.Icc 0 (fun _ => physicalPeriod), f (WithLp.toLp 2 u))/
      physicalPeriod^3+(∫ u : Fin 3 → ℝ in Set.Icc 0 (fun _ => physicalPeriod), g (WithLp.toLp 2 u))/physicalPeriod^3
  rw [integral_add hF hG]
  ring

/-- The physical connection mean is preserved by the real periodic phase,
 so the cached reference mean/sector certifies the corrected lift too. -/
theorem poissonCorrectedLift_mean (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (j : Fin 3) :
    physicalCubeMean (fun x => connection (poissonCorrectedLift q hq hp) x j)=
      physicalCubeMean (fun x => connection q x j) := by
  let theta := physicalPoissonPhase q hq hp
  have ht : ContDiff ℝ ∞ theta := physicalPoissonPhase_contDiff q hq hp
  have hfun : (fun x => connection (poissonCorrectedLift q hq hp) x j)=
      fun x => connection q x j+fderiv ℝ theta x (EuclideanSpace.single j 1) := by
    funext x
    exact connection_gauge_unit (hq.differentiable (by simp) x) (ht.differentiable (by simp) x) (hu x) j
  rw [hfun,physicalCubeMean_add (fun x => connection q x j)
    (fun x => fderiv ℝ theta x (EuclideanSpace.single j 1)) (contDiff_connection q hq j).continuous
    (((ht.fderiv_right (m := ∞) (by rfl)).continuous).clm_apply continuous_const),
    physicalCubeMean_partial_periodic theta ht (physicalPoissonPhase_periodic q hq hp) j,add_zero]

end Qatlib.Concepts.EffectiveGauge.TorusFourier
