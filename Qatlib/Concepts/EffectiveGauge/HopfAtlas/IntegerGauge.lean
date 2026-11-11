/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PhysicalPoissonGauge
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerWinding

set_option backward.isDefEq.respectTransparency false

/-!
# Integer Gauge

Hopf Atlas constructions for Effective Gauge.
Defines `integerGauge`, `selectedSectorWinding`, `selectedPoissonGauge`.
Proves `integerGauge_contDiff`, `integerGauge_periodic`, `integerGauge_norm`.
-/


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of integer Gauge in the Hopf Atlas construction. -/
def integerGauge (q : QuaternionField) (n : SpatialFrequency) : QuaternionField :=
  fun x => phase (windingLinear n x)*q x

/-- Original `integerGauge_contDiff` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_contDiff (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (n : SpatialFrequency) :
    ContDiff ℝ ∞ (integerGauge q n) :=
  (contDiff_phase.comp (windingLinear n).contDiff).mul hq

/-- Original `integerGauge_periodic` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_periodic (q : QuaternionField) (hp : IsPeriodicField q) (n : SpatialFrequency) :
    IsPeriodicField (integerGauge q n) := by
  intro x m
  simp only [integerGauge,map_add,windingLinear_lattice,phase_int_period,hp x m]

/-- Original `integerGauge_norm` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_norm (q : QuaternionField) (hu : ∀ x, ‖q x‖=1)
    (n : SpatialFrequency) (x : SpatialPoint) : ‖integerGauge q n x‖=1 := by
  simp [integerGauge,norm_mul,hu]

/-- Original `integerGauge_hopf` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_hopf (q : QuaternionField) (n : SpatialFrequency) (x : SpatialPoint) :
    hopf (integerGauge q n x)=hopf (q x) := hopf_phase _ _

/-- Original `integerGauge_origin` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_origin (q : QuaternionField) (n : SpatialFrequency) : integerGauge q n 0=q 0 := by
  simp [integerGauge,phase]

/-- Original `integerGauge_connection` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_connection (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (n : SpatialFrequency) (j : Fin 3) (x : SpatialPoint) :
    connection (integerGauge q n) x j=connection q x j+(n j : ℝ) := by
  have h := connection_gauge_unit (hq.differentiable (by simp) x)
    (windingLinear n).differentiableAt (hu x) j
  rw [(windingLinear n).hasFDerivAt.fderiv,windingLinear_basis] at h
  exact h

/-- Original `integerGauge_mean` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_mean (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (n : SpatialFrequency) (j : Fin 3) :
    physicalCubeMean (fun x => connection (integerGauge q n) x j)=
      physicalCubeMean (fun x => connection q x j)+(n j : ℝ) := by
  have heq : (fun x => connection (integerGauge q n) x j)=fun x => connection q x j+(n j : ℝ) :=
    funext (integerGauge_connection q hq hu n j)
  rw [heq,physicalCubeMean_add _ _ (contDiff_connection q hq j).continuous continuous_const,
    physicalCubeMean_const]

/-- Original `integerGauge_solenoidal` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_solenoidal (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (hs : IsSolenoidal q) (n : SpatialFrequency) :
    IsSolenoidal (integerGauge q n) := by
  intro x
  have hsol := hs x
  change (∑ j : Fin 3, fderiv ℝ (fun y => (1 : ℝ)*connection q y j) x (EuclideanSpace.single j 1))=0 at hsol
  simp only [one_mul] at hsol
  change (∑ j : Fin 3, fderiv ℝ (fun y => (1 : ℝ)*connection (integerGauge q n) y j) x
    (EuclideanSpace.single j 1))=0
  simp only [one_mul]
  have heach (j : Fin 3) : fderiv ℝ (fun y => connection (integerGauge q n) y j) x=
      fderiv ℝ (fun y => connection q y j) x := by
    have heq : (fun y => connection (integerGauge q n) y j)=fun y => connection q y j+(n j : ℝ) :=
      funext (integerGauge_connection q hq hu n j)
    rw [heq]
    exact (((contDiff_connection q hq j).differentiable (by simp) x).hasFDerivAt.add_const _).fderiv
  simpa only [heach] using hsol

/-- Original `integerGauge_connection_period` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_connection_period (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (n : SpatialFrequency) (j : Fin 3) (x : SpatialPoint) :
    (∫ t in (0 : ℝ)..physicalPeriod,
      connection (integerGauge q n) (x+t • EuclideanSpace.single j 1) j)=
      (∫ t in (0 : ℝ)..physicalPeriod, connection q (x+t • EuclideanSpace.single j 1) j)+
        physicalPeriod*(n j : ℝ) := by
  simp_rw [integerGauge_connection q hq hu n j]
  have hi : IntervalIntegrable (fun t : ℝ => connection q (x+t • EuclideanSpace.single j 1) j)
      volume 0 physicalPeriod :=
    ((contDiff_connection q hq j).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi intervalIntegrable_const]
  simp

/-- Original `integerGauge_holonomy` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem integerGauge_holonomy (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (n : SpatialFrequency) (j : Fin 3) (x : SpatialPoint) :
    phase (∫ t in (0 : ℝ)..physicalPeriod,
      connection (integerGauge q n) (x+t • EuclideanSpace.single j 1) j)=
      phase (∫ t in (0 : ℝ)..physicalPeriod, connection q (x+t • EuclideanSpace.single j 1) j) := by
  rw [integerGauge_connection_period q hq hu n j x,mul_comm physicalPeriod]
  exact phase_int_period _ _

/-- Definition of selected Sector Winding in the Hopf Atlas construction. -/
def selectedSectorWinding (result : SourceMeanSectorResult) : SpatialFrequency :=
  fun j => (result.choices j).winding

/-- Definition of selected Poisson Gauge in the Hopf Atlas construction. -/
def selectedPoissonGauge (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (result : SourceMeanSectorResult) : QuaternionField :=
  integerGauge (poissonCorrectedLift q hq hp) (selectedSectorWinding result)

/-- Original `selectedPoissonGauge_contDiff` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_contDiff (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) :
    ContDiff ℝ ∞ (selectedPoissonGauge q hq hp result) :=
  integerGauge_contDiff _ (poissonCorrectedLift_contDiff q hq hp) _

/-- Original `selectedPoissonGauge_periodic` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_periodic (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) :
    IsPeriodicField (selectedPoissonGauge q hq hp result) :=
  integerGauge_periodic _ (poissonCorrectedLift_periodic q hq hp) _

/-- Original `selectedPoissonGauge_norm` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_norm (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult) (x : SpatialPoint) :
    ‖selectedPoissonGauge q hq hp result x‖=1 :=
  integerGauge_norm _ (poissonCorrectedLift_norm q hq hp hu) _ x

/-- Original `selectedPoissonGauge_hopf` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_hopf (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) (x : SpatialPoint) :
    hopf (selectedPoissonGauge q hq hp result x)=hopf (q x) :=
  (integerGauge_hopf _ _ x).trans (poissonCorrectedLift_hopf q hq hp x)

/-- Original `selectedPoissonGauge_origin` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_origin (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) :
    selectedPoissonGauge q hq hp result 0=q 0 :=
  (integerGauge_origin _ _).trans (poissonCorrectedLift_origin q hq hp)

/-- Original `selectedPoissonGauge_solenoidal` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_solenoidal (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult) :
    IsSolenoidal (selectedPoissonGauge q hq hp result) :=
  integerGauge_solenoidal _ (poissonCorrectedLift_contDiff q hq hp)
    (poissonCorrectedLift_norm q hq hp hu) (poissonCorrectedLift_solenoidal q hq hp hu) _

/-- Original `selectedPoissonGauge_mean` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_mean (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult) (j : Fin 3) :
    physicalCubeMean (fun x => connection (selectedPoissonGauge q hq hp result) x j)=
      physicalCubeMean (fun x => connection q x j)+((result.choices j).winding : ℝ) := by
  rw [selectedPoissonGauge,integerGauge_mean _ (poissonCorrectedLift_contDiff q hq hp)
    (poissonCorrectedLift_norm q hq hp hu),poissonCorrectedLift_mean q hq hp hu j]
  rfl

/-- Original `selectedPoissonGauge_mean_cell` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_mean_cell (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult)
    (hc : SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection q x j)) result)
    (j : Fin 3) :
    ((result.choices j).shift : ℝ)+1/8 <
      physicalCubeMean (fun x => connection (selectedPoissonGauge q hq hp result) x j) ∧
    physicalCubeMean (fun x => connection (selectedPoissonGauge q hq hp result) x j)<
      ((result.choices j).shift : ℝ)+7/8 := by
  rw [selectedPoissonGauge_mean q hq hp hu result j]
  exact hc.2.2.2.1 j

/-- Original `selectedPoissonGauge_integer_unique` guarantee for the `IntegerGauge` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_integer_unique (q : QuaternionField) (result : SourceMeanSectorResult)
    (hc : SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection q x j)) result)
    (n : SpatialFrequency)
    (hn : ∀ j, ((result.choices j).shift : ℝ)+1/8<physicalCubeMean (fun x => connection q x j)+(n j : ℝ) ∧
      physicalCubeMean (fun x => connection q x j)+(n j : ℝ)<((result.choices j).shift : ℝ)+7/8) :
    n=selectedSectorWinding result := hc.2.2.2.2 n hn

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
