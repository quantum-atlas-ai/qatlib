/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.TorusFourier.PhysicalPoissonGauge
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerWinding

@[expose] public section

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

/-- Multiplication by the integer winding phase preserves smoothness of a quaternion field. -/
theorem integerGauge_contDiff (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (n : SpatialFrequency) :
    ContDiff ℝ ∞ (integerGauge q n) :=
  (contDiff_phase.comp (windingLinear n).contDiff).mul hq

/-- An integer winding phase preserves periodicity under all spatial lattice shifts. -/
theorem integerGauge_periodic (q : QuaternionField) (hp : IsPeriodicField q) (n : SpatialFrequency) :
    IsPeriodicField (integerGauge q n) := by
  intro x m
  simp only [integerGauge,map_add,windingLinear_lattice,phase_int_period,hp x m]

/-- An integer winding phase preserves unit norm at each point of a unit quaternion field. -/
theorem integerGauge_norm (q : QuaternionField) (hu : ∀ x, ‖q x‖=1)
    (n : SpatialFrequency) (x : SpatialPoint) : ‖integerGauge q n x‖=1 := by
  simp [integerGauge,norm_mul,hu]

/-- The integer winding gauge preserves the Hopf value of any quaternion field pointwise. -/
theorem integerGauge_hopf (q : QuaternionField) (n : SpatialFrequency) (x : SpatialPoint) :
    hopf (integerGauge q n x)=hopf (q x) := hopf_phase _ _

/-- The winding phase at the origin is one, so an integer gauge leaves the original field value
there. -/
theorem integerGauge_origin (q : QuaternionField) (n : SpatialFrequency) : integerGauge q n 0=q 0 := by
  simp [integerGauge,phase]

/-- For a smooth unit field, the integer winding gauge adds `n j` to the `j`-th connection
component everywhere. -/
theorem integerGauge_connection (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (n : SpatialFrequency) (j : Fin 3) (x : SpatialPoint) :
    connection (integerGauge q n) x j=connection q x j+(n j : ℝ) := by
  have h := connection_gauge_unit (hq.differentiable (by simp) x)
    (windingLinear n).differentiableAt (hu x) j
  rw [(windingLinear n).hasFDerivAt.fderiv,windingLinear_basis] at h
  exact h

/-- For a smooth unit field, the integer winding changes the cube mean of the `j`-th connection
component by the same integer `n j`. -/
theorem integerGauge_mean (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (n : SpatialFrequency) (j : Fin 3) :
    physicalCubeMean (fun x => connection (integerGauge q n) x j)=
      physicalCubeMean (fun x => connection q x j)+(n j : ℝ) := by
  have heq : (fun x => connection (integerGauge q n) x j)=fun x => connection q x j+(n j : ℝ) :=
    funext (integerGauge_connection q hq hu n j)
  rw [heq,physicalCubeMean_add _ _ (contDiff_connection q hq j).continuous continuous_const,
    physicalCubeMean_const]

/-- The integer winding gauge of a smooth solenoidal unit field remains solenoidal because its
connection changes by a constant vector. -/
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

/-- For a smooth unit field, applying winding `n` adds `physicalPeriod * n j` to the connection
integral along one period in coordinate `j`. -/
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

/-- For a smooth unit field, the integer winding gauge preserves the quaternion phase of the
connection integral along any full coordinate period. -/
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

/-- The Poisson correction followed by the selected integer winding is smooth for a smooth
periodic input field. -/
theorem selectedPoissonGauge_contDiff (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) :
    ContDiff ℝ ∞ (selectedPoissonGauge q hq hp result) :=
  integerGauge_contDiff _ (poissonCorrectedLift_contDiff q hq hp) _

/-- The selected Poisson gauge of a smooth periodic field is periodic under all lattice shifts. -/
theorem selectedPoissonGauge_periodic (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) :
    IsPeriodicField (selectedPoissonGauge q hq hp result) :=
  integerGauge_periodic _ (poissonCorrectedLift_periodic q hq hp) _

/-- If the smooth periodic reference is unit everywhere, so is its selected Poisson gauge. -/
theorem selectedPoissonGauge_norm (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult) (x : SpatialPoint) :
    ‖selectedPoissonGauge q hq hp result x‖=1 :=
  integerGauge_norm _ (poissonCorrectedLift_norm q hq hp hu) _ x

/-- For a smooth periodic reference and any sector result, the selected Poisson gauge preserves
the Hopf image pointwise. -/
theorem selectedPoissonGauge_hopf (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) (x : SpatialPoint) :
    hopf (selectedPoissonGauge q hq hp result x)=hopf (q x) :=
  (integerGauge_hopf _ _ x).trans (poissonCorrectedLift_hopf q hq hp x)

/-- The selected Poisson gauge of a smooth periodic field agrees with the original field at the
origin. -/
theorem selectedPoissonGauge_origin (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (result : SourceMeanSectorResult) :
    selectedPoissonGauge q hq hp result 0=q 0 :=
  (integerGauge_origin _ _).trans (poissonCorrectedLift_origin q hq hp)

/-- For a smooth periodic unit reference, the selected Poisson gauge produces a solenoidal
field. -/
theorem selectedPoissonGauge_solenoidal (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult) :
    IsSolenoidal (selectedPoissonGauge q hq hp result) :=
  integerGauge_solenoidal _ (poissonCorrectedLift_contDiff q hq hp)
    (poissonCorrectedLift_norm q hq hp hu) (poissonCorrectedLift_solenoidal q hq hp hu) _

/-- For a smooth periodic unit reference, the selected Poisson gauge shifts each connection mean
by the integer winding in that coordinate's sector choice. -/
theorem selectedPoissonGauge_mean (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1) (result : SourceMeanSectorResult) (j : Fin 3) :
    physicalCubeMean (fun x => connection (selectedPoissonGauge q hq hp result) x j)=
      physicalCubeMean (fun x => connection q x j)+((result.choices j).winding : ℝ) := by
  rw [selectedPoissonGauge,integerGauge_mean _ (poissonCorrectedLift_contDiff q hq hp)
    (poissonCorrectedLift_norm q hq hp hu),poissonCorrectedLift_mean q hq hp hu j]
  rfl

/-- For a smooth periodic unit reference and a certified mean sector, the `j`-th connection mean
of the selected gauge lies strictly between the chosen shift plus `1/8` and the shift plus
`7/8`. -/
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

/-- Under a mean-sector certificate, any integer winding that places every shifted connection
mean strictly in its chosen cell equals the certified winding. -/
theorem selectedPoissonGauge_integer_unique (q : QuaternionField) (result : SourceMeanSectorResult)
    (hc : SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection q x j)) result)
    (n : SpatialFrequency)
    (hn : ∀ j, ((result.choices j).shift : ℝ)+1/8<physicalCubeMean (fun x => connection q x j)+(n j : ℝ) ∧
      physicalCubeMean (fun x => connection q x j)+(n j : ℝ)<((result.choices j).shift : ℝ)+7/8) :
    n=selectedSectorWinding result := hc.2.2.2.2 n hn

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
