/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierMode
import Mathlib.Topology.Algebra.Group.Quotient

set_option backward.isDefEq.respectTransparency false

/-!
# Unit Torus Descent

Hopf Atlas constructions for Effective Gauge.
Defines `unitTorusProjection`, `unitTorusLift`, `unitTorusContinuousLift`.
Proves `unitTorusProjection_quotient`, `unitPeriodic_eq_of_projection_eq`, `unitTorusLift_apply`.
-/


set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of unit Torus Projection in the Hopf Atlas construction. -/
def unitTorusProjection (x : SpatialPoint) : UnitAddTorus (Fin 3) := fun j => (x j : UnitAddCircle)

/-- Original `unitTorusProjection_quotient` guarantee for the `UnitTorusDescent` construction; the complete source hypotheses are retained. -/
theorem unitTorusProjection_quotient : IsOpenQuotientMap unitTorusProjection := by
  have hpi : IsOpenQuotientMap (fun x : Fin 3 → ℝ => fun j => (x j : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun t : ℝ => (t : UnitAddCircle))))
  exact hpi.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.isOpenQuotientMap

/-- Equality of quotient coordinates is precisely an integer lattice shift;
this is used for values, without differentiating any representative map. -/
theorem unitPeriodic_eq_of_projection_eq {E : Type*} (f : SpatialPoint → E)
    (hp : IsUnitPeriodicField f) (x y : SpatialPoint) (hxy : unitTorusProjection x=unitTorusProjection y) : f x=f y := by
  have hcoord (j : Fin 3) : ∃ n : ℤ, (n : ℝ)=x j-y j := by
    have hj : (x j : UnitAddCircle)=(y j : UnitAddCircle) := congrFun hxy j
    have hzero : ((x j-y j : ℝ) : UnitAddCircle)=0 := by
      rw [AddCircle.coe_sub,hj,sub_self]
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
    exact ⟨n,by simpa only [zsmul_eq_mul,mul_one] using hn⟩
  let n : SpatialFrequency := fun j => Classical.choose (hcoord j)
  have hn (j : Fin 3) : (n j : ℝ)=x j-y j := Classical.choose_spec (hcoord j)
  have heq : x=y+unitIntegerShift n := by
    ext j
    change x j=y j+(n j : ℝ)
    rw [hn]
    ring
  rw [heq]
  exact hp y n

/-- A noncomputable representative is used only to define the exact analytic
function on the compact torus. No evaluator or algorithm is inferred from it. -/
def unitTorusLift {E : Type*} (f : SpatialPoint → E) (z : UnitAddTorus (Fin 3)) : E :=
  f (Function.surjInv unitTorusProjection_quotient.surjective z)

/-- Original `unitTorusLift_apply` guarantee for the `UnitTorusDescent` construction; the complete source hypotheses are retained. -/
theorem unitTorusLift_apply {E : Type*} (f : SpatialPoint → E) (hp : IsUnitPeriodicField f) (x : SpatialPoint) :
    unitTorusLift f (unitTorusProjection x)=f x :=
  unitPeriodic_eq_of_projection_eq f hp _ x (Function.surjInv_eq unitTorusProjection_quotient.surjective _)

/-- Original `continuous_unitTorusLift` guarantee for the `UnitTorusDescent` construction; the complete source hypotheses are retained. -/
theorem continuous_unitTorusLift {E : Type*} [TopologicalSpace E]
    (f : SpatialPoint → E) (hf : Continuous f) (hp : IsUnitPeriodicField f) : Continuous (unitTorusLift f) := by
  apply unitTorusProjection_quotient.isQuotientMap.continuous_iff.mpr
  have heq : unitTorusLift f ∘ unitTorusProjection=f := funext (unitTorusLift_apply f hp)
  rw [heq]
  exact hf

/-- Definition of unit Torus Continuous Lift in the Hopf Atlas construction. -/
def unitTorusContinuousLift {E : Type*} [TopologicalSpace E]
    (f : SpatialPoint → E) (hf : Continuous f) (hp : IsUnitPeriodicField f) : C(UnitAddTorus (Fin 3),E) :=
  ⟨unitTorusLift f,continuous_unitTorusLift f hf hp⟩

/-- Original `unitTorusContinuousLift_apply` guarantee for the `UnitTorusDescent` construction; the complete source hypotheses are retained. -/
theorem unitTorusContinuousLift_apply {E : Type*} [TopologicalSpace E]
    (f : SpatialPoint → E) (hf : Continuous f) (hp : IsUnitPeriodicField f) (x : SpatialPoint) :
    unitTorusContinuousLift f hf hp (unitTorusProjection x)=f x := unitTorusLift_apply f hp x

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
