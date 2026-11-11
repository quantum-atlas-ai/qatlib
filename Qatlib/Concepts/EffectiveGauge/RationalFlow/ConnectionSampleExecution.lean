/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ConnectionSamplePlan
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierMode

set_option backward.isDefEq.respectTransparency false

/-!
# Connection Sample Execution

Rational Flow constructions for Effective Gauge.
Defines `rationalUnitWrap`, `rationalUnitNeighbor`, `connectionSampleExecution`.
Proves `rationalUnitWrap_mem`, `rationalUnitWrap_periodic`, `rationalUnitNeighbor_cast`.
-/

set_option autoImplicit false
open Set
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of rational Unit Wrap in the Rational Flow construction. -/
def rationalUnitWrap (a : Fin 3 → ℚ) : Fin 3 → ℚ :=
  fun j => a j-(Int.floor (a j) : ℚ)

/-- Definition of rational Unit Neighbor in the Rational Flow construction. -/
def rationalUnitNeighbor (a : Fin 3 → ℚ) (h : ℚ) (j : Fin 3) : Fin 3 → ℚ :=
  fun k => a k+if k=j then h else 0

/-- One center call and exactly three neighbor calls. The value program
and every query tolerance are part of the same finite execution. -/
def connectionSampleExecution (value : (Fin 3 → ℚ) → ℚ → Option (Quaternion ℚ))
    (R1 R2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Fin 3 → ℚ) := do
  let h := connectionSampleSpacing R2 tolerance
  let eta := connectionSampleAccuracy R1 R2 tolerance
  let center ← value (rationalUnitWrap a) eta
  let n0 ← value (rationalUnitWrap (rationalUnitNeighbor a h 0)) eta
  let n1 ← value (rationalUnitWrap (rationalUnitNeighbor a h 1)) eta
  let n2 ← value (rationalUnitWrap (rationalUnitNeighbor a h 2)) eta
  return ![rationalConnectionForwardSample center n0 h,
    rationalConnectionForwardSample center n1 h,rationalConnectionForwardSample center n2 h]

noncomputable section
open scoped ContDiff Quaternion

/-- Original `rationalUnitWrap_mem` guarantee for the `ConnectionSampleExecution` construction; the complete source hypotheses are retained. -/
theorem rationalUnitWrap_mem (a : Fin 3 → ℚ) (j : Fin 3) :
    (rationalUnitWrap a j : ℝ)∈Icc 0 1 := by
  have hl := Int.floor_le (a j)
  have hu := Int.lt_floor_add_one (a j)
  constructor <;> dsimp only [rationalUnitWrap] <;> push_cast
  · exact_mod_cast sub_nonneg.mpr hl
  · have h : a j-(Int.floor (a j) : ℚ) ≤ 1 := by linarith
    exact_mod_cast h

/-- Original `rationalUnitWrap_periodic` guarantee for the `ConnectionSampleExecution` construction; the complete source hypotheses are retained. -/
theorem rationalUnitWrap_periodic {E : Type*} (f : SpatialPoint → E)
    (hp : IsUnitPeriodicField f) (a : Fin 3 → ℚ) :
    f (rationalSpatialPoint (rationalUnitWrap a))=f (rationalSpatialPoint a) := by
  have he : rationalSpatialPoint (rationalUnitWrap a)=
      rationalSpatialPoint a+unitIntegerShift (fun j => -Int.floor (a j)) := by
    ext j
    simp [rationalSpatialPoint,rationalUnitWrap,unitIntegerShift,sub_eq_add_neg]
  rw [he]
  exact hp _ _

/-- Original `rationalUnitNeighbor_cast` guarantee for the `ConnectionSampleExecution` construction; the complete source hypotheses are retained. -/
theorem rationalUnitNeighbor_cast (a : Fin 3 → ℚ) (h : ℚ) (j : Fin 3) :
    rationalSpatialPoint (rationalUnitNeighbor a h j)=
      rationalSpatialPoint a+(h : ℝ) • EuclideanSpace.single j 1 := by
  ext k
  by_cases he : k=j <;> simp [rationalSpatialPoint,rationalUnitNeighbor,he]

/-- Conditional interface for the executed four values. The source-only
consumer must discharge this value accuracy using its actual reference program. -/
theorem connectionSampleExecution_error (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ x, ‖q x‖=1) (hp : IsUnitPeriodicField q)
    (value : (Fin 3 → ℚ) → ℚ → Option (Quaternion ℚ))
    (hv : ∀ b : Fin 3 → ℚ, (∀ j, (b j : ℝ)∈Icc 0 1) → ∀ t : ℚ, 0<t → t ≤ 1 →
      ∃ out, value b t=some out ∧ ‖rationalQuaternionCast out-q (rationalSpatialPoint b)‖ ≤ (t : ℝ))
    (R1 R2 : ℚ) (h1 : 0 ≤ R1) (h2 : 0 ≤ R2)
    (hb1 : ∀ x j, ‖spatialWordPartial q [j] x‖ ≤ (R1 : ℝ))
    (hb2 : ∀ x j, ‖spatialWordPartial q [j,j] x‖ ≤ (R2 : ℝ))
    (a : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ out, connectionSampleExecution value R1 R2 a tolerance=some out ∧
      ∀ j, |(out j : ℝ)-connection q (rationalSpatialPoint a) j| ≤ (tolerance : ℝ)/2 := by
  let h := connectionSampleSpacing R2 tolerance
  let eta := connectionSampleAccuracy R1 R2 tolerance
  have hh : 0<h := connectionSampleSpacing_pos R2 tolerance h2 ht
  have he : 0<eta := connectionSampleAccuracy_pos R1 R2 tolerance h1 h2 ht
  have hbudget := connectionSamplePlan_budget R1 R2 tolerance h1 h2 ht
  have he1 : eta ≤ 1 := by have := hbudget.1; dsimp only [eta]; linarith
  obtain ⟨center,hc,hec⟩ := hv (rationalUnitWrap a) (rationalUnitWrap_mem a) eta he he1
  have hn (j : Fin 3) := hv (rationalUnitWrap (rationalUnitNeighbor a h j))
    (rationalUnitWrap_mem _) eta he he1
  obtain ⟨n0,hn0,he0⟩ := hn 0
  obtain ⟨n1,hn1,he1'⟩ := hn 1
  obtain ⟨n2,hn2,he2⟩ := hn 2
  let neighbors : Fin 3 → Quaternion ℚ := ![n0,n1,n2]
  have hcn : ‖rationalQuaternionCast center-q (rationalSpatialPoint a)‖ ≤ (eta : ℝ) := by
    rwa [rationalUnitWrap_periodic q hp a] at hec
  have hnn (j : Fin 3) : ‖rationalQuaternionCast (neighbors j)-
      q (rationalSpatialPoint a+(h : ℝ) • EuclideanSpace.single j 1)‖ ≤ (eta : ℝ) := by
    rw [rationalUnitWrap_periodic q hp,rationalUnitNeighbor_cast] at he0 he1' he2
    fin_cases j <;> assumption
  refine ⟨(fun j => rationalConnectionForwardSample center (neighbors j) h),?_,?_⟩
  · change (value (rationalUnitWrap a) eta).bind _=_
    rw [hc,Option.bind_some]
    change (value (rationalUnitWrap (rationalUnitNeighbor a h 0)) eta).bind _=_
    rw [hn0,Option.bind_some]
    change (value (rationalUnitWrap (rationalUnitNeighbor a h 1)) eta).bind _=_
    rw [hn1,Option.bind_some]
    change (value (rationalUnitWrap (rationalUnitNeighbor a h 2)) eta).bind _=_
    rw [hn2,Option.bind_some]
    change some ![rationalConnectionForwardSample center n0 h,
      rationalConnectionForwardSample center n1 h,rationalConnectionForwardSample center n2 h]=_
    congr 1
    funext j
    fin_cases j <;> rfl
  · intro j
    rw [rationalConnectionForwardSample_cast]
    have herr := connectionForwardSample_error q hq hu (rationalSpatialPoint a) j
      (R1 : ℝ) (R2 : ℝ) (h : ℝ) (eta : ℝ) (by exact_mod_cast hh) (by exact_mod_cast he.le)
      (hb1 _ j) (fun y => hb2 y j) (rationalQuaternionCast center)
      (rationalQuaternionCast (neighbors j)) hcn (hnn j)
    apply herr.trans
    exact_mod_cast hbudget.2

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
