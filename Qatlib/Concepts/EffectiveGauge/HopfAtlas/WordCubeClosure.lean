/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordTransport

set_option backward.isDefEq.respectTransparency false

/-! # Extend actual coordinate-word identities from the open unit cube to every face -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of In Open Unit Cube in the Hopf Atlas construction. -/
def InOpenUnitCube (x : SpatialPoint) : Prop := ∀ i, 0<x i ∧ x i<1

/-- Original `isOpen_openUnitCube` guarantee for the `WordCubeClosure` construction; the complete source hypotheses are retained. -/
theorem isOpen_openUnitCube : IsOpen {x : SpatialPoint | InOpenUnitCube x} := by
  have hset : {x : SpatialPoint | InOpenUnitCube x}=⋂ i : Fin 3, {x : SpatialPoint | 0<x i ∧ x i<1} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_iInter,InOpenUnitCube]
  rw [hset]
  apply isOpen_iInter_of_finite
  intro i
  have hi : Continuous (fun x : SpatialPoint => x i) := (EuclideanSpace.proj i).continuous
  exact (isOpen_lt continuous_const hi).inter (isOpen_lt hi continuous_const)

/-- A one-parameter segment toward the cube centre approaches each boundary
point from the open cube, including its edges and corners. -/
theorem continuous_eq_on_closedUnitCube {E : Type*} [TopologicalSpace E] [T2Space E]
    (f g : SpatialPoint → E) (hf : Continuous f) (hg : Continuous g)
    (he : ∀ x, InOpenUnitCube x → f x=g x) (x : SpatialPoint) (hx : InUnitCube x) : f x=g x := by
  let c : SpatialPoint := WithLp.toLp 2 (fun _ => (1/2 : ℝ))
  let line : ℝ → SpatialPoint := fun t => (1-t) • x+t • c
  have hline : Continuous line :=
    ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
  have heq : EqOn (fun t => f (line t)) (fun t => g (line t)) (Ioo (0 : ℝ) 1) := by
    intro t ht
    apply he
    intro i
    have hi := hx i
    change 0<(1-t)*x i+t*(1/2) ∧ (1-t)*x i+t*(1/2)<1
    have ht0 := ht.1
    have ht1 := ht.2
    have hi0 := hi.1
    have hi1 := hi.2
    constructor <;> nlinarith [mul_nonneg (show 0≤1-t by linarith) hi0,
      mul_nonneg (show 0≤1-t by linarith) (show 0≤1-x i by linarith)]
  have hc := heq.closure (hf.comp hline) (hg.comp hline)
  have hzero : (0 : ℝ)∈closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    exact ⟨le_rfl,zero_le_one⟩
  simpa only [line,sub_zero,one_smul,zero_smul,add_zero] using hc hzero

/-- Equality of the original fields on the closed cube licenses derivatives
only on its open interior first. Continuity of the proved actual word fields
then supplies the entire closed cube. -/
theorem spatialWordPartial_eq_on_closedUnitCube {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (he : ∀ x, InUnitCube x → f x=g x) (w : List (Fin 3))
    (x : SpatialPoint) (hx : InUnitCube x) : spatialWordPartial f w x=spatialWordPartial g w x := by
  apply continuous_eq_on_closedUnitCube (spatialWordPartial f w) (spatialWordPartial g w)
    (contDiff_spatialWordPartial f hf w).continuous (contDiff_spatialWordPartial g hg w).continuous _ x hx
  intro y hy
  have heq : f=ᶠ[𝓝 y] g := by
    filter_upwards [isOpen_openUnitCube.mem_nhds hy] with z hz
    exact he z (fun i => ⟨(hz i).1.le,(hz i).2.le⟩)
  exact (spatialWordPartial_eventuallyEq heq w).eq_of_nhds

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
