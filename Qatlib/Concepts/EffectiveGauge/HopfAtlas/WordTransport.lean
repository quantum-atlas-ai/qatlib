/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCoefficientWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.TransverseInitial

set_option backward.isDefEq.respectTransparency false

/-! # Differentiating the same normalized physical transport, including slab endpoints -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
open Set Filter
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `spatialWordPartial_eventuallyEq` guarantee for the `WordTransport` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : SpatialPoint → E} {x : SpatialPoint} (h : f =ᶠ[𝓝 x] g) (w : List (Fin 3)) :
    spatialWordPartial f w =ᶠ[𝓝 x] spatialWordPartial g w := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    exact (ih.fderiv (𝕜 := ℝ)).mono fun y hy =>
      congrArg (fun A : SpatialPoint →L[ℝ] E => A (EuclideanSpace.single i 1)) hy

/-- Differentiate on the open slab first. Equality on a closed cube at one
point alone would not justify this step. -/
theorem spatialWordPartial_transport_interior (q K : SpatialPoint → ℍ)
    (hq : ContDiff ℝ ∞ q)
    (hode : ∀ x : SpatialPoint, 0 ≤ x 0 ∧ x 0 ≤ 1 → spatialWordPartial q [0] x=q x*K x)
    (w : List (Fin 3)) (x : SpatialPoint) (hx : 0<x 0 ∧ x 0<1) :
    spatialWordPartial q (0::w) x=spatialWordPartial (fun y => q y*K y) w x := by
  have hcoord : Continuous (fun y : SpatialPoint => y 0) := (EuclideanSpace.proj 0).continuous
  have hopen : IsOpen {y : SpatialPoint | 0<y 0 ∧ y 0<1} :=
    (isOpen_lt continuous_const hcoord).inter (isOpen_lt hcoord continuous_const)
  have he : spatialWordPartial q [0] =ᶠ[𝓝 x] (fun y => q y*K y) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hode y ⟨hy.1.le,hy.2.le⟩
  have hw := (spatialWordPartial_eventuallyEq he w).eq_of_nhds
  rw [← spatialWordPartial_append] at hw
  have hperm : (0::w).Perm (w++[0]) :=
    (List.perm_append_comm : ([0]++w).Perm (w++[0]))
  rw [spatialWordPartial_perm q hq hperm]
  exact hw

/-- Continuity supplies the two endpoint faces after differentiation in the
interior. No derivative of wrapping, or endpoint-only identity, is used. -/
theorem spatialWordPartial_transport_slab (q K : SpatialPoint → ℍ)
    (hq : ContDiff ℝ ∞ q) (hK : ContDiff ℝ ∞ K)
    (hode : ∀ x : SpatialPoint, 0 ≤ x 0 ∧ x 0 ≤ 1 → spatialWordPartial q [0] x=q x*K x)
    (w : List (Fin 3)) (x : SpatialPoint) (hx : 0 ≤ x 0 ∧ x 0 ≤ 1) :
    spatialWordPartial q (0::w) x=spatialWordPartial (fun y => q y*K y) w x := by
  let line : ℝ → SpatialPoint := fun t => x+(t-x 0) • EuclideanSpace.single 0 1
  have hline : Continuous line := continuous_const.add
    ((continuous_id.sub continuous_const).smul continuous_const)
  have hcoord (t : ℝ) : line t 0=t := by simp [line]
  have he : EqOn (fun t => spatialWordPartial q (0::w) (line t))
      (fun t => spatialWordPartial (fun y => q y*K y) w (line t)) (Ioo 0 1) := by
    intro t ht
    apply spatialWordPartial_transport_interior q K hq hode w
    simpa only [hcoord,Set.mem_Ioo] using ht
  have hc := he.closure ((contDiff_spatialWordPartial q hq (0::w)).continuous.comp hline)
    ((contDiff_spatialWordPartial _ (hq.mul hK) w).continuous.comp hline)
  have hxcl : x 0 ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    exact hx
  simpa only [line,sub_self,zero_smul,add_zero] using hc hxcl

/-- Original `sourceLiftSpatialExtension_unit_initial` guarantee for the `WordTransport` construction; the complete source hypotheses are retained. -/
theorem sourceLiftSpatialExtension_unit_initial (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (x : SpatialPoint) (hx : x 0=0) :
    sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • x)=q₀ := by
  change sourceLiftExtension v hv q₀ h₀
    ((sourcePositionInverse (physicalPeriod • x)).1,(physicalPeriod • x) 0)=q₀
  have hzero : (physicalPeriod • x) 0=0 := by simp [hx]
  rw [hzero,sourceLiftExtension_eq v hv hu q₀ h₀ _ ⟨0,⟨le_rfl,physicalPeriod_pos.le⟩⟩]
  exact pathTransport_start q₀ h₀ _

/-- Original `sourceLiftSpatialExtension_unit_transverse_initial` guarantee for the `WordTransport` construction; the complete source hypotheses are retained. -/
theorem sourceLiftSpatialExtension_unit_transverse_initial (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (w : List (Fin 3)) (htrans : ∀ i ∈ w, i≠0) (hw : w≠[])
    (x : SpatialPoint) (hx : x 0=0) :
    spatialWordPartial (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) w x=0 :=
  spatialWordPartial_plane_constant _
    ((contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod))
    q₀ (sourceLiftSpatialExtension_unit_initial v hv hu q₀ h₀) w htrans hw x hx

/-- Original `sourceLiftSpatialExtension_unit_word_ode` guarantee for the `WordTransport` construction; the complete source hypotheses are retained. -/
theorem sourceLiftSpatialExtension_unit_word_ode (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (w : List (Fin 3)) (x : SpatialPoint) (hx : 0 ≤ x 0 ∧ x 0 ≤ 1) :
    spatialWordPartial (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) (0::w) x=
      spatialWordPartial (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)*
        sourceHorizontalQuaternion (unitCoordinateSpin v) y) w x :=
  spatialWordPartial_transport_slab _ _
    ((contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod))
    (contDiff_sourceHorizontalQuaternion (contDiff_unitCoordinateSpin v hv))
    (sourceLiftSpatialExtension_unit_timePartial v hv hu q₀ h₀) w x hx

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
