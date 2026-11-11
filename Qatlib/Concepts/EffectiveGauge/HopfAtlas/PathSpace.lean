/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RelativeTransport
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SpinRepresentation
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous paths on the physical transport interval

The path norm is the actual uniform quaternion / Euclidean norm on [0,2 pi].
The Volterra operator integrates a clamped continuous extension; on the
physical interval this is the original path, including both endpoints.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace NNReal Topology
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `physicalPeriod_pos` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
theorem physicalPeriod_pos : 0 < physicalPeriod := by
  unfold physicalPeriod
  positivity

/-- Abbreviation for Transport Time in the Hopf Atlas construction. -/
abbrev TransportTime := Icc (0 : ℝ) physicalPeriod
/-- Abbreviation for Quaternion Path in the Hopf Atlas construction. -/
abbrev QuaternionPath := C(TransportTime, ℍ)
/-- Abbreviation for Coefficient Path in the Hopf Atlas construction. -/
abbrev CoefficientPath := C(TransportTime, SpatialPoint)

/-- Definition of transport Start in the Hopf Atlas construction. -/
def transportStart : TransportTime := ⟨0, le_rfl, physicalPeriod_pos.le⟩

/-- The initial time supplies a point of the transport interval. -/
instance : Nonempty TransportTime := ⟨transportStart⟩

/-- Definition of extend Path in the Hopf Atlas construction. -/
def extendPath {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E)) (t : ℝ) : E :=
  f (projIcc 0 physicalPeriod physicalPeriod_pos.le t)

/-- Original `continuous_extendPath` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
theorem continuous_extendPath {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E)) :
    Continuous (extendPath f) := f.continuous.comp continuous_projIcc

/-- Original `extendPath_on` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
@[simp] theorem extendPath_on {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E))
    (t : ℝ) (ht : t ∈ Icc 0 physicalPeriod) : extendPath f t=f ⟨t, ht⟩ := by
  simp only [extendPath, projIcc_of_mem physicalPeriod_pos.le ht]

/-- Original `extendPath_coe` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
@[simp] theorem extendPath_coe {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E))
    (t : TransportTime) : extendPath f t=f t := extendPath_on f t t.2

/-- Definition of coefficient Embedding in the Hopf Atlas construction. -/
def coefficientEmbedding : CoefficientPath →L[ℝ] QuaternionPath :=
  ContinuousLinearMap.compLeftContinuous ℝ TransportTime spinEmbedding.toContinuousLinearMap

/-- Original `coefficientEmbedding_apply` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
@[simp] theorem coefficientEmbedding_apply (K : CoefficientPath) (t : TransportTime) :
    coefficientEmbedding K t=spinOfVector (K t) := rfl

/-- Original `coefficientEmbedding_norm` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
theorem coefficientEmbedding_norm (K : CoefficientPath) : ‖coefficientEmbedding K‖=‖K‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg K)).mpr
    intro t
    simpa only [coefficientEmbedding_apply, spinOfVector_norm] using K.norm_coe_le_norm t
  · apply (ContinuousMap.norm_le _ (norm_nonneg (coefficientEmbedding K))).mpr
    intro t
    simpa only [coefficientEmbedding_apply, spinOfVector_norm] using
      (coefficientEmbedding K).norm_coe_le_norm t

/-- Definition of volterra Path in the Hopf Atlas construction. -/
private def volterraPath (f : QuaternionPath) : QuaternionPath where
  toFun t := ∫ u in (0 : ℝ)..(t : ℝ), extendPath f u
  continuous_toFun := by
    have h : Continuous (fun t : ℝ => ∫ u in (0 : ℝ)..t, extendPath f u) :=
      continuous_iff_continuousAt.mpr fun t =>
        ((continuous_extendPath f).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
    exact h.comp continuous_subtype_val

/-- Original `volterraPath_norm` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
private theorem volterraPath_norm (f : QuaternionPath) : ‖volterraPath f‖ ≤ physicalPeriod*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg physicalPeriod_pos.le (norm_nonneg f))).mpr
  intro t
  change ‖∫ u in (0 : ℝ)..(t : ℝ), extendPath f u‖ ≤ _
  calc
    _ ≤ ‖f‖*|(t : ℝ)-0| := norm_integral_le_of_norm_le_const
      (fun u _ => f.norm_coe_le_norm _)
    _ ≤ physicalPeriod*‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.2.1, mul_comm]
      exact mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg f)

/-- Bounded real-linear indefinite integration on the physical interval. -/
def pathVolterra : QuaternionPath →L[ℝ] QuaternionPath :=
  LinearMap.mkContinuous
    { toFun := volterraPath
      map_add' := by
        intro f g
        apply ContinuousMap.ext
        intro t
        change (∫ u in (0 : ℝ)..(t : ℝ), extendPath f u+extendPath g u) = _
        exact integral_add ((continuous_extendPath f).intervalIntegrable _ _)
          ((continuous_extendPath g).intervalIntegrable _ _)
      map_smul' := by
        intro c f
        apply ContinuousMap.ext
        intro t
        change (∫ u in (0 : ℝ)..(t : ℝ), c • extendPath f u) = _
        exact integral_smul c (extendPath f) }
    physicalPeriod volterraPath_norm

/-- Original `pathVolterra_apply` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
@[simp] theorem pathVolterra_apply (f : QuaternionPath) (t : TransportTime) :
    pathVolterra f t = ∫ u in (0 : ℝ)..(t : ℝ), extendPath f u := rfl

/-- Original `pathVolterra_norm_le` guarantee for the `PathSpace` construction; the complete source hypotheses are retained. -/
theorem pathVolterra_norm_le : ‖pathVolterra‖ ≤ physicalPeriod := by
  exact LinearMap.mkContinuous_norm_le _ physicalPeriod_pos.le volterraPath_norm

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
