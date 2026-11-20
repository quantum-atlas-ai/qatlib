/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RelativeTransport
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SpinRepresentation
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

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

/-- The physical period is strictly positive, as it is twice π. -/
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

/-- Extending a continuous path by projecting real times onto the closed transport interval
gives a continuous function on the real line. -/
theorem continuous_extendPath {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E)) :
    Continuous (extendPath f) := f.continuous.comp continuous_projIcc

/-- At a real time belonging to the transport interval, the extended path evaluates to the
original path at that time. -/
@[simp] theorem extendPath_on {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E))
    (t : ℝ) (ht : t ∈ Icc 0 physicalPeriod) : extendPath f t=f ⟨t, ht⟩ := by
  simp only [extendPath, projIcc_of_mem physicalPeriod_pos.le ht]

/-- Coercing an interval time to the reals and evaluating the extended path gives the original
path value. -/
@[simp] theorem extendPath_coe {E : Type*} [TopologicalSpace E] (f : C(TransportTime, E))
    (t : TransportTime) : extendPath f t=f t := extendPath_on f t t.2

/-- Definition of coefficient Embedding in the Hopf Atlas construction. -/
def coefficientEmbedding : CoefficientPath →L[ℝ] QuaternionPath :=
  ContinuousLinearMap.compLeftContinuous ℝ TransportTime spinEmbedding.toContinuousLinearMap

/-- The quaternion coefficient path at time `t` is the purely imaginary embedding of the vector
coefficient at `t`. -/
@[simp] theorem coefficientEmbedding_apply (K : CoefficientPath) (t : TransportTime) :
    coefficientEmbedding K t=spinOfVector (K t) := rfl

/-- The pointwise imaginary-quaternion embedding preserves the supremum norm of a coefficient
path. -/
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

/-- The supremum norm of the indefinite integral from zero along a quaternion path is at most
the physical period times the original supremum norm. -/
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
    { toFun := fun f =>
        { toFun := fun t => ∫ u in (0 : ℝ)..(t : ℝ), extendPath f u
          continuous_toFun := by exact (volterraPath f).continuous }
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
    physicalPeriod (by exact volterraPath_norm)

/-- The Volterra operator evaluates at time `t` as the integral of the extended quaternion path
from zero to `t`. -/
@[simp] theorem pathVolterra_apply (f : QuaternionPath) (t : TransportTime) :
    pathVolterra f t = ∫ u in (0 : ℝ)..(t : ℝ), extendPath f u := rfl

/-- The Volterra integration operator on continuous quaternion paths has operator norm at most
the physical period. -/
theorem pathVolterra_norm_le : ‖pathVolterra‖ ≤ physicalPeriod := by
  exact LinearMap.mkContinuous_norm_le _ physicalPeriod_pos.le volterraPath_norm

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
