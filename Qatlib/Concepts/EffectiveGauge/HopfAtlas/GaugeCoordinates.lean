/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeFourierArtifact
public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Coordinates

Hopf Atlas constructions for Effective Gauge.
Defines `quaternionCoordinateCLM`, `quaternionComplexCoordinateCLM`.
Proves `quaternionCoordinateCLM_norm_le`, `quaternionComplexCoordinateCLM_norm_le`, `rationalQuaternionCoordinate_cast`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of quaternion Coordinate CLM in the Hopf Atlas construction. -/
def quaternionCoordinateCLM (j : Fin 4) : ℍ →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap

/-- Definition of quaternion Complex Coordinate CLM in the Hopf Atlas construction. -/
def quaternionComplexCoordinateCLM (j : Fin 4) : ℍ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (quaternionCoordinateCLM j)

/-- The absolute value of each real coordinate of a quaternion is bounded by its quaternion
norm. -/
theorem quaternionCoordinateCLM_norm_le (j : Fin 4) (q : ℍ) :
    ‖quaternionCoordinateCLM j q‖ ≤ ‖q‖ := by
  have h := PiLp.norm_apply_le (Quaternion.linearIsometryEquivTuple q) j
  change ‖(Quaternion.linearIsometryEquivTuple q) j‖ ≤ ‖q‖
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- The complex norm of a quaternion coordinate embedded as a real number is bounded by the norm
of the quaternion. -/
theorem quaternionComplexCoordinateCLM_norm_le (j : Fin 4) (q : ℍ) :
    ‖quaternionComplexCoordinateCLM j q‖ ≤ ‖q‖ := by
  change ‖((quaternionCoordinateCLM j q : ℝ) : ℂ)‖ ≤ ‖q‖
  rw [Complex.norm_real]
  exact quaternionCoordinateCLM_norm_le j q

/-- Extracting a real coordinate after casting a rational quaternion gives the real cast of the
corresponding rational coordinate. -/
theorem rationalQuaternionCoordinate_cast (q : Quaternion ℚ) (j : Fin 4) :
    (rationalQuaternionCoordinate q j : ℝ)=quaternionCoordinateCLM j (rationalQuaternionCast q) := by
  fin_cases j <;> rfl

/-- Extracting a complex coordinate after casting a rational quaternion gives the complex cast
of the corresponding rational coordinate. -/
theorem rationalQuaternionCoordinate_complex_cast (q : Quaternion ℚ) (j : Fin 4) :
    ((rationalQuaternionCoordinate q j : ℚ) : ℂ)=
      quaternionComplexCoordinateCLM j (rationalQuaternionCast q) := by
  rw [← Complex.ofReal_ratCast,rationalQuaternionCoordinate_cast]
  rfl

/-- Taking a complex-valued quaternion coordinate is 1-Lipschitz in the quaternion norm. -/
theorem quaternionComplexCoordinate_error (j : Fin 4) (a b : ℍ) :
    ‖quaternionComplexCoordinateCLM j a-quaternionComplexCoordinateCLM j b‖ ≤ ‖a-b‖ := by
  rw [← map_sub]
  exact quaternionComplexCoordinateCLM_norm_le j (a-b)

/-- For a smooth quaternion field with its iterated partial along `w` bounded everywhere by `M`,
the same iterated partial of each complex-valued coordinate is also bounded by `M`. -/
theorem quaternionComplexCoordinate_word_bound (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q)
    (j : Fin 4) (w : List (Fin 3)) (M : ℝ)
    (hM : ∀ x, ‖spatialWordPartial Q w x‖ ≤ M) (x : SpatialPoint) :
    ‖spatialWordPartial (fun y => quaternionComplexCoordinateCLM j (Q y)) w x‖ ≤ M := by
  rw [spatialWordPartial_clm (quaternionComplexCoordinateCLM j) Q hQ]
  exact (quaternionComplexCoordinateCLM_norm_le j _).trans (hM x)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
