/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceAngularIdentity
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordPrimitive

set_option backward.isDefEq.respectTransparency false

/-! # The actual source real phase is a coordinate primitive with the exact derivative -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `contDiff_sourceUnitRealPhase` guarantee for the `SourcePhasePrimitive` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceUnitRealPhase (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (sourceUnitRealPhase v hv q₀ h₀) :=
  (contDiff_terminalRealPhase v hv q₀ h₀).comp
    ((contDiff_id.const_smul physicalPeriod).comp spatialTransverseProjection.contDiff)

/-- Original `spatialTransverseProjection_face_one` guarantee for the `SourcePhasePrimitive` construction; the complete source hypotheses are retained. -/
theorem spatialTransverseProjection_face_one (a : ℝ) (x : SpatialPoint) :
    spatialTransverseProjection (coordinateFace 1 a x)=
      transversePair (a,(spatialTransverseProjection x) 1) := by
  ext i
  fin_cases i
  · exact coordinateFace_same 1 a x
  · exact coordinateFace_other 1 2 a x (by decide)

/-- Original `circleLogPrimitive_y_partial` guarantee for the `SourcePhasePrimitive` construction; the complete source hypotheses are retained. -/
theorem circleLogPrimitive_y_partial (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k)
    (p : TransversePoint) :
    fderiv ℝ (circleLogPrimitive k) p (EuclideanSpace.single 0 1)=circleAngularRate k p := by
  have hp : transversePair (p 0,p 1)=p := by ext i; fin_cases i <;> rfl
  have hd := (((contDiff_circleLogPrimitive hk).differentiable (by simp)
    (transversePair (p 0,p 1))).hasFDerivAt).comp_hasDerivAt (p 0)
      (transversePair_hasDerivAt (p 1) (p 0))
  have he := hd.unique (circleLogPrimitive_hasDerivAt hk (p 1) (p 0))
  simpa only [hp] using he

/-- Original `spatialWordPartial_scalar_transversePullback` guarantee for the `SourcePhasePrimitive` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_scalar_transversePullback (f : TransversePoint → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : SpatialPoint) :
    spatialWordPartial (fun y => f (spatialTransverseProjection y)) [1] x=
      fderiv ℝ f (spatialTransverseProjection x) (EuclideanSpace.single 0 1) := by
  have hd := ((hf.differentiable (by simp) (spatialTransverseProjection x)).hasFDerivAt).comp x
    spatialTransverseProjection.hasFDerivAt
  change HasFDerivAt (fun y => f (spatialTransverseProjection y)) _ x at hd
  change fderiv ℝ (fun y => f (spatialTransverseProjection y)) x (EuclideanSpace.single 1 1)=_
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,spatialTransverseProjection_axis_one]

/-- Original `sourceUnitRealPhase_y_partial` guarantee for the `SourcePhasePrimitive` construction; the complete source hypotheses are retained. -/
theorem sourceUnitRealPhase_y_partial (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) :
    spatialWordPartial (sourceUnitRealPhase v hv q₀ h₀) [1]=
      wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1 := by
  let k := fun p => terminalRatio v hv q₀ h₀ (physicalPeriod • p)
  have hk : ContDiff ℝ ∞ k :=
    (contDiff_terminalRatio v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod)
  have hphase : sourceUnitRealPhase v hv q₀ h₀=
      fun y => circleLogPrimitive k (spatialTransverseProjection y) :=
    funext (sourceUnitRealPhase_primitive v hv q₀ h₀)
  have hratio : sourceUnitTerminalRatio v hv q₀ h₀=fun y => k (spatialTransverseProjection y) :=
    funext (sourceUnitTerminalRatio_eq v hv hu q₀ h₀)
  funext x
  rw [hphase,hratio,spatialWordPartial_scalar_transversePullback _ (contDiff_circleLogPrimitive hk),
    wordAngularRate_transversePullback k hk,circleLogPrimitive_y_partial k hk]

/-- The normalized real phase is precisely this real-valued integral. Its
representation retains all winding information and the physical scaling. -/
theorem sourceUnitRealPhase_coordinatePrimitive (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) :
    sourceUnitRealPhase v hv q₀ h₀=
      coordinatePrimitive (wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1) := by
  let k := fun p => terminalRatio v hv q₀ h₀ (physicalPeriod • p)
  have hk : ContDiff ℝ ∞ k :=
    (contDiff_terminalRatio v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod)
  have hratio : sourceUnitTerminalRatio v hv q₀ h₀=fun y => k (spatialTransverseProjection y) :=
    funext (sourceUnitTerminalRatio_eq v hv hu q₀ h₀)
  funext x
  rw [sourceUnitRealPhase_primitive]
  change (∫ s in (0 : ℝ)..x 1, circleAngularRate k
    (transversePair (s,(spatialTransverseProjection x) 1)))=_
  unfold coordinatePrimitive
  apply integral_congr
  intro s hs
  rw [hratio]
  change circleAngularRate k (transversePair (s,(spatialTransverseProjection x) 1))=
    wordAngularRate (fun y => k (spatialTransverseProjection y)) 1 (coordinateFace 1 s x)
  rw [wordAngularRate_transversePullback k hk,spatialTransverseProjection_face_one]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
