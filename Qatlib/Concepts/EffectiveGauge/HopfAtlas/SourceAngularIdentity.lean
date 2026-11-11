/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceAngularWord

set_option backward.isDefEq.respectTransparency false

/-! # Angular majorants refer to the same real phase and physical terminal ratio -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of spatial Transverse Projection in the Hopf Atlas construction. -/
def spatialTransverseProjection : SpatialPoint →L[ℝ] TransversePoint :=
  (ContinuousLinearMap.fst ℝ TransversePoint ℝ).comp sourcePositionInverse

/-- Original `spatialTransverseProjection_axis_one` guarantee for the `SourceAngularIdentity` construction; the complete source hypotheses are retained. -/
theorem spatialTransverseProjection_axis_one :
    spatialTransverseProjection (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))=
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
  ext j
  fin_cases j <;> rfl

/-- Original `wordAngularRate_transversePullback` guarantee for the `SourceAngularIdentity` construction; the complete source hypotheses are retained. -/
theorem wordAngularRate_transversePullback (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k)
    (u : SpatialPoint) :
    wordAngularRate (fun x => k (spatialTransverseProjection x)) 1 u=
      circleAngularRate k (spatialTransverseProjection u) := by
  have hd := ((hk.differentiable (by simp) (spatialTransverseProjection u)).hasFDerivAt).comp u spatialTransverseProjection.hasFDerivAt
  change HasFDerivAt (fun x => k (spatialTransverseProjection x)) _ u at hd
  unfold wordAngularRate
  simp only [spatialWordPartial]
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,spatialTransverseProjection_axis_one]
  rfl

/-- The unit field's angular rate retains exactly the physical chain-rule
factor L; this is an identity of real rates, rather than only of phases. -/
theorem sourceUnitTerminalRatio_angular_eq (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (u : SpatialPoint) :
    wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1 u=
      physicalPeriod*circleAngularRate (terminalRatio v hv q₀ h₀)
        (physicalPeriod • spatialTransverseProjection u) := by
  have heq : sourceUnitTerminalRatio v hv q₀ h₀=
      fun x => (fun p => terminalRatio v hv q₀ h₀ (physicalPeriod • p)) (spatialTransverseProjection x) :=
    funext (sourceUnitTerminalRatio_eq v hv hu q₀ h₀)
  rw [heq,wordAngularRate_transversePullback
    (fun p : TransversePoint => terminalRatio v hv q₀ h₀ (physicalPeriod • p))
    ((contDiff_terminalRatio v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod)) u]
  exact circleAngularRate_scaled _ (contDiff_terminalRatio v hv q₀ h₀)
    physicalPeriod (spatialTransverseProjection u)

/-- Definition of source Unit Real Phase in the Hopf Atlas construction. -/
def sourceUnitRealPhase (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (u : SpatialPoint) : ℝ :=
  terminalRealPhase v hv q₀ h₀ (physicalPeriod • spatialTransverseProjection u)

/-- The exact real primitive, including all turns, is the one used by the
existing source real-phase algorithm. -/
theorem sourceUnitRealPhase_primitive (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (u : SpatialPoint) :
    sourceUnitRealPhase v hv q₀ h₀ u=
      circleLogPrimitive (fun p => terminalRatio v hv q₀ h₀ (physicalPeriod • p))
        (spatialTransverseProjection u) := by
  let p := spatialTransverseProjection u
  have hp : transversePair (p 0,p 1)=p := by ext j; fin_cases j <;> rfl
  have h := circleLogPrimitive_scaled (terminalRatio v hv q₀ h₀)
    (contDiff_terminalRatio v hv q₀ h₀) physicalPeriod (p 0) (p 1)
  rw [← transversePair_scale,hp] at h
  exact h.symm

/-- With the actual source-selected compatible seed and original geometry,
the very same terminal field is circle-valued. -/
theorem sourceUnitTerminalRatio_selected_circle (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (u : SpatialPoint) :
    IsCircleQuaternion (sourceUnitTerminalRatio v hv (rescaledOriginSeed v source m1 m2)
      (rescaledOriginSeed_spec v hu source hs m1 m2).1 u) := by
  rw [sourceUnitTerminalRatio_eq v hv hu]
  exact rescaledTerminalRatio_circle v hv hu hp source hs m1 m2 B hB mu hm hg hoff
    (spatialTransverseProjection u)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
