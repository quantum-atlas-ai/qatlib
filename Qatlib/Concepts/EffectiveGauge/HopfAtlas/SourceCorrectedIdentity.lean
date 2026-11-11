/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedCorrectedPreparation

set_option backward.isDefEq.respectTransparency false

/-! # The bounded corrected field is exactly the existing physical reference formula -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `spatialTransverseProjection_eq` guarantee for the `SourceCorrectedIdentity` construction; the complete source hypotheses are retained. -/
theorem spatialTransverseProjection_eq : spatialTransverseProjection=transverseProjection := rfl

/-- A global identity of smooth functions, before wrapping. It can therefore
be used for derivatives without differentiating a closed-cube equality. -/
theorem sourceCorrectedUnitLift_eq_physical (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (he : 0<eta) (he1 : eta ≤ 1/2) :
    sourceCorrectedUnitLift v hv q₀ h₀ eta=
      fun x => correctedReference v hv q₀ h₀ (physicalPeriod*eta) (physicalPeriod • x) := by
  funext x
  simp only [sourceCorrectedUnitLift,sourceCorrectionPhase,sourceUnitRealPhase,
    unitCutoffField_eq_physical eta he he1,correctedReference,
    map_smul,PiLp.smul_apply,smul_eq_mul,spatialTransverseProjection_eq]

/-- Every mixed word in the stored R vector bounds the exact globally smooth
physical corrected formula, not just a pointwise substitute on the cube. -/
theorem materializeCorrectedPreparation_physical_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (fun y => correctedReference v hv q₀ h₀
      (physicalPeriod*(eta : ℝ)) (physicalPeriod • y)) w x‖ ≤
      ((materializeCorrectedPreparation eta prepared).correctedBounds[r.val] : ℝ) := by
  rw [← sourceCorrectedUnitLift_eq_physical v hv q₀ h₀ (eta : ℝ)
    (Rat.cast_pos.mpr he) (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (show (eta : ℝ) ≤ ((1/2 : ℚ) : ℝ) from Rat.cast_le.mpr he1))]
  exact materializeCorrectedPreparation_corrected_bound v hv hu hp bounds hb source prepared hrun eta he q₀ h₀ r w hw x hx

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
