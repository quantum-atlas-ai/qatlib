/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCorrectedIdentity
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordCubeClosure

set_option backward.isDefEq.respectTransparency false

/-! # Transfer stored R bounds to the actual smooth periodic reference -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The two global smooth fields agree on an open cube before their words
are identified. Continuity then includes all faces, edges and corners. -/
theorem periodicReference_word_eq_corrected (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta)
    (sc : ℍ) (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (w : List (Fin 3)) (x : SpatialPoint) (hx : InUnitCube x) :
    spatialWordPartial (fun y => periodicReference v hv q₀ h₀ eta (physicalPeriod • y)) w x=
      spatialWordPartial (fun y => correctedReference v hv q₀ h₀ eta (physicalPeriod • y)) w x := by
  have hper := (periodicReference_spec v hv hu q₀ h₀ hp eta he sc hc hi).2.1
  apply spatialWordPartial_eq_on_closedUnitCube _ _
    (hper.comp (contDiff_id.const_smul physicalPeriod))
    ((contDiff_correctedReference v hv q₀ h₀ eta).comp (contDiff_id.const_smul physicalPeriod)) _ w x hx
  intro y hy
  exact periodicReference_eq_corrected_on_cube v hv hu q₀ h₀ hp eta he sc hc hi _ (unitCube_scale_physical y hy)

/-- No derivative of the discontinuous wrapping map is taken. This theorem
bounds the very periodic reference appearing in the same mean certificate. -/
theorem materializeCorrectedPreparation_periodic_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val) (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (fun y => sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta (physicalPeriod • y)) w x‖ ≤
      ((materializeCorrectedPreparation eta prepared).correctedBounds[r.val] : ℝ) := by
  let s := originalFirstJetPair source 0
  have hsa := OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs)
  let q₀ := rescaledOriginSeed v s (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
  have hseed := rescaledOriginSeed_spec v hu s hsa (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
  have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
  change ‖spatialWordPartial (fun y => periodicReference v hv q₀ hseed.1
    (physicalPeriod*(eta : ℝ)) (physicalPeriod • y)) w x‖ ≤ _
  rw [periodicReference_word_eq_corrected v hv hu q₀ hseed.1 (spin_field_periodic hp)
    _ (mul_pos physicalPeriod_pos (Rat.cast_pos.mpr he)) _ hc hseed.2.1 w x hx]
  exact materializeCorrectedPreparation_physical_bound v hv hu hp bounds hb source prepared hrun
    eta he he1 q₀ hseed.1 r w hw x hx

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
