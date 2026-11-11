/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.StoredGaugeArtifact
import Qatlib.Concepts.EffectiveGauge.SpectralH1.SourceGaugeArtifactH1

set_option backward.isDefEq.respectTransparency false

/-!
# Stored Gauge Artifact H1

Spectral H1 constructions for Effective Gauge.
Proves `automaticStoredGaugeArtifactFromGap_H1_correct`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The retained finite preparation changes execution reuse, while the exact
same saved artifact retains the original physical H1 and decoder guarantees. -/
theorem automaticStoredGaugeArtifactFromGap_H1_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ prepared artifact, cachedMeanPreparationRun source bounds=some prepared ∧
      automaticStoredGaugeArtifactFromGap source bounds gap tolerance=some artifact ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
        eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
      let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
      let energy := physicalFieldH1Energy (fun X => Q X-gaugeFourierArtifactField artifact X)
      energy ≤ (tolerance : ℝ)^2/4 ∧ Real.sqrt energy ≤ (tolerance : ℝ)/2 ∧
      ∀ X : Fin 3 → ℚ, ∀ accuracy : ℚ, 0<accuracy →
        ‖rationalQuaternionCast (gaugeFourierArtifactValue artifact X accuracy)-
          gaugeFourierArtifactField artifact (rationalSpatialPoint X)‖ ≤ (accuracy : ℝ)/2 := by
  rw [automaticStoredGaugeArtifactFromGap_output]
  exact automaticGaugeFourierArtifactFromGap_H1_correct v hv hu hp source hs bounds hb
    gap hgap B hB hg hoff tolerance ht

end Qatlib.Concepts.EffectiveGauge.SpectralH1
