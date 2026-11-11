/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeArtifactPhysicalH1
import Qatlib.Concepts.EffectiveGauge.SpectralH1.SourceGaugeFourierArtifact
import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeSpectralBudget

set_option backward.isDefEq.respectTransparency false

/-!
# Source Gauge Artifact H1

Spectral H1 constructions for Effective Gauge.
Proves `materializeGaugeFourierArtifactFromGap_H1_correct`, `automaticGaugeFourierArtifactFromGap_H1_correct`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The original source supplies both the numerical coefficient errors
and the true third derivative bound for this actual saved artifact.
The error is the ordinary unnormalized physical H1 energy. -/
theorem materializeGaugeFourierArtifactFromGap_H1_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ artifact, materializeGaugeFourierArtifactFromGap source prepared gap tolerance=some artifact ∧
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
      physicalFieldH1Energy (fun X => Q X-gaugeFourierArtifactField artifact X) ≤ (tolerance : ℝ)^2/4 ∧
      ∀ X : Fin 3 → ℚ, ∀ accuracy : ℚ, 0<accuracy →
        ‖rationalQuaternionCast (gaugeFourierArtifactValue artifact X accuracy)-
          gaugeFourierArtifactField artifact (rationalSpatialPoint X)‖ ≤ (accuracy : ℝ)/2 := by
  obtain ⟨artifact,data,hmaterialize,hindices,hrows,hcoef⟩ := materializeGaugeFourierArtifactFromGap_coefficients
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff tolerance ht
  refine ⟨artifact,hmaterialize,?_⟩
  dsimp only
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
    eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
  have hQ : ContDiff ℝ ∞ Q := selectedPoissonGauge_contDiff q spec.2.1.1 spec.1 prepared.sector
  have hQp : IsPeriodicField Q := selectedPoissonGauge_periodic q spec.2.1.1 spec.1 prepared.sector
  let P1 := cachedGaugeWordMajorant eta prepared 1
  let M3 := cachedGaugeWordMajorant eta prepared 3
  let N := finiteGaugeOutputCutoff M3 tolerance
  let accuracy := finiteGaugeCoefficientAccuracy N tolerance
  let M := finiteGaugeCoefficientMesh P1 N accuracy
  let d := finiteGaugeModeAccuracy accuracy
  let length := fourierPeriodExecution (finiteGaugeModePeriodAccuracy N accuracy)
  have ha : 0<accuracy := finiteGaugeCoefficientAccuracy_pos N tolerance ht
  have hthird (i : Fin 3) (u : SpatialPoint) :
      ‖spatialWordPartial (fun u => Q (physicalPeriod • u)) [i,i,i] u‖ ≤ (M3 : ℝ) :=
    materializeReferencePreparation_gauge_word_bound v hv hu hp source hs bounds hb prepared hrun eta collar.1 he1
      B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin [i,i,i] (by norm_num) u
  have hM3 : 0 ≤ M3 := Rat.cast_nonneg.mp ((norm_nonneg _).trans (hthird 0 0))
  have hcube (k : SpatialFrequency) (hk : k∈Finset.Icc (-N : SpatialFrequency) N) (i : Fin 3) :
      |(k i : ℝ)| ≤ (N : ℝ) := by
    have h := frequency_coordinate_abs_le_radius k i
    have hr : (frequencyRadius k : ℝ) ≤ N := by exact_mod_cast (frequency_mem_cube k N).mp hk
    exact h.trans hr
  have hbound := gaugeArtifact_physical_H1_bound Q hQ hQp artifact N M length d data hrows
    (accuracy : ℝ) (M3 : ℝ) (Rat.cast_pos.mpr ha).le (Rat.cast_nonneg.mpr hM3)
    (fun j k hk => hcoef k (hcube k hk) j) hthird
  refine ⟨hbound.trans ?_,fun X accuracy hacc => gaugeFourierArtifactValue_error artifact X accuracy hacc⟩
  have hbudget := finiteGaugeSpectral_H1_budget M3 tolerance hM3 ht
  dsimp only [finitePoissonFrequencyCount] at hbudget
  have hbudgetR : 48*(M3 : ℝ)^2/((N : ℝ)+1)^4+
      4*343*(((2*N+1)^3 : ℕ) : ℝ)*(1+3*(N : ℝ)^2)*(accuracy : ℝ)^2 ≤ (tolerance : ℝ)^2/4 := by
    exact_mod_cast hbudget
  linarith

/-- Fully automatic original-input construction, with both physical H1
accuracy to the canonical field and independent source-free point
decoding of the same finite artifact. -/
theorem automaticGaugeFourierArtifactFromGap_H1_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ prepared artifact, cachedMeanPreparationRun source bounds=some prepared ∧
      automaticGaugeFourierArtifactFromGap source bounds gap tolerance=some artifact ∧
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
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  obtain ⟨prepared,hrun,_⟩ := cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb
    eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  obtain ⟨artifact,hmat,hcert⟩ := materializeGaugeFourierArtifactFromGap_H1_correct
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff tolerance ht
  refine ⟨prepared,artifact,hrun,?_,?_⟩
  · rw [automaticGaugeFourierArtifactFromGap,hrun,Option.bind_some,hmat]
  · dsimp only at hcert ⊢
    refine ⟨hcert.1,?_,hcert.2⟩
    have htR : (0 : ℝ)<tolerance := Rat.cast_pos.mpr ht
    apply (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (tolerance : ℝ)/2)).mpr
    nlinarith [hcert.1]

end Qatlib.Concepts.EffectiveGauge.SpectralH1
