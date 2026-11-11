/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeCoefficientGrid
import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeCoefficientBudget

set_option backward.isDefEq.respectTransparency false

/-!
# Source Gauge Fourier Artifact

Spectral H1 constructions for Effective Gauge.
Proves `materializeGaugeFourierArtifactFromGap_coefficients`, `automaticGaugeFourierArtifactFromGap_success`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original source and bounds produce one finite saved artifact. Every
stored component approximates the true coefficient of the same canonical
gauge. No coefficient, point-value or Q-modulus promise is an input. -/
theorem materializeGaugeFourierArtifactFromGap_coefficients (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
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
    let Q := fun u => selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector (physicalPeriod • u)
    let hQ := (selectedPoissonGauge_contDiff q spec.2.1.1 spec.1 prepared.sector).comp
      (contDiff_id.const_smul physicalPeriod)
    let hQp : IsUnitPeriodicField Q := periodicField_rescale_unit _ (selectedPoissonGauge_periodic q spec.2.1.1 spec.1 prepared.sector)
    let P1 := cachedGaugeWordMajorant eta prepared 1
    let N := finiteGaugeOutputCutoff (cachedGaugeWordMajorant eta prepared 3) tolerance
    let accuracy := finiteGaugeCoefficientAccuracy N tolerance
    let M := finiteGaugeCoefficientMesh P1 N accuracy
    let d := finiteGaugeModeAccuracy accuracy
    let length := fourierPeriodExecution (finiteGaugeModePeriodAccuracy N accuracy)
    ∃ artifact data, materializeGaugeFourierArtifactFromGap source prepared gap tolerance=some artifact ∧
      data.map Prod.fst=sourceMeanGrid M ∧
      artifact.coefficients=(sourceFrequencyGrid N).map (fun k =>
        (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data))) ∧
      ∀ k : SpatialFrequency, (∀ i, |(k i : ℝ)| ≤ (N : ℝ)) → ∀ j : Fin 4,
      let f := fun x => quaternionComplexCoordinateCLM j (Q x)
      let hf := (quaternionComplexCoordinateCLM j).contDiff.comp hQ
      let hp' : IsUnitPeriodicField f := fun x n => by dsimp only [f]; rw [hQp x n]
      ‖unitFourierCoefficient f hf.continuous hp' k-
        rationalCircleCast (rationalGaugeFourierCoefficientsOfData M length k d data j)‖ ≤ (accuracy : ℝ) := by
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
  let Q := fun u => selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector (physicalPeriod • u)
  have hQ : ContDiff ℝ ∞ Q := (selectedPoissonGauge_contDiff q spec.2.1.1 spec.1 prepared.sector).comp
    (contDiff_id.const_smul physicalPeriod)
  have hQp : IsUnitPeriodicField Q := periodicField_rescale_unit _
    (selectedPoissonGauge_periodic q spec.2.1.1 spec.1 prepared.sector)
  let P1 := cachedGaugeWordMajorant eta prepared 1
  let N := finiteGaugeOutputCutoff (cachedGaugeWordMajorant eta prepared 3) tolerance
  let accuracy := finiteGaugeCoefficientAccuracy N tolerance
  let M := finiteGaugeCoefficientMesh P1 N accuracy
  let s := finiteGaugeSampleAccuracy accuracy
  let d := finiteGaugeModeAccuracy accuracy
  let ell := finiteGaugeModePeriodAccuracy N accuracy
  let length := fourierPeriodExecution ell
  have ha : 0<accuracy := finiteGaugeCoefficientAccuracy_pos N tolerance ht
  have hspos : 0<s := div_pos ha (by norm_num)
  have hword (x : SpatialPoint) (i : Fin 3) : ‖spatialWordPartial Q [i] x‖ ≤ (P1 : ℝ) :=
    materializeReferencePreparation_gauge_word_bound v hv hu hp source hs bounds hb prepared hrun
      eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin [i] (by norm_num) x
  have hP : 0 ≤ P1 := Rat.cast_nonneg.mp ((norm_nonneg _).trans (hword 0 0))
  have hM := (finiteGaugeCoefficientMesh_spec P1 N accuracy ha).1
  have hd := finiteGaugeModeAccuracy_spec accuracy ha
  have hell := finiteGaugeModePeriodAccuracy_spec N accuracy ha
  obtain ⟨plan,hplan,hprep,hsampling⟩ := materializeGaugeUnitSamplingFromGap_correct
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff s hspos
  let sample := fun index => sourceGaugeUnitSampling source gap plan (sourceMeanUnitPoint M index)
  have hsample (index : SourceMeanIndex) : ∃ out, sample index=some out ∧
      ‖rationalQuaternionCast out-Q (rationalSpatialPoint (sourceMeanUnitPoint M index))‖ ≤ (s : ℝ) := by
    simpa only [hprep] using hsampling (sourceMeanUnitPoint M index)
  have hnorm (x : SpatialPoint) : ‖Q x‖ ≤ 1 :=
    (selectedPoissonGauge_norm q spec.2.1.1 spec.1 (fun z => (spec.2.1.2 z).1) prepared.sector _).le
  have hperiod := fourierPeriodExecution_error ell hell.1
  have hellR : 3*(N : ℝ)*(ell : ℝ) ≤ (d : ℝ)/2 := by exact_mod_cast hell.2
  obtain ⟨data,hdata,hindices,herror⟩ := gaugeGridExecution_coefficient_error Q hQ hQp hnorm P1 hP hword
    M hM sample s hsample N length d hd.1 hd.2.1 (ell : ℝ) hperiod hellR
  let artifact : RationalGaugeFourierArtifact := ⟨(sourceFrequencyGrid N).map (fun k =>
    (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data)))⟩
  refine ⟨artifact,data,?_,hindices,rfl,?_⟩
  · change (materializeGaugeUnitSamplingFromGap source prepared gap s).bind
      (fun plan => (gaugeGridExecution
        (fun index => sourceGaugeUnitSampling source gap plan (sourceMeanUnitPoint M index))
        (sourceMeanGrid M)).bind (fun data => some ⟨(sourceFrequencyGrid N).map (fun k =>
          (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data)))⟩))=some artifact
    rw [hplan,Option.bind_some]
    change (gaugeGridExecution sample (sourceMeanGrid M)).bind _=some artifact
    rw [hdata]
    rfl
  · intro k hk j
    have he := herror k hk j
    have hbudget : 3*((P1 : ℝ)+7*(N : ℝ))/(M : ℝ)+((s : ℝ)+(1+(s : ℝ))*(d : ℝ)) ≤ (accuracy : ℝ) := by
      exact_mod_cast finiteGaugeCoefficientSampling_budget P1 N accuracy ha
    exact he.trans hbudget

/-- The automatic entry really terminates with a saved artifact, preparing
the mean once. Its coefficient certificate is the preceding theorem for
this identical successful preparation and materialization. -/
theorem automaticGaugeFourierArtifactFromGap_success (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ prepared artifact, cachedMeanPreparationRun source bounds=some prepared ∧
      materializeGaugeFourierArtifactFromGap source prepared gap tolerance=some artifact ∧
      automaticGaugeFourierArtifactFromGap source bounds gap tolerance=some artifact := by
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  obtain ⟨prepared,hrun,_⟩ := cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb
    eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  obtain ⟨artifact,data,hmaterialize,_⟩ := materializeGaugeFourierArtifactFromGap_coefficients
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff tolerance ht
  refine ⟨prepared,artifact,hrun,hmaterialize,?_⟩
  rw [automaticGaugeFourierArtifactFromGap,hrun,Option.bind_some,hmaterialize]

end Qatlib.Concepts.EffectiveGauge.SpectralH1
