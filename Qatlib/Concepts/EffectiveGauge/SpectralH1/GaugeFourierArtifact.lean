/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.NormalizedGaugeSampling
import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeSpectralPlan
import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientGridExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Fourier Artifact

Spectral H1 constructions for Effective Gauge.
Defines `RationalGaugeGridData`, `RationalGaugeFourierCoefficients`, `gaugeArtifactFrequency`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Abbreviation for Rational Gauge Grid Data in the Spectral H1 construction. -/
abbrev RationalGaugeGridData := List (SourceMeanIndex × Quaternion ℚ)
/-- Abbreviation for Rational Gauge Fourier Coefficients in the Spectral H1 construction. -/
abbrev RationalGaugeFourierCoefficients := List (Vector ℤ 3 × Vector RationalCircleSample 4)

/-- Definition of gauge Artifact Frequency in the Spectral H1 construction. -/
def gaugeArtifactFrequency (k : Vector ℤ 3) : SpatialFrequency := fun j => k[j.val]

/-- Definition of rational Quaternion Coordinate in the Spectral H1 construction. -/
def rationalQuaternionCoordinate (q : Quaternion ℚ) (j : Fin 4) : ℚ := ![q.re,q.imI,q.imJ,q.imK] j

/-- Definition of gauge Grid Execution in the Spectral H1 construction. -/
def gaugeGridExecution (sample : SourceMeanIndex → Option (Quaternion ℚ)) :
    List SourceMeanIndex → Option RationalGaugeGridData
  | [] => some []
  | index::rest => (sample index).bind (fun value =>
      (gaugeGridExecution sample rest).map (fun data => (index,value)::data))

/-- Definition of rational Gauge Coefficient Term in the Spectral H1 construction. -/
def rationalGaugeCoefficientTerm (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (record : SourceMeanIndex × Quaternion ℚ) (j : Fin 4) : RationalCircleSample :=
  let e := (rationalFourierMode length (-k) (sourceMeanUnitPoint M record.1) d).value
  let value := rationalQuaternionCoordinate record.2 j
  (e.1*value,e.2*value)

/-- Definition of rational Gauge Fourier Coefficients Of Data in the Spectral H1 construction. -/
def rationalGaugeFourierCoefficientsOfData (M : ℕ) (length : ℚ) (k : SpatialFrequency) (d : ℚ)
    (data : RationalGaugeGridData) : Fin 4 → RationalCircleSample :=
  fun j => rationalPairAverage M (data.map (fun record => rationalGaugeCoefficientTerm M length k d record j))

/-- Only a finite list of integer frequencies and rational component pairs
is retained. There is no source, gauge state, reference or PDE callback. -/
structure RationalGaugeFourierArtifact where
  coefficients : RationalGaugeFourierCoefficients

/-- Definition of materialize Gauge Fourier Artifact From Gap in the Spectral H1 construction. -/
def materializeGaugeFourierArtifactFromGap (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) : Option RationalGaugeFourierArtifact := do
  let eta := referenceUnitCollar gap
  let P1 := cachedGaugeWordMajorant eta prepared 1
  let M3 := cachedGaugeWordMajorant eta prepared 3
  let N := finiteGaugeOutputCutoff M3 tolerance
  let accuracy := finiteGaugeCoefficientAccuracy N tolerance
  let M := finiteGaugeCoefficientMesh P1 N accuracy
  let sampleAccuracy := finiteGaugeSampleAccuracy accuracy
  let d := finiteGaugeModeAccuracy accuracy
  let ell := finiteGaugeModePeriodAccuracy N accuracy
  let length := fourierPeriodExecution ell
  let plan ← materializeGaugeUnitSamplingFromGap source prepared gap sampleAccuracy
  let data ← gaugeGridExecution
    (fun index => sourceGaugeUnitSampling source gap plan (sourceMeanUnitPoint M index)) (sourceMeanGrid M)
  return ⟨(sourceFrequencyGrid N).map (fun k => (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData M length k d data)))⟩

/-- Definition of automatic Gauge Fourier Artifact From Gap in the Spectral H1 construction. -/
def automaticGaugeFourierArtifactFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option RationalGaugeFourierArtifact :=
  (cachedMeanPreparationRun source bounds).bind (fun prepared =>
    materializeGaugeFourierArtifactFromGap source prepared gap tolerance)

/-- Definition of gauge Artifact Coefficient L1 in the Spectral H1 construction. -/
def gaugeArtifactCoefficientL1 (artifact : RationalGaugeFourierArtifact) : ℚ :=
  (artifact.coefficients.map (fun record => ∑ j : Fin 4, (|(record.2[j.val]).1| + |(record.2[j.val]).2|))).sum

/-- Definition of gauge Artifact Cis Accuracy in the Spectral H1 construction. -/
def gaugeArtifactCisAccuracy (artifact : RationalGaugeFourierArtifact) (accuracy : ℚ) : ℚ :=
  min 1 (accuracy/(8*(gaugeArtifactCoefficientL1 artifact+1)))

/-- A finite source-free evaluation of the saved spectral artifact.
The meaning uses exact integer physical frequencies, not approximate L. -/
def gaugeFourierArtifactValue (artifact : RationalGaugeFourierArtifact) (X : Fin 3 → ℚ)
    (accuracy : ℚ) : Quaternion ℚ :=
  let d := gaugeArtifactCisAccuracy artifact accuracy
  let terms : List (Fin 4 → RationalCircleSample) := artifact.coefficients.map (fun record =>
    let e := (rationalCis (rationalWindingAngle (gaugeArtifactFrequency record.1) X) d).value
    fun j : Fin 4 => cisPairMul (record.2[j.val]) e)
  let coordinate := fun j : Fin 4 => ((terms.map (fun (term : Fin 4 → RationalCircleSample) => term j)).sum).1
  ⟨coordinate 0,coordinate 1,coordinate 2,coordinate 3⟩

noncomputable section
open scoped Quaternion

/-- Definition of gauge Fourier Artifact Field in the Spectral H1 construction. -/
def gaugeFourierArtifactField (artifact : RationalGaugeFourierArtifact) (X : SpatialPoint) : ℍ :=
  let coordinate := fun j : Fin 4 =>
    ((artifact.coefficients.map (fun record => rationalCircleCast (record.2[j.val])*
      unitFourierMode (gaugeArtifactFrequency record.1) (physicalPeriod⁻¹ • X))).sum).re
  ⟨coordinate 0,coordinate 1,coordinate 2,coordinate 3⟩

end
end Qatlib.Concepts.EffectiveGauge.SpectralH1
