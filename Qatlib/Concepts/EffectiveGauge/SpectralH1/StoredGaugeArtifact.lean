/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.StoredGaugeUnitSampling
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeededGaugeGrid
import Qatlib.Concepts.EffectiveGauge.SpectralH1.GaugeFourierArtifact
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SeedPaletteExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Stored Gauge Artifact

Spectral H1 constructions for Effective Gauge.
Defines `StoredGaugeArtifactParameters`, `storedGaugeArtifactParameters`, `storedGaugeArtifactExecution`.
Proves `storedSourceGaugeFromPrepared_fields`, `materializeStoredGaugeUnitSampling_fields`, `materializeStoredGaugeUnitSampling_output`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `storedSourceGaugeFromPrepared_fields` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem storedSourceGaugeFromPrepared_fields (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) (state : StoredGaugeState)
    (h : storedSourceGaugeFromPrepared source frame tolerance=some state) :
    state.frame=frame ∧ state.poisson.preparation.prepared=frame.prepared := by
  unfold storedSourceGaugeFromPrepared at h
  rcases Option.map_eq_some_iff.mp h with ⟨result,hresult,rfl⟩
  exact ⟨rfl,(storedPoissonCoefficientPreparation_fields source frame _ result hresult).1⟩

/-- Original `materializeStoredGaugeUnitSampling_fields` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem materializeStoredGaugeUnitSampling_fields (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) (plan : StoredGaugeUnitSamplingPlan)
    (h : materializeStoredGaugeUnitSampling source frame tolerance=some plan) :
    plan.gauge.frame=frame ∧ plan.gauge.poisson.preparation.prepared=frame.prepared := by
  unfold materializeStoredGaugeUnitSampling at h
  rcases Option.map_eq_some_iff.mp h with ⟨state,hstate,rfl⟩
  exact storedSourceGaugeFromPrepared_fields source frame tolerance state hstate

/-- Original `materializeStoredGaugeUnitSampling_output` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem materializeStoredGaugeUnitSampling_output (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) :
    (materializeStoredGaugeUnitSampling source
      (storeReferenceFrame source prepared (referenceUnitCollar gap)) tolerance).map
        StoredGaugeUnitSamplingPlan.toPlan=
      materializeGaugeUnitSamplingFromGap source prepared gap tolerance := by
  unfold materializeStoredGaugeUnitSampling materializeGaugeUnitSamplingFromGap
  rw [← storedSourceGaugeFromPrepared_output source prepared gap tolerance]
  generalize hs : storedSourceGaugeFromPrepared source
    (storeReferenceFrame source prepared (referenceUnitCollar gap)) tolerance=out
  cases out with
  | none => rfl
  | some state =>
    simp only [Option.map_some]
    have hfields := storedSourceGaugeFromPrepared_fields source _ tolerance state hs
    have hstate : state=⟨storeReferenceFrame source prepared (referenceUnitCollar gap),state.poisson⟩ := by
      rw [← hfields.1]
    rw [hstate]
    exact congrArg some (materializeStoredGaugeUnitSamplingPlan_output source prepared gap _ hfields.2 tolerance)

/-- Data and hypotheses for Stored Gauge Artifact Parameters in the Spectral H1 construction. -/
structure StoredGaugeArtifactParameters where
  cutoff : ℕ
  mesh : ℕ
  sampleAccuracy : ℚ
  modeAccuracy : ℚ
  period : ℚ

/-- Definition of stored Gauge Artifact Parameters in the Spectral H1 construction. -/
def storedGaugeArtifactParameters (frame : StoredReferenceFrame) (tolerance : ℚ) : StoredGaugeArtifactParameters :=
  let N := finiteGaugeOutputCutoff frame.gaugeBounds[3] tolerance
  let accuracy := finiteGaugeCoefficientAccuracy N tolerance
  let M := finiteGaugeCoefficientMesh frame.gaugeBounds[1] N accuracy
  let sample := finiteGaugeSampleAccuracy accuracy
  let d := finiteGaugeModeAccuracy accuracy
  let ell := finiteGaugeModePeriodAccuracy N accuracy
  ⟨N,M,sample,d,fourierPeriodExecution ell⟩

/-- Definition of stored Gauge Artifact Execution in the Spectral H1 construction. -/
def storedGaugeArtifactExecution (value : (Fin 3 → ℚ) → Option (Quaternion ℚ))
    (p : StoredGaugeArtifactParameters) : Option RationalGaugeFourierArtifact :=
  (gaugeGridExecution (fun index => value (sourceMeanUnitPoint p.mesh index)) (sourceMeanGrid p.mesh)).map
    (fun data => ⟨(sourceFrequencyGrid p.cutoff).map (fun k =>
      (Vector.ofFn k,Vector.ofFn (rationalGaugeFourierCoefficientsOfData p.mesh p.period k p.modeAccuracy data)))⟩)

/-- One palette is built outside the complete final gauge grid. Every
physical point request and every nested phase-log node reads these seeds. -/
def seededGaugeArtifactExecution (source : RationalJetSource) (plan : StoredGaugeUnitSamplingPlan)
    (p : StoredGaugeArtifactParameters) : Option RationalGaugeFourierArtifact :=
  let palette := sourceSeedPalette source plan.gauge.frame
    (referencePhysicalValueAccuracy (gaugePhysicalValueAccuracy plan.tolerance))
  storedGaugeArtifactExecution (fun address => gaugePhysicalWithSeeds source plan.gauge palette
    (fun j => plan.period*rationalUnitWrap address j) plan.tolerance) p

/-- Original `seededGaugeArtifactExecution_correct` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem seededGaugeArtifactExecution_correct (source : RationalJetSource) (plan : StoredGaugeUnitSamplingPlan)
    (p : StoredGaugeArtifactParameters) :
    seededGaugeArtifactExecution source plan p=
      storedGaugeArtifactExecution (storedSourceGaugeUnitSampling source plan) p := by
  have hvalues :
      (fun address : Fin 3 → ℚ => gaugePhysicalWithSeeds source plan.gauge
        (storeReferenceSeedPalette source plan.gauge.frame
          (referencePhysicalValueAccuracy (gaugePhysicalValueAccuracy plan.tolerance)))
        (fun j => plan.period*rationalUnitWrap address j) plan.tolerance)=
      storedSourceGaugeUnitSampling source plan :=
    funext (fun address => gaugePhysicalWithSeeds_correct source plan.gauge
      (fun j => plan.period*rationalUnitWrap address j) plan.tolerance)
  simpa only [seededGaugeArtifactExecution,sourceSeedPalette_correct] using
    congrArg (fun value : (Fin 3 → ℚ) → Option (Quaternion ℚ) => storedGaugeArtifactExecution value p) hvalues

/-- One retained frame supplies all P/R bounds, the coefficient grid and the
complete gauge sampling grid. The final artifact is still source free. -/
def materializeStoredGaugeArtifact (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : Option RationalGaugeFourierArtifact := do
  let p := storedGaugeArtifactParameters frame tolerance
  let plan ← materializeStoredGaugeUnitSampling source frame p.sampleAccuracy
  seededGaugeArtifactExecution source plan p

/-- Definition of automatic Stored Gauge Artifact From Gap in the Spectral H1 construction. -/
def automaticStoredGaugeArtifactFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option RationalGaugeFourierArtifact := do
  let prepared ← cachedMeanPreparationRun source bounds
  let frame := storeReferenceFrame source prepared (referenceUnitCollar gap)
  materializeStoredGaugeArtifact source frame tolerance

/-- Original `storedGaugeArtifactExecution_output` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem storedGaugeArtifactExecution_output (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap : ℚ) (plan : StoredGaugeUnitSamplingPlan)
    (hframe : plan.gauge.frame=storeReferenceFrame source prepared (referenceUnitCollar gap))
    (hprepared : plan.gauge.poisson.preparation.prepared=prepared) (p : StoredGaugeArtifactParameters) :
    storedGaugeArtifactExecution (storedSourceGaugeUnitSampling source plan) p=
      storedGaugeArtifactExecution (sourceGaugeUnitSampling source gap plan.toPlan) p := by
  have he : storedSourceGaugeUnitSampling source plan=sourceGaugeUnitSampling source gap plan.toPlan := by
    funext address
    exact storedSourceGaugeUnitSampling_output source prepared gap plan hframe hprepared address
  rw [he]

/-- Original `materializeGaugeArtifact_old_execution` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
private theorem materializeGaugeArtifact_old_execution (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) :
    let p := storedGaugeArtifactParameters (storeReferenceFrame source prepared (referenceUnitCollar gap)) tolerance
    materializeGaugeFourierArtifactFromGap source prepared gap tolerance=
      (materializeGaugeUnitSamplingFromGap source prepared gap p.sampleAccuracy).bind
        (fun plan => storedGaugeArtifactExecution (sourceGaugeUnitSampling source gap plan) p) := by
  dsimp only
  unfold materializeGaugeFourierArtifactFromGap storedGaugeArtifactParameters
  have h1 : (storeReferenceFrame source prepared (referenceUnitCollar gap)).gaugeBounds[1]=
      cachedGaugeWordMajorant (referenceUnitCollar gap) prepared 1 :=
    storeReferenceFrame_gaugeBounds source prepared _ (1 : Fin 4)
  have h3 : (storeReferenceFrame source prepared (referenceUnitCollar gap)).gaugeBounds[3]=
      cachedGaugeWordMajorant (referenceUnitCollar gap) prepared 3 :=
    storeReferenceFrame_gaugeBounds source prepared _ (3 : Fin 4)
  rw [h1,h3]
  simp only [storedGaugeArtifactExecution,Option.map_eq_bind,Function.comp_def,
    Option.bind_eq_bind,Option.pure_def]

/-- Original `materializeStoredGaugeArtifact_output` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem materializeStoredGaugeArtifact_output (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) :
    materializeStoredGaugeArtifact source
      (storeReferenceFrame source prepared (referenceUnitCollar gap)) tolerance=
      materializeGaugeFourierArtifactFromGap source prepared gap tolerance := by
  let frame := storeReferenceFrame source prepared (referenceUnitCollar gap)
  let p := storedGaugeArtifactParameters frame tolerance
  unfold materializeStoredGaugeArtifact
  simp only [seededGaugeArtifactExecution_correct]
  rw [materializeGaugeArtifact_old_execution]
  change (materializeStoredGaugeUnitSampling source frame p.sampleAccuracy).bind
      (fun plan => storedGaugeArtifactExecution (storedSourceGaugeUnitSampling source plan) p)=
    (materializeGaugeUnitSamplingFromGap source prepared gap p.sampleAccuracy).bind
      (fun plan => storedGaugeArtifactExecution (sourceGaugeUnitSampling source gap plan) p)
  rw [← materializeStoredGaugeUnitSampling_output source prepared gap p.sampleAccuracy]
  generalize hs : materializeStoredGaugeUnitSampling source frame p.sampleAccuracy=out
  cases out with
  | none => rfl
  | some plan =>
    change storedGaugeArtifactExecution (storedSourceGaugeUnitSampling source plan) p=
      storedGaugeArtifactExecution (sourceGaugeUnitSampling source gap plan.toPlan) p
    have hfields := materializeStoredGaugeUnitSampling_fields source frame p.sampleAccuracy plan hs
    exact storedGaugeArtifactExecution_output source prepared gap plan hfields.1 hfields.2 p

/-- Original `automaticStoredGaugeArtifactFromGap_output` guarantee for the `StoredGaugeArtifact` construction; the complete source hypotheses are retained. -/
theorem automaticStoredGaugeArtifactFromGap_output (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) :
    automaticStoredGaugeArtifactFromGap source bounds gap tolerance=
      automaticGaugeFourierArtifactFromGap source bounds gap tolerance := by
  simp [automaticStoredGaugeArtifactFromGap,automaticGaugeFourierArtifactFromGap,
    materializeStoredGaugeArtifact_output]

end Qatlib.Concepts.EffectiveGauge.SpectralH1
