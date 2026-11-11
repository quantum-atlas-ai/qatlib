/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.StoredPoissonPreparation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PreparedSourceGauge

set_option backward.isDefEq.respectTransparency false

/-!
# Stored Gauge State

Spectral H1 constructions for Effective Gauge.
Defines `StoredGaugeState`, `storedReferencePhysicalValue`, `storedSourceGaugeFromPrepared`.
Proves `storedReferencePhysicalValue_store`, `storedSourceGaugeFromPrepared_output`, `storedAutomaticSourceGaugeFromGap_output`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Data and hypotheses for Stored Gauge State in the Spectral H1 construction. -/
structure StoredGaugeState where
  frame : StoredReferenceFrame
  poisson : GeneralPoissonValueState

/-- Definition of stored Reference Physical Value in the Spectral H1 construction. -/
def storedReferencePhysicalValue (source : RationalJetSource) (frame : StoredReferenceFrame)
    (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  referencePhysicalValueExecution (storedReferenceValue source frame)
    frame.regularity.corrected.correctedBounds[1] X tolerance

/-- Definition of stored Source Gauge From Prepared in the Spectral H1 construction. -/
def storedSourceGaugeFromPrepared (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : Option StoredGaugeState :=
  (storedPoissonCoefficientPreparation source frame
    (physicalPoissonValueTolerance (gaugePhysicalValueAccuracy tolerance))).map
      (fun result => ⟨frame,materializeGeneralPoissonValueState result⟩)

/-- Definition of stored Automatic Source Gauge From Gap in the Spectral H1 construction. -/
def storedAutomaticSourceGaugeFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option StoredGaugeState :=
  (storedAutomaticPoissonCoefficientsFromGap source bounds gap
    (physicalPoissonValueTolerance (gaugePhysicalValueAccuracy tolerance))).map
      (fun result => ⟨result.1,materializeGeneralPoissonValueState result.2⟩)

/-- Definition of stored Source Gauge Physical Value in the Spectral H1 construction. -/
def storedSourceGaugePhysicalValue (source : RationalJetSource) (state : StoredGaugeState)
    (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) := do
  let gamma := gaugePhysicalValueAccuracy tolerance
  let reference ← storedReferencePhysicalValue source state.frame X gamma
  let angle := rationalWindingAngle (selectedSectorWinding state.poisson.preparation.prepared.sector) X+
    generalPoissonPhysicalPhaseValue state.poisson X gamma
  return rationalCircleQuaternion (rationalCis angle gamma).value*reference

/-- Original `storedReferencePhysicalValue_store` guarantee for the `StoredGaugeState` construction; the complete source hypotheses are retained. -/
theorem storedReferencePhysicalValue_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (X : Fin 3 → ℚ) (tolerance : ℚ) :
    storedReferencePhysicalValue source (storeReferenceFrame source prepared eta) X tolerance=
      sourceReferencePhysicalValue source prepared eta X tolerance := rfl

/-- Original `storedSourceGaugeFromPrepared_output` guarantee for the `StoredGaugeState` construction; the complete source hypotheses are retained. -/
theorem storedSourceGaugeFromPrepared_output (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) :
    (storedSourceGaugeFromPrepared source
      (storeReferenceFrame source prepared (referenceUnitCollar gap)) tolerance).map StoredGaugeState.poisson=
      materializeSourceGaugeFromGap source prepared gap tolerance := by
  simp [storedSourceGaugeFromPrepared,materializeSourceGaugeFromGap,
    storedPoissonCoefficientPreparation_store,Option.map_map,Function.comp_def]

/-- Original `storedAutomaticSourceGaugeFromGap_output` guarantee for the `StoredGaugeState` construction; the complete source hypotheses are retained. -/
theorem storedAutomaticSourceGaugeFromGap_output (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) :
    (storedAutomaticSourceGaugeFromGap source bounds gap tolerance).map StoredGaugeState.poisson=
      automaticSourceGaugeFromGap source bounds gap tolerance := by
  have h := congrArg (Option.map materializeGeneralPoissonValueState)
    (storedAutomaticPoissonCoefficientsFromGap_output source bounds gap
      (physicalPoissonValueTolerance (gaugePhysicalValueAccuracy tolerance)))
  simpa [storedAutomaticSourceGaugeFromGap,automaticSourceGaugeFromGap,automaticPhysicalPoissonFromGap,
    automaticGeneralPoissonFromGap,Option.map_map,Function.comp_def] using h

/-- Original `storedSourceGaugePhysicalValue_store` guarantee for the `StoredGaugeState` construction; the complete source hypotheses are retained. -/
theorem storedSourceGaugePhysicalValue_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap : ℚ) (r : GeneralPoissonValueState) (hprepared : r.preparation.prepared=prepared)
    (X : Fin 3 → ℚ) (tolerance : ℚ) :
    storedSourceGaugePhysicalValue source
      ⟨storeReferenceFrame source prepared (referenceUnitCollar gap),r⟩ X tolerance=
      sourceGaugePhysicalValue source gap r X tolerance := by
  simp only [storedSourceGaugePhysicalValue,storedReferencePhysicalValue_store,
    sourceGaugePhysicalValue,hprepared]

end Qatlib.Concepts.EffectiveGauge.SpectralH1
