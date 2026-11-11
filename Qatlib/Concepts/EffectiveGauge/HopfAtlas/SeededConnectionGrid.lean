/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceSeedPalette
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SeedPaletteExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Seeded Connection Grid

Hopf Atlas constructions for Effective Gauge.
Defines `connectionSampleWithSeeds`, `connectionGridWithSeeds`.
Proves `connectionSampleWithSeeds_correct`, `connectionGridWithSeeds_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of connection Sample With Seeds in the Hopf Atlas construction. -/
def connectionSampleWithSeeds (source : RationalJetSource) (frame : StoredReferenceFrame)
    (palette : ReferenceSeedPalette) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Fin 3 → ℚ) :=
  connectionSampleExecution (fun address _ => referenceValueWithSeeds source frame palette address)
    frame.regularity.corrected.correctedBounds[1] frame.regularity.corrected.correctedBounds[2] a tolerance

/-- Definition of connection Grid With Seeds in the Hopf Atlas construction. -/
def connectionGridWithSeeds (source : RationalJetSource) (frame : StoredReferenceFrame)
    (M : ℕ) (tolerance : ℚ) : Option RationalConnectionGridData :=
  let gamma := connectionSampleAccuracy frame.regularity.corrected.correctedBounds[1]
    frame.regularity.corrected.correctedBounds[2] tolerance
  let palette := sourceSeedPalette source frame gamma
  connectionGridExecution
    (fun index => connectionSampleWithSeeds source frame palette (sourceMeanUnitPoint M index) tolerance)
    (sourceMeanGrid M)

/-- Original `connectionSampleWithSeeds_correct` guarantee for the `SeededConnectionGrid` construction; the complete source hypotheses are retained. -/
theorem connectionSampleWithSeeds_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (a : Fin 3 → ℚ) (tolerance : ℚ) :
    connectionSampleWithSeeds source frame
      (storeReferenceSeedPalette source frame
        (connectionSampleAccuracy frame.regularity.corrected.correctedBounds[1]
          frame.regularity.corrected.correctedBounds[2] tolerance)) a tolerance=
      storedConnectionSampling source frame a tolerance := by
  simp only [connectionSampleWithSeeds,storedConnectionSampling,connectionSampleExecution,
    referenceValueWithSeeds_correct]

/-- Original `connectionGridWithSeeds_correct` guarantee for the `SeededConnectionGrid` construction; the complete source hypotheses are retained. -/
theorem connectionGridWithSeeds_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (M : ℕ) (tolerance : ℚ) :
    connectionGridWithSeeds source frame M tolerance=storedConnectionGrid source frame M tolerance := by
  let gamma := connectionSampleAccuracy frame.regularity.corrected.correctedBounds[1]
    frame.regularity.corrected.correctedBounds[2] tolerance
  have hsample :
      (fun index : SourceMeanIndex => connectionSampleWithSeeds source frame
        (storeReferenceSeedPalette source frame gamma) (sourceMeanUnitPoint M index) tolerance)=
      (fun index : SourceMeanIndex => storedConnectionSampling source frame (sourceMeanUnitPoint M index) tolerance) :=
    funext (fun index => connectionSampleWithSeeds_correct source frame (sourceMeanUnitPoint M index) tolerance)
  simpa only [connectionGridWithSeeds,storedConnectionGrid,sourceSeedPalette_correct] using
    congrArg (fun sample : SourceMeanIndex → Option (Fin 3 → ℚ) =>
      connectionGridExecution sample (sourceMeanGrid M)) hsample

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
