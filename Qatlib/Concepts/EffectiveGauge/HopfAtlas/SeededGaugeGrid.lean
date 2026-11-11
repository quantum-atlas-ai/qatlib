/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.StoredGaugeState
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceSeedPalette
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SeedPaletteExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Seeded Gauge Grid

Hopf Atlas constructions for Effective Gauge.
Defines `referencePhysicalWithSeeds`, `gaugePhysicalWithSeeds`, `gaugePhysicalWithSeedCache`.
Proves `referencePhysicalWithSeeds_correct`, `gaugePhysicalWithSeeds_correct`, `gaugePhysicalWithSeedCache_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of reference Physical With Seeds in the Hopf Atlas construction. -/
def referencePhysicalWithSeeds (source : RationalJetSource) (frame : StoredReferenceFrame)
    (palette : ReferenceSeedPalette) (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  let ell := rationalPhysicalAddressAccuracy frame.regularity.corrected.correctedBounds[1] X tolerance
  referenceValueWithSeeds source frame palette (rationalUnitWrap (rationalPhysicalPoissonAddress X ell))

/-- Definition of gauge Physical With Seeds in the Hopf Atlas construction. -/
def gaugePhysicalWithSeeds (source : RationalJetSource) (state : StoredGaugeState)
    (palette : ReferenceSeedPalette) (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) := do
  let gamma := gaugePhysicalValueAccuracy tolerance
  let reference ← referencePhysicalWithSeeds source state.frame palette X gamma
  let angle := rationalWindingAngle (selectedSectorWinding state.poisson.preparation.prepared.sector) X+
    generalPoissonPhysicalPhaseValue state.poisson X gamma
  return rationalCircleQuaternion (rationalCis angle gamma).value*reference

/-- Independent physical requests build four finite seeds once for their
whole phase grid, rather than once per phase-log sample. -/
def gaugePhysicalWithSeedCache (source : RationalJetSource) (state : StoredGaugeState)
    (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  let palette := sourceSeedPalette source state.frame
    (referencePhysicalValueAccuracy (gaugePhysicalValueAccuracy tolerance))
  gaugePhysicalWithSeeds source state palette X tolerance

/-- Original `referencePhysicalWithSeeds_correct` guarantee for the `SeededGaugeGrid` construction; the complete source hypotheses are retained. -/
theorem referencePhysicalWithSeeds_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (X : Fin 3 → ℚ) (tolerance : ℚ) :
    referencePhysicalWithSeeds source frame
      (storeReferenceSeedPalette source frame (referencePhysicalValueAccuracy tolerance)) X tolerance=
      storedReferencePhysicalValue source frame X tolerance := by
  simp only [referencePhysicalWithSeeds,storedReferencePhysicalValue,referencePhysicalValueExecution,
    referenceValueWithSeeds_correct]

/-- Original `gaugePhysicalWithSeeds_correct` guarantee for the `SeededGaugeGrid` construction; the complete source hypotheses are retained. -/
theorem gaugePhysicalWithSeeds_correct (source : RationalJetSource) (state : StoredGaugeState)
    (X : Fin 3 → ℚ) (tolerance : ℚ) :
    gaugePhysicalWithSeeds source state
      (storeReferenceSeedPalette source state.frame
        (referencePhysicalValueAccuracy (gaugePhysicalValueAccuracy tolerance))) X tolerance=
      storedSourceGaugePhysicalValue source state X tolerance := by
  unfold gaugePhysicalWithSeeds storedSourceGaugePhysicalValue
  dsimp only
  rw [referencePhysicalWithSeeds_correct]

/-- Original `gaugePhysicalWithSeedCache_correct` guarantee for the `SeededGaugeGrid` construction; the complete source hypotheses are retained. -/
theorem gaugePhysicalWithSeedCache_correct (source : RationalJetSource) (state : StoredGaugeState)
    (X : Fin 3 → ℚ) (tolerance : ℚ) :
    gaugePhysicalWithSeedCache source state X tolerance=storedSourceGaugePhysicalValue source state X tolerance :=
  by
    simpa only [gaugePhysicalWithSeedCache,sourceSeedPalette_correct] using
      gaugePhysicalWithSeeds_correct source state X tolerance

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
