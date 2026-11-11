/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.OriginalSeedAtlas
import Qatlib.Concepts.EffectiveGauge.SpectralH1.TransferredGaugeArtifact
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SeedTransferBudget
import Qatlib.Concepts.EffectiveGauge.SpectralH1.StoredGaugeArtifactH1

set_option backward.isDefEq.respectTransparency false

/-!
# Seed Transferred Producer

Spectral H1 constructions for Effective Gauge.
Defines `materializeSeedTransferredArtifact`, `automaticSeedTransferredArtifact`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- A finite rotated artifact with one retained preparation. The requested
alternate chart is tested by the actual finite source answers. -/
def materializeSeedTransferredArtifact (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap : ℚ) (toChart : SeedChart) (tolerance : ℚ) : Option TransferredGaugeArtifact := do
  let frame := storeReferenceFrame source prepared (referenceUnitCollar gap)
  let delta := seedTransferArtifactAccuracy frame.gaugeBounds[1] tolerance
  let base ← materializeStoredGaugeArtifact source frame (tolerance/8)
  let transition ← originalSeedTransitionRun source (prepared.derivativeBounds 1)
    (prepared.derivativeBounds 2) frame.chart toChart (2*delta)
  return ⟨base,transition⟩

/-- Definition of automatic Seed Transferred Artifact in the Spectral H1 construction. -/
def automaticSeedTransferredArtifact (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap : ℚ) (toChart : SeedChart) (tolerance : ℚ) : Option TransferredGaugeArtifact := do
  let prepared ← cachedMeanPreparationRun source bounds
  materializeSeedTransferredArtifact source prepared gap toChart tolerance

end Qatlib.Concepts.EffectiveGauge.SpectralH1
