/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceSeedPalette

set_option backward.isDefEq.respectTransparency false

/-!
# Seed Palette Execution

Rational Flow constructions for Effective Gauge.
Defines `ChargedOriginalJetSource`, `ChargedFrameSeed`, `ReferenceSeedExecution`.
Proves `chargedFrameSeed_value`, `referenceSeedPaletteExecution_value`, `sourceSeedPalette_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Abbreviation for Charged Original Jet Source in the Rational Flow construction. -/
abbrev ChargedOriginalJetSource := OriginalJetQuery → (Fin 3 → ℚ) × ℕ

/-- Data and hypotheses for Charged Frame Seed in the Rational Flow construction. -/
structure ChargedFrameSeed where
  value : Quaternion ℚ
  requests : List OriginalJetQuery
  sourceCharge : ℕ

/-- Data and hypotheses for Reference Seed Execution in the Rational Flow construction. -/
structure ReferenceSeedExecution where
  palette : ReferenceSeedPalette
  requests : List OriginalJetQuery
  sourceCharge : ℕ

/-- Definition of frame Seed Requests in the Rational Flow construction. -/
def frameSeedRequests (frame : StoredReferenceFrame) (tolerance : ℚ) : List OriginalJetQuery :=
  let label := rescaleSourceQuery (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2)
    (0,seedValuePrecision tolerance)
  [((label.1,0),label.2),((label.1,firstJetIndex 0),label.2)]

/-- The charged legacy pair has two actual original jet requests. Its value
is the same seed used by the rational reference; fees do not affect branches. -/
def chargedFrameSeed (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : ChargedFrameSeed :=
  let b := seedValuePrecision tolerance
  let label := rescaleSourceQuery (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2) (0,b)
  let value := source ((label.1,0),label.2)
  let derivative := source ((label.1,firstJetIndex 0),label.2)
  ⟨rationalChartSeed frame.chart value.1 b,
    [((label.1,0),label.2),((label.1,firstJetIndex 0),label.2)],value.2+derivative.2⟩

/-- Definition of reference Seed Requests in the Rational Flow construction. -/
def referenceSeedRequests (frame : StoredReferenceFrame) (tolerance : ℚ) : List OriginalJetQuery :=
  let b := phaseLogPrecision (tolerance/32)
  let e := (2^b : ℚ)⁻¹
  frameSeedRequests frame (tolerance/8)++frameSeedRequests frame (tolerance/16)++
    frameSeedRequests frame ((e/8)/8)++frameSeedRequests frame (e/8)

/-- Actual palette construction and its source-request ledger share the same
four returned seed records. Arithmetic costs are a separate obligation. -/
def referenceSeedPaletteExecution (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : ReferenceSeedExecution :=
  let b := phaseLogPrecision (tolerance/32)
  let e := (2^b : ℚ)⁻¹
  let line := chargedFrameSeed source frame (tolerance/8)
  let transition := chargedFrameSeed source frame (tolerance/16)
  let logLine := chargedFrameSeed source frame ((e/8)/8)
  let logBase := chargedFrameSeed source frame (e/8)
  ⟨⟨tolerance,b,line.value,transition.value,logLine.value,logBase.value⟩,
    line.requests++transition.requests++logLine.requests++logBase.requests,
    line.sourceCharge+transition.sourceCharge+logLine.sourceCharge+logBase.sourceCharge⟩

/-- Definition of source Seed Palette in the Rational Flow construction. -/
def sourceSeedPalette (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : ReferenceSeedPalette :=
  (referenceSeedPaletteExecution (fun query => (source query,0)) frame tolerance).palette

/-- Original `chargedFrameSeed_value` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
theorem chargedFrameSeed_value (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) :
    (chargedFrameSeed source frame tolerance).value=
      originSeedOnChart (rescaledSpinSamples (originalFirstJetPair (fun q => (source q).1) 0)
        (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2)) frame.chart tolerance := rfl

/-- Original `referenceSeedPaletteExecution_value` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
theorem referenceSeedPaletteExecution_value (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) :
    (referenceSeedPaletteExecution source frame tolerance).palette=
      storeReferenceSeedPalette (fun q => (source q).1) frame tolerance := by
  simp only [referenceSeedPaletteExecution,chargedFrameSeed_value,storeReferenceSeedPalette]

/-- Original `sourceSeedPalette_correct` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
theorem sourceSeedPalette_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) : sourceSeedPalette source frame tolerance=storeReferenceSeedPalette source frame tolerance :=
  referenceSeedPaletteExecution_value (fun query => (source query,0)) frame tolerance

/-- Original `referenceSeedPaletteExecution_requests` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
theorem referenceSeedPaletteExecution_requests (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) :
    (referenceSeedPaletteExecution source frame tolerance).requests=referenceSeedRequests frame tolerance := rfl

/-- Original `referenceSeedRequests_length` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
theorem referenceSeedRequests_length (frame : StoredReferenceFrame) (tolerance : ℚ) :
    (referenceSeedRequests frame tolerance).length=8 := by
  simp [referenceSeedRequests,frameSeedRequests]

/-- Original `referenceSeedPaletteExecution_charge` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
theorem referenceSeedPaletteExecution_charge (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) :
    (referenceSeedPaletteExecution source frame tolerance).sourceCharge=
      ((referenceSeedRequests frame tolerance).map (fun query => (source query).2)).sum := by
  simp [referenceSeedPaletteExecution,referenceSeedRequests,chargedFrameSeed,frameSeedRequests,Nat.add_assoc]

/-- Original `sourceRequestSum_le` guarantee for the `SeedPaletteExecution` construction; the complete source hypotheses are retained. -/
private theorem sourceRequestSum_le (source : ChargedOriginalJetSource) (labels : List OriginalJetQuery) (T : ℕ)
    (hT : ∀ query∈labels, (source query).2 ≤ T) :
    (labels.map (fun query => (source query).2)).sum ≤ labels.length*T := by
  induction labels with
  | nil => simp
  | cons query rest ih =>
    have hq := hT query (by simp)
    have hr := ih (fun q hq => hT q (by simp only [List.mem_cons]; exact Or.inr hq))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul] at *
    omega

/-- Source fees only: all eight original queries are charged even when a
branch uses fewer seeds, and repeated precision labels are not deduplicated. -/
theorem referenceSeedPaletteExecution_charge_le (source : ChargedOriginalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) (T : ℕ)
    (hT : ∀ query∈referenceSeedRequests frame tolerance, (source query).2 ≤ T) :
    (referenceSeedPaletteExecution source frame tolerance).sourceCharge ≤ 8*T := by
  rw [referenceSeedPaletteExecution_charge,← referenceSeedRequests_length frame tolerance]
  exact sourceRequestSum_le source _ T hT

end Qatlib.Concepts.EffectiveGauge.RationalFlow
