/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.StoredReferenceFrame

set_option backward.isDefEq.respectTransparency false

/-!
# Reference Seed Palette

Hopf Atlas constructions for Effective Gauge.
Defines `ReferenceSeedPalette`, `storeReferenceSeedPalette`, `referenceLineWithSeed`.
Proves `referenceLineWithSeed_correct`, `terminalCircleWithSeeds_correct`, `rationalPhaseLog_same_precision`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Four finite fine seed values suffice for every branch and every sample
of a reference request at one fixed tolerance. No seed function is retained. -/
structure ReferenceSeedPalette where
  tolerance : ℚ
  logPrecision : ℕ
  line : Quaternion ℚ
  transition : Quaternion ℚ
  logLine : Quaternion ℚ
  logBase : Quaternion ℚ

/-- Definition of store Reference Seed Palette in the Hopf Atlas construction. -/
def storeReferenceSeedPalette (source : RationalJetSource) (frame : StoredReferenceFrame) (tolerance : ℚ) :
    ReferenceSeedPalette :=
  let samples := rescaledSpinSamples (originalFirstJetPair source 0)
    (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2)
  let b := phaseLogPrecision (tolerance/32)
  let e := (2^b : ℚ)⁻¹
  let line := originSeedOnChart samples frame.chart (tolerance/8)
  let transition := originSeedOnChart samples frame.chart (tolerance/16)
  let logLine := originSeedOnChart samples frame.chart ((e/8)/8)
  let logBase := originSeedOnChart samples frame.chart (e/8)
  ⟨tolerance,b,line,transition,logLine,logBase⟩

/-- Definition of reference Line With Seed in the Hopf Atlas construction. -/
def referenceLineWithSeed (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (seed : Quaternion ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Quaternion ℚ :=
  if m1=0 then seed else seed*rationalCayleyValue
    (physicalCayleyExecution (rescaledSpinSamples source m1 m2) (a 1) (a 2) (a 0)
      (7*m1) (49*m2) (tolerance/4))

/-- Definition of terminal Circle With Seeds in the Hopf Atlas construction. -/
def terminalCircleWithSeeds (source : RationalJetSource) (frame : StoredReferenceFrame)
    (palette : ReferenceSeedPalette) (z : ℚ) (label : ℚ × ℕ) : RationalCircleSample :=
  let e := (2^label.2 : ℚ)⁻¹
  let q := referenceLineWithSeed (originalFirstJetPair source 0)
    (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2)
    palette.logLine ![1,label.1,z] (e/8)
  let ratio := q*star palette.logBase
  (ratio.re,ratio.imI)

/-- Original `referenceLineWithSeed_correct` guarantee for the `ReferenceSeedPalette` construction; the complete source hypotheses are retained. -/
theorem referenceLineWithSeed_correct (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (chart : SeedChart) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    referenceLineWithSeed source m1 m2
      (originSeedOnChart (rescaledSpinSamples source m1 m2) chart (tolerance/8)) a tolerance=
      rescaledLineOnChart source m1 m2 chart a tolerance := rfl

/-- Original `terminalCircleWithSeeds_correct` guarantee for the `ReferenceSeedPalette` construction; the complete source hypotheses are retained. -/
theorem terminalCircleWithSeeds_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance z x : ℚ) :
    terminalCircleWithSeeds source frame (storeReferenceSeedPalette source frame tolerance) z
      (x,phaseLogPrecision (tolerance/32))=
    terminalCircleSamplesOnChart (originalFirstJetPair source 0)
      (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2) z frame.chart
      (x,phaseLogPrecision (tolerance/32)) := rfl

/-- Only the precision actually used by the finite phase-log program is
required, rather than equality of arbitrary callback functions. -/
theorem rationalPhaseLog_same_precision (f g : ℚ × ℕ → RationalCircleSample) (endpoint bound tolerance : ℚ)
    (h : ∀ x, f (x,phaseLogPrecision tolerance)=g (x,phaseLogPrecision tolerance)) :
    rationalPhaseLog f endpoint bound tolerance=rationalPhaseLog g endpoint bound tolerance := by
  have hs : phaseLogSamples f endpoint (phaseLogSteps endpoint bound) (phaseLogPrecision tolerance)=
      phaseLogSamples g endpoint (phaseLogSteps endpoint bound) (phaseLogPrecision tolerance) := by
    funext j
    unfold phaseLogSamples
    split_ifs
    · rfl
    · exact h _
  simp only [rationalPhaseLog,hs]

/-- Definition of reference Angle With Seeds in the Hopf Atlas construction. -/
def referenceAngleWithSeeds (source : RationalJetSource) (frame : StoredReferenceFrame)
    (palette : ReferenceSeedPalette) (x y z : ℚ) : Option RationalReferenceAngleResult :=
  let Q := ((7*frame.prepared.derivativeBounds 1)^2+49*frame.prepared.derivativeBounds 2)/2
  (rationalPhaseLog (terminalCircleWithSeeds source frame palette z) y Q (palette.tolerance/32)).map (fun log =>
    let rho := rationalSmoothStep ((x-(1-frame.collar/2))/(frame.collar/4)) (palette.tolerance/(64*(Q+1)))
    ⟨(1-rho.value)*log.value,log.errorBound+rho.error*Q,log,rho⟩)

/-- Definition of reference Value With Seeds in the Hopf Atlas construction. -/
def referenceValueWithSeeds (source : RationalJetSource) (frame : StoredReferenceFrame)
    (palette : ReferenceSeedPalette) (a : Fin 3 → ℚ) : Option (Quaternion ℚ) :=
  if frame.prepared.derivativeBounds 1=0 then some palette.line
  else if referenceValueBoundary frame.collar a then some palette.line
  else if a 0 ≤ 1-frame.collar/2 then some (referenceLineWithSeed (originalFirstJetPair source 0)
    (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2) palette.line a palette.tolerance)
  else (referenceAngleWithSeeds source frame palette (a 0) (a 1) (a 2)).map
    (referenceAngleValue palette.transition palette.tolerance)

/-- Original `referenceAngleWithSeeds_correct` guarantee for the `ReferenceSeedPalette` construction; the complete source hypotheses are retained. -/
theorem referenceAngleWithSeeds_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance x y z : ℚ) :
    referenceAngleWithSeeds source frame (storeReferenceSeedPalette source frame tolerance) x y z=
      sourceReferenceAngleOnChart (originalFirstJetPair source 0)
        (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2)
        frame.chart frame.collar x y z tolerance := by
  unfold referenceAngleWithSeeds sourceReferenceAngleOnChart
  have htol : (storeReferenceSeedPalette source frame tolerance).tolerance=tolerance := rfl
  simp only [htol]
  rw [rationalPhaseLog_same_precision _ _ y _ (tolerance/32)
    (fun x => terminalCircleWithSeeds_correct source frame tolerance z x)]

/-- Original `referenceValueWithSeeds_correct` guarantee for the `ReferenceSeedPalette` construction; the complete source hypotheses are retained. -/
theorem referenceValueWithSeeds_correct (source : RationalJetSource) (frame : StoredReferenceFrame)
    (tolerance : ℚ) (a : Fin 3 → ℚ) :
    referenceValueWithSeeds source frame (storeReferenceSeedPalette source frame tolerance) a=
      storedReferenceValue source frame a tolerance := by
  unfold referenceValueWithSeeds storedReferenceValue sourceReferenceValueOnChart
  split_ifs
  · rfl
  · rfl
  · exact congrArg some (referenceLineWithSeed_correct _ _ _ _ a tolerance)
  · rw [referenceAngleWithSeeds_correct]
    rfl

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
