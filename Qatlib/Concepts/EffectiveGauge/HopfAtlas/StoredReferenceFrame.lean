/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientGridExecution
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeWordBound

set_option backward.isDefEq.respectTransparency false

/-!
# Stored Reference Frame

Hopf Atlas constructions for Effective Gauge.
Defines `StoredReferenceFrame`, `StoredReferenceFrame.prepared`, `storeReferenceFrame`.
Proves `storeReferenceFrame_prepared`, `storedReferenceValue_store`, `storedConnectionSampling_store`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Finite preparation data retained across all reference and grid requests.
No source evaluator or spatial value function is stored in this cache. -/
structure StoredReferenceFrame where
  regularity : CachedReferencePreparation
  collar : ℚ
  chart : SeedChart
  gaugeBounds : Vector ℚ 4

/-- Definition of prepared in the Hopf Atlas construction. -/
def StoredReferenceFrame.prepared (frame : StoredReferenceFrame) : CachedMeanPreparation :=
  frame.regularity.prepared

/-- Definition of store Reference Frame in the Hopf Atlas construction. -/
def storeReferenceFrame (source : RationalJetSource) (prepared : CachedMeanPreparation) (eta : ℚ) :
    StoredReferenceFrame :=
  let regularity := materializeReferencePreparation eta prepared
  let chart := chosenOriginChart (rescaledSpinSamples (originalFirstJetPair source 0)
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2))
  let gaugeBounds := Vector.ofFn (fun r : Fin 4 =>
    gaugeWordMajorant (storedPhaseValue regularity.corrected.correctedBounds)
      regularity.connectionBounds[6] (selectedSectorWinding prepared.sector) r.val)
  ⟨regularity,eta,chart,gaugeBounds⟩

/-- Definition of stored Reference Value in the Hopf Atlas construction. -/
def storedReferenceValue (source : RationalJetSource) (frame : StoredReferenceFrame)
    (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  sourceReferenceValueOnChart (originalFirstJetPair source 0)
    (frame.prepared.derivativeBounds 1) (frame.prepared.derivativeBounds 2)
    frame.chart frame.collar a tolerance

/-- Definition of stored Connection Sampling in the Hopf Atlas construction. -/
def storedConnectionSampling (source : RationalJetSource) (frame : StoredReferenceFrame)
    (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Fin 3 → ℚ) :=
  connectionSampleExecution (storedReferenceValue source frame)
    frame.regularity.corrected.correctedBounds[1] frame.regularity.corrected.correctedBounds[2] a tolerance

/-- Definition of stored Connection Grid in the Hopf Atlas construction. -/
def storedConnectionGrid (source : RationalJetSource) (frame : StoredReferenceFrame)
    (M : ℕ) (tolerance : ℚ) : Option RationalConnectionGridData :=
  connectionGridExecution (fun index => storedConnectionSampling source frame (sourceMeanUnitPoint M index) tolerance)
    (sourceMeanGrid M)

/-- Original `storeReferenceFrame_prepared` guarantee for the `StoredReferenceFrame` construction; the complete source hypotheses are retained. -/
theorem storeReferenceFrame_prepared (source : RationalJetSource) (prepared : CachedMeanPreparation) (eta : ℚ) :
    (storeReferenceFrame source prepared eta).prepared=prepared := rfl

/-- Only an output identity for correctness transport. Re-evaluating the RHS
would repeat preparation; it is not an execution or fee prescription. -/
theorem storedReferenceValue_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    storedReferenceValue source (storeReferenceFrame source prepared eta) a tolerance=
      preparedReferenceValueProgram source prepared eta a tolerance := rfl

/-- Original `storedConnectionSampling_store` guarantee for the `StoredReferenceFrame` construction; the complete source hypotheses are retained. -/
theorem storedConnectionSampling_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    storedConnectionSampling source (storeReferenceFrame source prepared eta) a tolerance=
      sourceConnectionSampling source prepared eta a tolerance := rfl

/-- Original `storedConnectionGrid_store` guarantee for the `StoredReferenceFrame` construction; the complete source hypotheses are retained. -/
theorem storedConnectionGrid_store (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (M : ℕ) (tolerance : ℚ) :
    storedConnectionGrid source (storeReferenceFrame source prepared eta) M tolerance=
      connectionGridExecution
        (fun index => sourceConnectionSampling source prepared eta (sourceMeanUnitPoint M index) tolerance)
        (sourceMeanGrid M) := rfl

/-- Original `storeReferenceFrame_gaugeBounds` guarantee for the `StoredReferenceFrame` construction; the complete source hypotheses are retained. -/
theorem storeReferenceFrame_gaugeBounds (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (r : Fin 4) :
    (storeReferenceFrame source prepared eta).gaugeBounds[r.val]=cachedGaugeWordMajorant eta prepared r.val := by
  simp only [storeReferenceFrame,Vector.getElem_ofFn]
  rfl

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- Original `storedConnectionSampling_error` guarantee for the `StoredReferenceFrame` construction; the complete source hypotheses are retained. -/
theorem storedConnectionSampling_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ b, OnCubeBoundary b → mu ≤ ‖z-b‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (a : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ out, storedConnectionSampling source (storeReferenceFrame source prepared eta) a tolerance=some out ∧ ∀ j,
      |(out j : ℝ)-physicalPeriod*connection (preparedPeriodicReference v hv hu source hs prepared eta)
        (physicalPeriod • rationalSpatialPoint a) j| ≤ (tolerance : ℝ)/2 := by
  rw [storedConnectionSampling_store]
  exact sourceConnectionSampling_error v hv hu hp source hs bounds hb prepared hrun eta he he1 B hB mu hm hg hoff hmargin a tolerance ht

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
