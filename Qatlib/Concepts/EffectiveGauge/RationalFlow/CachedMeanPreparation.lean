/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceFrameBounds

set_option backward.isDefEq.respectTransparency false

/-!
# The returned derivative cache drives the finite mean preparation

The bound program is evaluated once. The mean producer consumes the
returned first and second values directly and performs no second raw-bound
pass. This is the derivative-cache/mean part of frame preparation; the
reference chart, regularity recurrences and final gauge are separate.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Data and hypotheses for Cached Mean Preparation in the Rational Flow construction. -/
structure CachedMeanPreparation where
  derivativeBounds : SourceFrameBoundPacket
  boundRequests : List ℕ
  sector : SourceMeanSectorResult

/-- Definition of cached Mean Preparation Run in the Rational Flow construction. -/
def cachedMeanPreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) :
    Option CachedMeanPreparation := do
  let (packet,labels) ← sourceFrameBoundRun bounds
  let sector ← sourceMeanSectorExecution source (packet 1) (packet 2)
  pure ⟨packet,labels,sector⟩

noncomputable section
open Set
open scoped ContDiff

/-- Same finite run, same stored cache, and same stored physical intervals
and sector. The mean's exact reference uses those stored effective bounds. -/
theorem cachedMeanPreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedMeanPreparationRun source bounds=some result ∧
      result.boundRequests.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ result.boundRequests, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (r : Fin 10) (w : List (Fin 3)), w.length=r.val → ∀ x, InFundamentalCube x →
        ‖spatialWordPartial v w x‖ ≤ (result.derivativeBounds r : ℝ)) ∧
      (∀ (r : Fin 10) (w : List (Fin 3)), w.length=r.val → ∀ u, InUnitCube u →
        ‖spatialWordPartial (unitCoordinateSpin v) w u‖ ≤
          (sourceFrameUnitBound result.derivativeBounds r : ℝ)) ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
          (result.derivativeBounds 1) (result.derivativeBounds 2) eta) x j)) result.sector := by
  have hs1 := OriginalAllJetAccurate.first v source hs
  have hb12 := OriginalPositiveJetBounds.first_second v hv bounds hb
  have hb1 := OriginalPositiveJetBounds.nonneg v hv bounds hb 1 (by decide)
  have hb2 := OriginalPositiveJetBounds.nonneg v hv bounds hb 2 (by decide)
  obtain ⟨sector,hsector,hcert⟩ := sourceMeanBoundsSectorExecution_correct v hv hu hp source hs1
    bounds hb1 hb2 hb12 eta he B hB mu hm hg hoff hmargin
  have hcached : sourceMeanSectorExecution source (sourceFrameBoundExpected bounds 1)
      (sourceFrameBoundExpected bounds 2)=some sector := by
    rw [sourceFrameBoundExpected_first,sourceFrameBoundExpected_second,
      ← sourceMeanBoundsSectorExecution_effective_eq]
    exact hsector
  refine ⟨⟨sourceFrameBoundExpected bounds,
    sourceFrameBoundLabels (sourceMeanCompressedBound (bounds 1)),sector⟩,?_,
    sourceFrameBoundLabels_length _,sourceFrameBoundLabels_domain _,?_,?_,?_⟩
  · rw [cachedMeanPreparationRun,sourceFrameBoundRun_eq]
    change (sourceMeanSectorExecution source (sourceFrameBoundExpected bounds 1)
      (sourceFrameBoundExpected bounds 2)).bind (fun s => some
        (⟨sourceFrameBoundExpected bounds,sourceFrameBoundLabels (sourceMeanCompressedBound (bounds 1)),s⟩ : CachedMeanPreparation))=_
    rw [hcached]
    rfl
  · exact sourceFrameBoundExpected_word v hv hu hp bounds hb
  · exact sourceFrameBoundExpected_unit_word v hv hu hp bounds hb
  · simpa only [sourceFrameBoundExpected_first,sourceFrameBoundExpected_second] using hcert

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
