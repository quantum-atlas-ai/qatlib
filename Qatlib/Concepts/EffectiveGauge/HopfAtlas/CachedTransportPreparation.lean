/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceTransportWord
import Qatlib.Concepts.EffectiveGauge.RationalFlow.CachedMeanPreparation

set_option backward.isDefEq.respectTransparency false

/-! # Materialized coefficient and transport caches after the same finite mean preparation -/
set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Data and hypotheses for Cached Transport Preparation in the Hopf Atlas construction. -/
structure CachedTransportPreparation where
  prepared : CachedMeanPreparation
  coefficientBounds : Vector ℚ 9
  transportBounds : Vector ℚ 9

/-- Definition of materialize Transport Preparation in the Hopf Atlas construction. -/
def materializeTransportPreparation (prepared : CachedMeanPreparation) : CachedTransportPreparation :=
  let coeffs := Vector.ofFn (sourceFrameCoefficientMajorant prepared.derivativeBounds)
  let coefficient := fun n => if hn : n<9 then coeffs[n] else 0
  let transports := Vector.ofFn (fun r : Fin 9 => transportWordMajorant coefficient r.val)
  ⟨prepared,coeffs,transports⟩

/-- Definition of cached Transport Preparation Run in the Hopf Atlas construction. -/
def cachedTransportPreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) :
    Option CachedTransportPreparation :=
  (cachedMeanPreparationRun source bounds).map materializeTransportPreparation

/-- Original `materializeTransportPreparation_coefficient` guarantee for the `CachedTransportPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeTransportPreparation_coefficient (prepared : CachedMeanPreparation) (r : Fin 9) :
    (materializeTransportPreparation prepared).coefficientBounds[r.val]=
      sourceFrameCoefficientMajorant prepared.derivativeBounds r := by
  simp [materializeTransportPreparation]

/-- Original `materializeTransportPreparation_transport` guarantee for the `CachedTransportPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeTransportPreparation_transport (prepared : CachedMeanPreparation) (r : Fin 9) :
    (materializeTransportPreparation prepared).transportBounds[r.val]=
      sourceFrameTransportMajorant prepared.derivativeBounds r := by
  simp only [materializeTransportPreparation,Vector.getElem_ofFn,sourceFrameTransportMajorant]
  rfl

/-- The stored source cache and request trace came from the actual bound run. -/
theorem cachedMeanPreparationRun_boundExecution (source : RationalJetSource) (bounds : ℕ → ℚ)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared) :
    sourceFrameBoundRun bounds=some (prepared.derivativeBounds,prepared.boundRequests) := by
  rw [cachedMeanPreparationRun,sourceFrameBoundRun_eq] at hrun
  change (sourceMeanSectorExecution source (sourceFrameBoundExpected bounds 1)
    (sourceFrameBoundExpected bounds 2)).bind (fun sector => some
      (⟨sourceFrameBoundExpected bounds,sourceFrameBoundLabels (sourceMeanCompressedBound (bounds 1)),sector⟩ : CachedMeanPreparation))=some prepared at hrun
  cases hs : sourceMeanSectorExecution source (sourceFrameBoundExpected bounds 1)
      (sourceFrameBoundExpected bounds 2) with
  | none => simp [hs] at hrun
  | some sector =>
    have heq : (⟨sourceFrameBoundExpected bounds,
      sourceFrameBoundLabels (sourceMeanCompressedBound (bounds 1)),sector⟩ : CachedMeanPreparation)=prepared := by
      simpa only [hs,Option.bind_some,Option.some.injEq] using hrun
    rw [← heq]
    exact sourceFrameBoundRun_eq bounds

noncomputable section
open scoped Quaternion ContDiff

/-- The stored numerical vectors certify the same actual raw lift. This
conditional consumer preserves the successful producer identity; existence
and mean/sector correctness are supplied by cachedMeanPreparationRun_correct. -/
theorem materializeTransportPreparation_raw_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 9) (w : List (Fin 3)) (hw : w.length=r.val)
    (u : SpatialPoint) (hucube : InUnitCube u) :
    ‖spatialWordPartial (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) w u‖ ≤
      ((materializeTransportPreparation prepared).transportBounds[r.val] : ℝ) := by
  obtain ⟨packet,labels,hpacket,hlen,hlabels,hQ⟩ :=
    sourceFrameBoundRun_transport_correct v hv hu hp bounds hb
  have hsame : (packet,labels)=(prepared.derivativeBounds,prepared.boundRequests) :=
    Option.some.inj (hpacket.symm.trans (cachedMeanPreparationRun_boundExecution source bounds prepared hrun))
  have hcache : packet=prepared.derivativeBounds := congrArg Prod.fst hsame
  rw [hcache] at hQ
  rw [materializeTransportPreparation_transport]
  exact hQ q₀ h₀ r w hw u hucube

/-- Full source-driven success, same mean/sector result, and stored Q bounds
are simultaneous guarantees of this one finite materializing execution. -/
theorem cachedTransportPreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedTransportPreparationRun source bounds=some result ∧
      cachedMeanPreparationRun source bounds=some result.prepared ∧
      result.prepared.boundRequests.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ result.prepared.boundRequests, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (r : Fin 10) (w : List (Fin 3)), w.length=r.val → ∀ x, InFundamentalCube x →
        ‖spatialWordPartial v w x‖ ≤ (result.prepared.derivativeBounds r : ℝ)) ∧
      (∀ (r : Fin 10) (w : List (Fin 3)), w.length=r.val → ∀ u, InUnitCube u →
        ‖spatialWordPartial (unitCoordinateSpin v) w u‖ ≤
          (sourceFrameUnitBound result.prepared.derivativeBounds r : ℝ)) ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
          (result.prepared.derivativeBounds 1) (result.prepared.derivativeBounds 2) eta) x j))
        result.prepared.sector ∧
      (∀ r : Fin 9, result.coefficientBounds[r.val]=
        sourceFrameCoefficientMajorant result.prepared.derivativeBounds r) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 9) (w : List (Fin 3)), w.length=r.val →
        ∀ u, InUnitCube u →
          ‖spatialWordPartial (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) w u‖ ≤
            (result.transportBounds[r.val] : ℝ)) := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  refine ⟨materializeTransportPreparation prepared,?_,hrun,hlen,hlabels,hphys,hunit,hsector,?_,?_⟩
  · simp only [cachedTransportPreparationRun,hrun,Option.map_some]
  · exact materializeTransportPreparation_coefficient prepared
  · exact materializeTransportPreparation_raw_bound v hv hu hp bounds hb source prepared hrun

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
