/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedTransportPreparation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceAngularIdentity

set_option backward.isDefEq.respectTransparency false

/-! # Gamma preprocessing reads the already stored Q vector -/
set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of stored Transport Value in the Hopf Atlas construction. -/
def storedTransportValue (q : Vector ℚ 9) (n : ℕ) : ℚ :=
  if hn : n<9 then q[n] else 0

/-- Definition of stored Gamma Majorant in the Hopf Atlas construction. -/
def storedGammaMajorant (q : Vector ℚ 9) (r : Fin 8) : ℚ :=
  ∑ j ∈ Finset.range (r.val+1), (r.val.choose j : ℚ)*
    storedTransportValue q j*storedTransportValue q (r.val-j+1)

/-- Data and hypotheses for Cached Angular Preparation in the Hopf Atlas construction. -/
structure CachedAngularPreparation where
  transport : CachedTransportPreparation
  angularBounds : Vector ℚ 8

/-- Definition of materialize Angular Preparation in the Hopf Atlas construction. -/
def materializeAngularPreparation (prepared : CachedMeanPreparation) : CachedAngularPreparation :=
  let transport := materializeTransportPreparation prepared
  let gamma := Vector.ofFn (storedGammaMajorant transport.transportBounds)
  ⟨transport,gamma⟩

/-- Definition of cached Angular Preparation Run in the Hopf Atlas construction. -/
def cachedAngularPreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) :
    Option CachedAngularPreparation :=
  (cachedMeanPreparationRun source bounds).map materializeAngularPreparation

/-- This stage preserves the actual preceding producer when projected back. -/
theorem cachedAngularPreparationRun_transport (source : RationalJetSource) (bounds : ℕ → ℚ) :
    (cachedAngularPreparationRun source bounds).map CachedAngularPreparation.transport=
      cachedTransportPreparationRun source bounds := by
  simp [cachedAngularPreparationRun,cachedTransportPreparationRun,Option.map_map,
    Function.comp_def,materializeAngularPreparation]

/-- Original `materializeAngularPreparation_angular` guarantee for the `CachedAngularPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeAngularPreparation_angular (prepared : CachedMeanPreparation) (r : Fin 8) :
    (materializeAngularPreparation prepared).angularBounds[r.val]=
      sourceFrameGammaMajorant prepared.derivativeBounds r := by
  have hQ (n : ℕ) (hn : n<9) :
      storedTransportValue (materializeTransportPreparation prepared).transportBounds n=
        transportWordMajorant (sourceFrameCoefficientNat prepared.derivativeBounds) n := by
    rw [storedTransportValue,dif_pos hn]
    exact materializeTransportPreparation_transport prepared ⟨n,hn⟩
  simp only [materializeAngularPreparation,Vector.getElem_ofFn,storedGammaMajorant,sourceFrameGammaMajorant]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [hQ j (by omega),hQ (r.val-j+1) (by omega)]

noncomputable section
open scoped Quaternion ContDiff

/-- The actual stored Gamma vector, computed from stored Q, bounds the
actual terminal angular field of the same physical raw lift. -/
theorem materializeAngularPreparation_angular_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val)
    (u : SpatialPoint) (hucube : InUnitCube u) :
    ‖spatialWordPartial (wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1) w u‖ ≤
      ((materializeAngularPreparation prepared).angularBounds[r.val] : ℝ) := by
  obtain ⟨packet,labels,hpacket,hlen,hlabels,hGamma⟩ :=
    sourceFrameBoundRun_angular_correct v hv hu hp bounds hb
  have hsame : (packet,labels)=(prepared.derivativeBounds,prepared.boundRequests) :=
    Option.some.inj (hpacket.symm.trans (cachedMeanPreparationRun_boundExecution source bounds prepared hrun))
  have hcache : packet=prepared.derivativeBounds := congrArg Prod.fst hsame
  rw [hcache] at hGamma
  rw [materializeAngularPreparation_angular]
  exact hGamma q₀ h₀ r w hw u hucube

/-- All guarantees belong to one actual materialized preparation. Its Q
and Gamma vectors reuse the same derivative packet and actual mean sector. -/
theorem cachedAngularPreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedAngularPreparationRun source bounds=some result ∧
      cachedTransportPreparationRun source bounds=some result.transport ∧
      result.transport.prepared.boundRequests.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ result.transport.prepared.boundRequests, 1 ≤ order ∧ order ≤ 9) ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
          (result.transport.prepared.derivativeBounds 1) (result.transport.prepared.derivativeBounds 2) eta) x j))
        result.transport.prepared.sector ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 9) (w : List (Fin 3)), w.length=r.val →
        ∀ u, InUnitCube u →
          ‖spatialWordPartial (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) w u‖ ≤
            (result.transport.transportBounds[r.val] : ℝ)) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ u, InUnitCube u →
        ‖spatialWordPartial (wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1) w u‖ ≤
          (result.angularBounds[r.val] : ℝ)) := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  refine ⟨materializeAngularPreparation prepared,?_,?_,hlen,hlabels,hsector,?_,?_⟩
  · simp only [cachedAngularPreparationRun,hrun,Option.map_some]
  · simp only [cachedTransportPreparationRun,hrun,Option.map_some,materializeAngularPreparation]
  · exact materializeTransportPreparation_raw_bound v hv hu hp bounds hb source prepared hrun
  · exact materializeAngularPreparation_angular_bound v hv hu hp bounds hb source prepared hrun

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
