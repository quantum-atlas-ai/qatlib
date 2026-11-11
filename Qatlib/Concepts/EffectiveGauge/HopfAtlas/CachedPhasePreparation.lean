/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedAngularPreparation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourcePhaseWord

set_option backward.isDefEq.respectTransparency false

/-! # The real-phase majorants read the stored angular vector -/
set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of stored Lambda Majorant in the Hopf Atlas construction. -/
def storedLambdaMajorant (gamma : Vector ℚ 8) (r : Fin 8) : ℚ :=
  if hr : r.val=0 then 7*gamma[0] else gamma[r.val-1]+7*gamma[r.val]

/-- Data and hypotheses for Cached Phase Preparation in the Hopf Atlas construction. -/
structure CachedPhasePreparation where
  angular : CachedAngularPreparation
  phaseBounds : Vector ℚ 8

/-- Definition of materialize Phase Preparation in the Hopf Atlas construction. -/
def materializePhasePreparation (prepared : CachedMeanPreparation) : CachedPhasePreparation :=
  let angular := materializeAngularPreparation prepared
  let phase := Vector.ofFn (storedLambdaMajorant angular.angularBounds)
  ⟨angular,phase⟩

/-- Definition of cached Phase Preparation Run in the Hopf Atlas construction. -/
def cachedPhasePreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) : Option CachedPhasePreparation :=
  (cachedMeanPreparationRun source bounds).map materializePhasePreparation

/-- Original `cachedPhasePreparationRun_angular` guarantee for the `CachedPhasePreparation` construction; the complete source hypotheses are retained. -/
theorem cachedPhasePreparationRun_angular (source : RationalJetSource) (bounds : ℕ → ℚ) :
    (cachedPhasePreparationRun source bounds).map CachedPhasePreparation.angular=
      cachedAngularPreparationRun source bounds := by
  simp [cachedPhasePreparationRun,cachedAngularPreparationRun,Option.map_map,
    Function.comp_def,materializePhasePreparation]

/-- Original `materializePhasePreparation_phase` guarantee for the `CachedPhasePreparation` construction; the complete source hypotheses are retained. -/
theorem materializePhasePreparation_phase (prepared : CachedMeanPreparation) (r : Fin 8) :
    (materializePhasePreparation prepared).phaseBounds[r.val]=
      sourceFrameLambdaMajorant prepared.derivativeBounds r := by
  simp only [materializePhasePreparation,Vector.getElem_ofFn,storedLambdaMajorant,sourceFrameLambdaMajorant]
  split_ifs with hr
  · exact congrArg (fun q : ℚ => 7*q) (materializeAngularPreparation_angular prepared 0)
  · rw [materializeAngularPreparation_angular prepared ⟨r.val-1,by omega⟩,
      materializeAngularPreparation_angular prepared r]

noncomputable section
open scoped Quaternion ContDiff

/-- The computed finite vector bounds the actual real phase, with all turns
retained. No real phase or regularity modulus is supplied as an input. -/
theorem materializePhasePreparation_phase_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (sourceUnitRealPhase v hv q₀ h₀) w x‖ ≤
      ((materializePhasePreparation prepared).phaseBounds[r.val] : ℝ) := by
  obtain ⟨packet,labels,hpacket,hlen,hlabels,hLambda⟩ :=
    sourceFrameBoundRun_phase_correct v hv hu hp bounds hb
  have hsame : (packet,labels)=(prepared.derivativeBounds,prepared.boundRequests) :=
    Option.some.inj (hpacket.symm.trans (cachedMeanPreparationRun_boundExecution source bounds prepared hrun))
  have hcache : packet=prepared.derivativeBounds := congrArg Prod.fst hsame
  rw [hcache] at hLambda
  rw [materializePhasePreparation_phase]
  exact hLambda q₀ h₀ r w hw x hx

/-- Source-driven success preserves the exact preceding angular execution
and the same reference mean, while adding the actual real-phase bounds. -/
theorem cachedPhasePreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedPhasePreparationRun source bounds=some result ∧
      cachedAngularPreparationRun source bounds=some result.angular ∧
      result.angular.transport.prepared.boundRequests.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ result.angular.transport.prepared.boundRequests, 1 ≤ order ∧ order ≤ 9) ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
          (result.angular.transport.prepared.derivativeBounds 1)
          (result.angular.transport.prepared.derivativeBounds 2) eta) x j))
        result.angular.transport.prepared.sector ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ x, InUnitCube x → ‖spatialWordPartial (sourceUnitRealPhase v hv q₀ h₀) w x‖ ≤
          (result.phaseBounds[r.val] : ℝ)) := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  refine ⟨materializePhasePreparation prepared,?_,?_,hlen,hlabels,hsector,?_⟩
  · simp only [cachedPhasePreparationRun,hrun,Option.map_some]
  · simp only [cachedAngularPreparationRun,hrun,Option.map_some,materializePhasePreparation]
  · exact materializePhasePreparation_phase_bound v hv hu hp bounds hb source prepared hrun

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
