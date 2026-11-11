/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedPhasePreparation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCorrectionWord

set_option backward.isDefEq.respectTransparency false

/-! # Stored cutoff and correction bounds from the same original-source execution -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of stored Phase Value in the Hopf Atlas construction. -/
def storedPhaseValue (lambda : Vector ℚ 8) (n : ℕ) : ℚ :=
  if hn : n<8 then lambda[n] else 0

/-- Definition of stored Correction Majorant in the Hopf Atlas construction. -/
def storedCorrectionMajorant (cutoff lambda : Vector ℚ 8) (r : Fin 8) : ℚ :=
  ∑ j ∈ range (r.val+1), (r.val.choose j : ℚ)*storedPhaseValue cutoff j*storedPhaseValue lambda (r.val-j)

/-- Data and hypotheses for Cached Correction Preparation in the Hopf Atlas construction. -/
structure CachedCorrectionPreparation where
  phase : CachedPhasePreparation
  cutoffBounds : Vector ℚ 8
  correctionBounds : Vector ℚ 8

/-- Definition of materialize Correction Preparation in the Hopf Atlas construction. -/
def materializeCorrectionPreparation (eta : ℚ) (prepared : CachedMeanPreparation) :
    CachedCorrectionPreparation :=
  let phase := materializePhasePreparation prepared
  let cutoff := Vector.ofFn (fun r : Fin 8 => cutoffUnitMajorant eta r.val)
  let correction := Vector.ofFn (storedCorrectionMajorant cutoff phase.phaseBounds)
  ⟨phase,cutoff,correction⟩

/-- Definition of cached Correction Preparation Run in the Hopf Atlas construction. -/
def cachedCorrectionPreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) (eta : ℚ) :
    Option CachedCorrectionPreparation :=
  (cachedMeanPreparationRun source bounds).map (materializeCorrectionPreparation eta)

/-- Original `cachedCorrectionPreparationRun_phase` guarantee for the `CachedCorrectionPreparation` construction; the complete source hypotheses are retained. -/
theorem cachedCorrectionPreparationRun_phase (source : RationalJetSource) (bounds : ℕ → ℚ) (eta : ℚ) :
    (cachedCorrectionPreparationRun source bounds eta).map CachedCorrectionPreparation.phase=
      cachedPhasePreparationRun source bounds := by
  simp [cachedCorrectionPreparationRun,cachedPhasePreparationRun,Option.map_map,
    Function.comp_def,materializeCorrectionPreparation]

/-- Original `materializeCorrectionPreparation_cutoff` guarantee for the `CachedCorrectionPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeCorrectionPreparation_cutoff (eta : ℚ) (prepared : CachedMeanPreparation) (r : Fin 8) :
    (materializeCorrectionPreparation eta prepared).cutoffBounds[r.val]=cutoffUnitMajorant eta r.val := by
  simp [materializeCorrectionPreparation]

/-- Original `materializeCorrectionPreparation_correction` guarantee for the `CachedCorrectionPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeCorrectionPreparation_correction (eta : ℚ) (prepared : CachedMeanPreparation) (r : Fin 8) :
    (materializeCorrectionPreparation eta prepared).correctionBounds[r.val]=
      sourceFrameCorrectionMajorant prepared.derivativeBounds eta r := by
  simp only [materializeCorrectionPreparation,Vector.getElem_ofFn,storedCorrectionMajorant,
    sourceFrameCorrectionMajorant]
  apply sum_congr rfl
  intro j hj
  have hjlt : j<8 := by have := mem_range.mp hj; omega
  have hklt : r.val-j<8 := by omega
  simp only [storedPhaseValue,dif_pos hjlt,dif_pos hklt,Vector.getElem_ofFn,
    sourceFrameLambdaNat]
  rw [materializePhasePreparation_phase prepared ⟨r.val-j,hklt⟩]

noncomputable section
open scoped Quaternion ContDiff

/-- Original `materializeCorrectionPreparation_correction_bound` guarantee for the `CachedCorrectionPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeCorrectionPreparation_correction_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ)) w x‖ ≤
      ((materializeCorrectionPreparation eta prepared).correctionBounds[r.val] : ℝ) := by
  obtain ⟨packet,labels,hpacket,_,_,hPhi⟩ :=
    sourceFrameBoundRun_correction_correct v hv hu hp bounds hb eta he
  have hsame : (packet,labels)=(prepared.derivativeBounds,prepared.boundRequests) :=
    Option.some.inj (hpacket.symm.trans (cachedMeanPreparationRun_boundExecution source bounds prepared hrun))
  have hcache : packet=prepared.derivativeBounds := congrArg Prod.fst hsame
  rw [hcache] at hPhi
  rw [materializeCorrectionPreparation_correction]
  exact hPhi q₀ h₀ r w hw x hx

/-- The same returned object carries its physical mean sector and the actual
cutoff-product bounds. Materialization never calls a source or bound oracle. -/
theorem cachedCorrectionPreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedCorrectionPreparationRun source bounds eta=some result ∧
      cachedPhasePreparationRun source bounds=some result.phase ∧
      result.phase.angular.transport.prepared.boundRequests.length=
        (if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ result.phase.angular.transport.prepared.boundRequests, 1 ≤ order ∧ order ≤ 9) ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
          (result.phase.angular.transport.prepared.derivativeBounds 1)
          (result.phase.angular.transport.prepared.derivativeBounds 2) eta) x j))
        result.phase.angular.transport.prepared.sector ∧
      (∀ (r : Fin 8) (w : List (Fin 3)), w.length=r.val → ∀ x,
        ‖spatialWordPartial (unitCutoffField (eta : ℝ)) w x‖ ≤ (result.cutoffBounds[r.val] : ℝ)) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ x, InUnitCube x → ‖spatialWordPartial (sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ)) w x‖ ≤
          (result.correctionBounds[r.val] : ℝ)) := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  refine ⟨materializeCorrectionPreparation eta prepared,?_,?_,hlen,hlabels,hsector,?_,?_⟩
  · simp only [cachedCorrectionPreparationRun,hrun,Option.map_some]
  · simp only [cachedPhasePreparationRun,hrun,Option.map_some,materializeCorrectionPreparation]
  · intro r w hw x
    rw [materializeCorrectionPreparation_cutoff,← hw]
    exact unitCutoffField_word_bound eta he w x
  · exact materializeCorrectionPreparation_correction_bound v hv hu hp bounds hb source prepared hrun eta he

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
