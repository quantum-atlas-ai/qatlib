/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicReferenceWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordConnection
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordPeriodic

set_option backward.isDefEq.respectTransparency false

/-! # Same-execution stored R0,...,R7 and c0,...,c6 for the periodic reference -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of stored Connection Majorant in the Hopf Atlas construction. -/
def storedConnectionMajorant (reference : Vector ℚ 8) (r : Fin 7) : ℚ :=
  ∑ j ∈ range (r.val+1), (r.val.choose j : ℚ)*storedPhaseValue reference j*
    storedPhaseValue reference (r.val-j+1)

/-- Data and hypotheses for Cached Reference Preparation in the Hopf Atlas construction. -/
structure CachedReferencePreparation where
  corrected : CachedCorrectedPreparation
  connectionBounds : Vector ℚ 7

/-- Definition of prepared in the Hopf Atlas construction. -/
def CachedReferencePreparation.prepared (result : CachedReferencePreparation) : CachedMeanPreparation :=
  result.corrected.correction.phase.angular.transport.prepared

/-- Definition of materialize Reference Preparation in the Hopf Atlas construction. -/
def materializeReferencePreparation (eta : ℚ) (prepared : CachedMeanPreparation) : CachedReferencePreparation :=
  let corrected := materializeCorrectedPreparation eta prepared
  let connection := Vector.ofFn (storedConnectionMajorant corrected.correctedBounds)
  ⟨corrected,connection⟩

/-- Definition of cached Reference Preparation Run in the Hopf Atlas construction. -/
def cachedReferencePreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) (eta : ℚ) :
    Option CachedReferencePreparation :=
  (cachedMeanPreparationRun source bounds).map (materializeReferencePreparation eta)

/-- The collar is selected from the original physical support gap, before
any output tolerance is supplied. -/
def cachedReferencePreparationFromGap (source : RationalJetSource) (bounds : ℕ → ℚ) (gap : ℚ) :
    Option CachedReferencePreparation :=
  cachedReferencePreparationRun source bounds (referenceUnitCollar gap)

/-- Original `materializeReferencePreparation_prepared` guarantee for the `CachedReferencePreparation` construction; the complete source hypotheses are retained. -/
theorem materializeReferencePreparation_prepared (eta : ℚ) (prepared : CachedMeanPreparation) :
    (materializeReferencePreparation eta prepared).prepared=prepared := rfl

/-- Original `cachedReferencePreparationRun_corrected` guarantee for the `CachedReferencePreparation` construction; the complete source hypotheses are retained. -/
theorem cachedReferencePreparationRun_corrected (source : RationalJetSource) (bounds : ℕ → ℚ) (eta : ℚ) :
    (cachedReferencePreparationRun source bounds eta).map CachedReferencePreparation.corrected=
      cachedCorrectedPreparationRun source bounds eta := by
  simp [cachedReferencePreparationRun,cachedCorrectedPreparationRun,Option.map_map,
    Function.comp_def,materializeReferencePreparation]

noncomputable section
open scoped Quaternion ContDiff

/-- Definition of prepared Periodic Reference in the Hopf Atlas construction. -/
def preparedPeriodicReference (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (prepared : CachedMeanPreparation) (eta : ℚ) : QuaternionField :=
  sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta

/-- Original `materializeReferencePreparation_reference_bound` guarantee for the `CachedReferencePreparation` construction; the complete source hypotheses are retained. -/
theorem materializeReferencePreparation_reference_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val) (x : SpatialPoint) :
    ‖spatialWordPartial (fun y => preparedPeriodicReference v hv hu source hs prepared eta
      (physicalPeriod • y)) w x‖ ≤
      ((materializeReferencePreparation eta prepared).corrected.correctedBounds[r.val] : ℝ) := by
  have hspec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  apply normalizedPeriodicWordBound_global _ hspec.2.1.1 hspec.1 w _ _ x
  intro u hu0
  exact materializeCorrectedPreparation_periodic_bound v hv hu hp source hs bounds hb prepared hrun
    eta he he1 B hB mu hm hg hoff hmargin r w hw u hu0

/-- Original `materializeReferencePreparation_connection_bound` guarantee for the `CachedReferencePreparation` construction; the complete source hypotheses are retained. -/
theorem materializeReferencePreparation_connection_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (r : Fin 7) (w : List (Fin 3)) (hw : w.length=r.val) (i : Fin 3) (x : SpatialPoint) :
    ‖spatialWordPartial (fun y => physicalPeriod*connection
      (preparedPeriodicReference v hv hu source hs prepared eta) (physicalPeriod • y) i) w x‖ ≤
      ((materializeReferencePreparation eta prepared).connectionBounds[r.val] : ℝ) := by
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have hspec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  have hq : ContDiff ℝ ∞ q := hspec.2.1.1
  have hscale : (fun y => physicalPeriod*connection q (physicalPeriod • y) i)=
      fun y => connection (fun z => q (physicalPeriod • z)) y i :=
    funext (fun y => (connection_scale q hq physicalPeriod y i).symm)
  change ‖spatialWordPartial (fun y => physicalPeriod*connection q (physicalPeriod • y) i) w x‖ ≤ _
  rw [hscale]
  let F := fun n => (storedPhaseValue (materializeReferencePreparation eta prepared).corrected.correctedBounds n : ℝ)
  have hBq (z : List (Fin 3)) (hz : z.length ≤ w.length+1) :
      ‖spatialWordPartial (fun y => q (physicalPeriod • y)) z x‖ ≤ F z.length := by
    have hzlt : z.length<8 := by omega
    simpa only [F,storedPhaseValue,dif_pos hzlt] using
      materializeReferencePreparation_reference_bound v hv hu hp source hs bounds hb prepared hrun eta he he1
        B hB mu hm hg hoff hmargin ⟨z.length,hzlt⟩ z rfl x
  have hbound := connection_word_bound _ (hq.comp (contDiff_id.const_smul physicalPeriod)) i F w x hBq
  apply hbound.trans_eq
  rw [hw]
  simp only [materializeReferencePreparation,Vector.getElem_ofFn,storedConnectionMajorant,
    Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,wordProductMajorant,F]

/-- One finite source execution supplies the physical mean sector, global R
bounds of its actual periodic reference, and global c bounds of its actual
normalized connection. No reference, phase, Poisson solution or modulus is input. -/
theorem cachedReferencePreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedReferencePreparationRun source bounds eta=some result ∧
      cachedCorrectedPreparationRun source bounds eta=some result.corrected ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (preparedPeriodicReference v hv hu source hs result.prepared eta) x j)) result.prepared.sector ∧
      (∀ (r : Fin 8) (w : List (Fin 3)), w.length=r.val → ∀ x,
        ‖spatialWordPartial (fun y => preparedPeriodicReference v hv hu source hs result.prepared eta
          (physicalPeriod • y)) w x‖ ≤ (result.corrected.correctedBounds[r.val] : ℝ)) ∧
      (∀ (r : Fin 7) (w : List (Fin 3)), w.length=r.val → ∀ i x,
        ‖spatialWordPartial (fun y => physicalPeriod*connection
          (preparedPeriodicReference v hv hu source hs result.prepared eta) (physicalPeriod • y) i) w x‖ ≤
          (result.connectionBounds[r.val] : ℝ)) := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  refine ⟨materializeReferencePreparation eta prepared,?_,?_,hsector,?_,?_⟩
  · simp only [cachedReferencePreparationRun,hrun,Option.map_some]
  · simp only [cachedCorrectedPreparationRun,hrun,Option.map_some,materializeReferencePreparation]
  · exact materializeReferencePreparation_reference_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin
  · exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin

/-- The original gap input selects the same fixed reference and all its
regularity caches; no collar parameter or output epsilon is requested. -/
theorem cachedReferencePreparationFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b) :
    ∃ result, cachedReferencePreparationFromGap source bounds gap=some result ∧
      cachedReferencePreparationRun source bounds (referenceUnitCollar gap)=some result ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (preparedPeriodicReference v hv hu source hs result.prepared (referenceUnitCollar gap)) x j)) result.prepared.sector ∧
      (∀ (r : Fin 8) (w : List (Fin 3)), w.length=r.val → ∀ x,
        ‖spatialWordPartial (fun y => preparedPeriodicReference v hv hu source hs result.prepared
          (referenceUnitCollar gap) (physicalPeriod • y)) w x‖ ≤ (result.corrected.correctedBounds[r.val] : ℝ)) ∧
      (∀ (r : Fin 7) (w : List (Fin 3)), w.length=r.val → ∀ i x,
        ‖spatialWordPartial (fun y => physicalPeriod*connection
          (preparedPeriodicReference v hv hu source hs result.prepared (referenceUnitCollar gap))
          (physicalPeriod • y) i) w x‖ ≤ (result.connectionBounds[r.val] : ℝ)) := by
  have he := referenceUnitCollar_spec gap hgap
  have he1 : referenceUnitCollar gap ≤ 1/2 := he.2.1.trans (by norm_num)
  have hmargin : 7*(referenceUnitCollar gap : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*referenceUnitCollar gap : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr he.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  obtain ⟨result,hrun,hprevious,hsector,hR,hC⟩ := cachedReferencePreparationRun_correct v hv hu hp source hs
    bounds hb (referenceUnitCollar gap) he.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff hmargin
  exact ⟨result,hrun,hrun,hsector,hR,hC⟩

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
