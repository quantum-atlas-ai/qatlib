/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedCorrectionPreparation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseExponentialWord

set_option backward.isDefEq.respectTransparency false

/-! # Stored derivative bounds of the executed corrected raw reference -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of stored Corrected Majorant in the Hopf Atlas construction. -/
def storedCorrectedMajorant (exponential : Vector ℚ 8) (transport : Vector ℚ 9) (r : Fin 8) : ℚ :=
  ∑ j ∈ range (r.val+1), (r.val.choose j : ℚ)*storedPhaseValue exponential j*
    storedTransportValue transport (r.val-j)

/-- Data and hypotheses for Cached Corrected Preparation in the Hopf Atlas construction. -/
structure CachedCorrectedPreparation where
  correction : CachedCorrectionPreparation
  exponentialBounds : Vector ℚ 8
  correctedBounds : Vector ℚ 8

/-- Definition of materialize Corrected Preparation in the Hopf Atlas construction. -/
def materializeCorrectedPreparation (eta : ℚ) (prepared : CachedMeanPreparation) : CachedCorrectedPreparation :=
  let correction := materializeCorrectionPreparation eta prepared
  let exponential := Vector.ofFn (fun r : Fin 8 => phaseWordMajorant
    (storedPhaseValue correction.correctionBounds) r.val)
  let corrected := Vector.ofFn (storedCorrectedMajorant exponential correction.phase.angular.transport.transportBounds)
  ⟨correction,exponential,corrected⟩

/-- Definition of cached Corrected Preparation Run in the Hopf Atlas construction. -/
def cachedCorrectedPreparationRun (source : RationalJetSource) (bounds : ℕ → ℚ) (eta : ℚ) :
    Option CachedCorrectedPreparation :=
  (cachedMeanPreparationRun source bounds).map (materializeCorrectedPreparation eta)

/-- Original `cachedCorrectedPreparationRun_correction` guarantee for the `CachedCorrectedPreparation` construction; the complete source hypotheses are retained. -/
theorem cachedCorrectedPreparationRun_correction (source : RationalJetSource) (bounds : ℕ → ℚ) (eta : ℚ) :
    (cachedCorrectedPreparationRun source bounds eta).map CachedCorrectedPreparation.correction=
      cachedCorrectionPreparationRun source bounds eta := by
  simp [cachedCorrectedPreparationRun,cachedCorrectionPreparationRun,Option.map_map,
    Function.comp_def,materializeCorrectedPreparation]

noncomputable section
open scoped Quaternion ContDiff

/-- Definition of source Corrected Unit Lift in the Hopf Atlas construction. -/
def sourceCorrectedUnitLift (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (x : SpatialPoint) : ℍ :=
  phase (sourceCorrectionPhase v hv q₀ h₀ eta x)*
    sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • x)

/-- Original `contDiff_sourceCorrectedUnitLift` guarantee for the `CachedCorrectedPreparation` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceCorrectedUnitLift (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) : ContDiff ℝ ∞ (sourceCorrectedUnitLift v hv q₀ h₀ eta) :=
  (contDiff_phase.comp (contDiff_sourceCorrectionPhase v hv q₀ h₀ eta)).mul
    ((contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod))

/-- Original `materializeCorrectedPreparation_exponential_bound` guarantee for the `CachedCorrectedPreparation` construction; the complete source hypotheses are retained. -/
theorem materializeCorrectedPreparation_exponential_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (fun y => phase (sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ) y)) w x‖ ≤
      ((materializeCorrectedPreparation eta prepared).exponentialBounds[r.val] : ℝ) := by
  simp only [materializeCorrectedPreparation,Vector.getElem_ofFn]
  rw [← hw]
  apply spatialWordPartial_phase_norm_le _ (contDiff_sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ)) _ w.length x
  · intro z hz
    have hzlt : z.length<8 := by omega
    simpa only [storedPhaseValue,dif_pos hzlt] using
      materializeCorrectionPreparation_correction_bound v hv hu hp bounds hb source prepared hrun eta he
        q₀ h₀ ⟨z.length,hzlt⟩ z rfl x hx
  · exact le_rfl

/-- The actual correction and raw transport are multiplied before taking
coordinate words; the stored convolution has no unknown reference modulus. -/
theorem materializeCorrectedPreparation_corrected_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (r : Fin 8) (w : List (Fin 3)) (hw : w.length=r.val)
    (x : SpatialPoint) (hx : InUnitCube x) :
    ‖spatialWordPartial (sourceCorrectedUnitLift v hv q₀ h₀ (eta : ℝ)) w x‖ ≤
      ((materializeCorrectedPreparation eta prepared).correctedBounds[r.val] : ℝ) := by
  let result := materializeCorrectedPreparation eta prepared
  let f := fun y => phase (sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ) y)
  let g := fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)
  let F := fun j => (storedPhaseValue result.exponentialBounds j : ℝ)
  let G := fun j => (storedTransportValue result.correction.phase.angular.transport.transportBounds j : ℝ)
  have hf : ContDiff ℝ ∞ f := contDiff_phase.comp (contDiff_sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ))
  have hg : ContDiff ℝ ∞ g := (contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp
    (contDiff_id.const_smul physicalPeriod)
  have hFB (z : List (Fin 3)) (hz : z.length ≤ w.length) : ‖spatialWordPartial f z x‖ ≤ F z.length := by
    have hzlt : z.length<8 := by omega
    simpa only [F,storedPhaseValue,dif_pos hzlt] using
      materializeCorrectedPreparation_exponential_bound v hv hu hp bounds hb source prepared hrun eta he
        q₀ h₀ ⟨z.length,hzlt⟩ z rfl x hx
  have hGB (z : List (Fin 3)) (hz : z.length ≤ w.length) : ‖spatialWordPartial g z x‖ ≤ G z.length := by
    have hzlt : z.length<9 := by omega
    simpa only [G,g,result,materializeCorrectedPreparation,materializeCorrectionPreparation,
      materializePhasePreparation,materializeAngularPreparation,storedTransportValue,dif_pos hzlt] using
      materializeTransportPreparation_raw_bound v hv hu hp bounds hb source prepared hrun
        q₀ h₀ ⟨z.length,hzlt⟩ z rfl x hx
  have hF (j : ℕ) (hj : j ≤ w.length) : 0 ≤ F j := by
    simpa only [List.length_replicate] using (norm_nonneg _).trans (hFB (List.replicate j 0) (by simpa))
  have hG (j : ℕ) (hj : j ≤ w.length) : 0 ≤ G j := by
    simpa only [List.length_replicate] using (norm_nonneg _).trans (hGB (List.replicate j 0) (by simpa))
  have hprod := spatialWordPartial_mul_norm_le f g hf hg F G w x hF hG hFB hGB
  change ‖spatialWordPartial (fun y => f y*g y) w x‖ ≤ _
  apply hprod.trans_eq
  rw [hw]
  simp only [result,materializeCorrectedPreparation,Vector.getElem_ofFn,storedCorrectedMajorant,
    Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,wordProductMajorant,F,G]

/-- Success retains the preceding same-execution mean certificate through
its producer identity and adds the true corrected-reference derivative vector. -/
theorem cachedCorrectedPreparationRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    ∃ result, cachedCorrectedPreparationRun source bounds eta=some result ∧
      cachedCorrectionPreparationRun source bounds eta=some result.correction ∧
      SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
          (result.correction.phase.angular.transport.prepared.derivativeBounds 1)
          (result.correction.phase.angular.transport.prepared.derivativeBounds 2) eta) x j))
        result.correction.phase.angular.transport.prepared.sector ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ x, InUnitCube x → ‖spatialWordPartial (sourceCorrectedUnitLift v hv q₀ h₀ (eta : ℝ)) w x‖ ≤
          (result.correctedBounds[r.val] : ℝ)) := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  refine ⟨materializeCorrectedPreparation eta prepared,?_,?_,hsector,?_⟩
  · simp only [cachedCorrectedPreparationRun,hrun,Option.map_some]
  · simp only [cachedCorrectionPreparationRun,hrun,Option.map_some,materializeCorrectedPreparation]
  · exact materializeCorrectedPreparation_corrected_bound v hv hu hp bounds hb source prepared hrun eta he

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
