/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugePositivePhase
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhasePositiveWord

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Word Bound

Hopf Atlas constructions for Effective Gauge.
Defines `gaugeWordMajorant`, `cachedGaugeWordMajorant`.
Proves `selectedPoissonGauge_normalized_word_bound`, `materializeReferencePreparation_gauge_word_bound`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of gauge Word Majorant in the Hopf Atlas construction. -/
def gaugeWordMajorant (R : ℕ → ℚ) (C6 : ℚ) (n : SpatialFrequency) (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (r+1), (r.choose j : ℚ)*
    phaseWordMajorant (gaugePositivePhaseModulus C6 n) j*R (r-j)

/-- Definition of cached Gauge Word Majorant in the Hopf Atlas construction. -/
def cachedGaugeWordMajorant (eta : ℚ) (prepared : CachedMeanPreparation) (r : ℕ) : ℚ :=
  let cache := materializeReferencePreparation eta prepared
  gaugeWordMajorant (storedPhaseValue cache.corrected.correctedBounds) cache.connectionBounds[6]
    (selectedSectorWinding prepared.sector) r

noncomputable section
open Set
open scoped Quaternion ContDiff

/-- Original `selectedPoissonGauge_normalized_word_bound` guarantee for the `GaugeWordBound` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_normalized_word_bound (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (C6 : ℚ)
    (hC6 : ∀ j i x, InUnitCube x →
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤ (C6 : ℝ))
    (R : ℕ → ℚ) (hR : ∀ w : List (Fin 3), w.length ≤ 3 → ∀ x,
      ‖spatialWordPartial (fun u => q (physicalPeriod • u)) w x‖ ≤ (R w.length : ℝ))
    (result : SourceMeanSectorResult) (w : List (Fin 3)) (hw : w.length ≤ 3) (x : SpatialPoint) :
    ‖spatialWordPartial (fun u => selectedPoissonGauge q hq hp result (physicalPeriod • u)) w x‖ ≤
      (gaugeWordMajorant R C6 (selectedSectorWinding result) w.length : ℝ) := by
  let n := selectedSectorWinding result
  let theta := normalizedGaugePhase q hq hp n
  let Phi := gaugePositivePhaseModulus C6 n
  let Q : QuaternionField := fun u => q (physicalPeriod • u)
  have ht : ContDiff ℝ ∞ theta := by
    exact ((contDiff_const.mul (windingLinear n).contDiff).add
      (normalizedConnectionPoisson_spec q hq hp).1).sub contDiff_const
  have hQ : ContDiff ℝ ∞ Q := hq.comp (contDiff_id.const_smul physicalPeriod)
  have hphase (z : List (Fin 3)) (hz : z.length ≤ 3) :
      ‖spatialWordPartial (fun u => phase (theta u)) z x‖ ≤ (phaseWordMajorant Phi z.length : ℝ) :=
    spatialWordPartial_phase_positive_norm_le theta ht Phi 3 x
      (fun z hz0 hz3 => normalizedGaugePhase_positive_bound q hq hp C6 hC6 n z hz0 hz3 x) z hz
  have hF (j : ℕ) (hj : j ≤ w.length) : (0 : ℝ) ≤ phaseWordMajorant Phi j := by
    have h := (norm_nonneg _).trans (hphase (List.replicate j 0) (by simpa using hj.trans hw))
    simpa only [List.length_replicate] using h
  have hG (j : ℕ) (hj : j ≤ w.length) : (0 : ℝ) ≤ R j := by
    have h := (norm_nonneg _).trans (hR (List.replicate j 0) (by simpa using hj.trans hw) x)
    simpa only [List.length_replicate] using h
  rw [selectedPoissonGauge_normalized]
  have h := spatialWordPartial_mul_norm_le (fun u => phase (theta u)) Q (contDiff_phase.comp ht) hQ
    (fun j => (phaseWordMajorant Phi j : ℝ)) (fun j => (R j : ℝ)) w x hF hG
    (fun z hz => hphase z (hz.trans hw)) (fun z hz => hR z (hz.trans hw) x)
  simpa only [gaugeWordMajorant,wordProductMajorant,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast] using h

/-- Original `materializeReferencePreparation_gauge_word_bound` guarantee for the `GaugeWordBound` construction; the complete source hypotheses are retained. -/
theorem materializeReferencePreparation_gauge_word_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (w : List (Fin 3)) (hw : w.length ≤ 3) (x : SpatialPoint) :
    let q := preparedPeriodicReference v hv hu source hs prepared eta
    let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
    ‖spatialWordPartial (fun u => selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector (physicalPeriod • u)) w x‖ ≤
      (cachedGaugeWordMajorant eta prepared w.length : ℝ) := by
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  let cache := materializeReferencePreparation eta prepared
  let R := storedPhaseValue cache.corrected.correctedBounds
  have hR (z : List (Fin 3)) (hz : z.length ≤ 3) (y : SpatialPoint) :
      ‖spatialWordPartial (fun u => q (physicalPeriod • u)) z y‖ ≤ (R z.length : ℝ) := by
    let r : Fin 8 := ⟨z.length,by omega⟩
    have h := materializeReferencePreparation_reference_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin r z rfl y
    simpa only [R,storedPhaseValue,dif_pos (show z.length<8 by omega)] using h
  have hC6 (j i : Fin 3) (y : SpatialPoint) (_hy : InUnitCube y) :
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) y‖ ≤ (cache.connectionBounds[6] : ℝ) :=
    materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin 6 (List.replicate 6 i) (by simp) j y
  exact selectedPoissonGauge_normalized_word_bound q spec.2.1.1 spec.1 cache.connectionBounds[6] hC6
    R hR prepared.sector w hw x

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
