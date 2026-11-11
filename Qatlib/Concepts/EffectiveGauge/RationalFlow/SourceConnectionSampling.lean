/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.ConnectionSampleExecution
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceValue
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CachedReferencePreparation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Connection Sampling

Rational Flow constructions for Effective Gauge.
Defines `preparedReferenceValueProgram`, `sourceConnectionSampling`, `sourceConnectionSamplingRun`.
Proves `sourceConnectionSampling_error`, `sourceConnectionSamplingRun_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of prepared Reference Value Program in the Rational Flow construction. -/
def preparedReferenceValueProgram (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  sourceReferenceValue (originalFirstJetPair source 0)
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta a tolerance

/-- Definition of source Connection Sampling in the Rational Flow construction. -/
def sourceConnectionSampling (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Fin 3 → ℚ) :=
  let cache := materializeReferencePreparation eta prepared
  connectionSampleExecution (preparedReferenceValueProgram source prepared eta)
    cache.corrected.correctedBounds[1] cache.corrected.correctedBounds[2] a tolerance

/-- Definition of source Connection Sampling Run in the Rational Flow construction. -/
def sourceConnectionSamplingRun (source : RationalJetSource) (bounds : ℕ → ℚ)
    (eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (CachedMeanPreparation × (Fin 3 → ℚ)) := do
  let prepared ← cachedMeanPreparationRun source bounds
  let out ← sourceConnectionSampling source prepared eta a tolerance
  return (prepared,out)

/-- Definition of source Connection Sampling From Gap in the Rational Flow construction. -/
def sourceConnectionSamplingFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (CachedMeanPreparation × (Fin 3 → ℚ)) :=
  sourceConnectionSamplingRun source bounds (referenceUnitCollar gap) a tolerance

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- The actual original source value program discharges all four sample
accuracy obligations. Its target and R bounds use the identical stored
preparation, including the effective zero-first-bound branch. -/
theorem sourceConnectionSampling_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ b, OnCubeBoundary b → mu ≤ ‖z-b‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (a : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ out, sourceConnectionSampling source prepared eta a tolerance=some out ∧ ∀ j,
      |(out j : ℝ)-physicalPeriod*connection (preparedPeriodicReference v hv hu source hs prepared eta)
        (physicalPeriod • rationalSpatialPoint a) j| ≤ (tolerance : ℝ)/2 := by
  let original := originalFirstJetPair source 0
  have hs0 := OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs)
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  let Q : QuaternionField := fun x => q (physicalPeriod • x)
  have hspec := sourcePeriodicReference_spec v hv hu hp original hs0
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  have hq : ContDiff ℝ ∞ q := hspec.2.1.1
  have hQ : ContDiff ℝ ∞ Q := hq.comp (contDiff_id.const_smul physicalPeriod)
  have hQu : ∀ x, ‖Q x‖=1 := fun x => (hspec.2.1.2 _).1
  have hQp : IsUnitPeriodicField Q := periodicField_rescale_unit q hspec.1
  obtain ⟨packet,labels,hpacket,hlen,hlabels,hphys,hunit⟩ :=
    sourceFrameBoundRun_correct v hv hu hp bounds hb
  have hsame : (packet,labels)=(prepared.derivativeBounds,prepared.boundRequests) :=
    Option.some.inj (hpacket.symm.trans (cachedMeanPreparationRun_boundExecution source bounds prepared hrun))
  have hcache : packet=prepared.derivativeBounds := congrArg Prod.fst hsame
  rw [hcache] at hphys
  have hzero : InFundamentalCube (0 : SpatialPoint) := by
    intro j
    exact ⟨by simp,by simpa using physicalPeriod_pos.le⟩
  have hm1 : 0 ≤ prepared.derivativeBounds 1 := by
    have ht' := (norm_nonneg _).trans (hphys 1 [0] rfl 0 hzero)
    exact_mod_cast ht'
  have hm2 : 0 ≤ prepared.derivativeBounds 2 := by
    have ht' := (norm_nonneg _).trans (hphys 2 [0,0] rfl 0 hzero)
    exact_mod_cast ht'
  have hb12 : SourceRescalingBounds v (prepared.derivativeBounds 1 : ℝ)
      (prepared.derivativeBounds 2 : ℝ) := by
    constructor
    · intro x hx j
      exact hphys 1 [j] rfl x hx
    · intro x hx j
      exact hphys 2 [j,0] rfl x hx
  have hvalue (b : Fin 3 → ℚ) (hb0 : ∀ j, (b j : ℝ)∈Icc 0 1)
      (t : ℚ) (ht0 : 0<t) (ht1 : t ≤ 1) :
      ∃ out, preparedReferenceValueProgram source prepared eta b t=some out ∧
        ‖rationalQuaternionCast out-Q (rationalSpatialPoint b)‖ ≤ (t : ℝ) := by
    exact sourceReferenceValue_error v hv hu hp original hs0
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) hm1 hm2 hb12
      B hB mu hm hg hoff eta he he1 hmargin b hb0 t ht0 ht1
  let cache := materializeReferencePreparation eta prepared
  let R1 := cache.corrected.correctedBounds[1]
  let R2 := cache.corrected.correctedBounds[2]
  have hR1 (x : SpatialPoint) (j : Fin 3) : ‖spatialWordPartial Q [j] x‖ ≤ (R1 : ℝ) :=
    materializeReferencePreparation_reference_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin 1 [j] rfl x
  have hR2 (x : SpatialPoint) (j : Fin 3) : ‖spatialWordPartial Q [j,j] x‖ ≤ (R2 : ℝ) :=
    materializeReferencePreparation_reference_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin 2 [j,j] rfl x
  have h1 : 0 ≤ R1 := by exact_mod_cast (norm_nonneg _).trans (hR1 0 0)
  have h2 : 0 ≤ R2 := by exact_mod_cast (norm_nonneg _).trans (hR2 0 0)
  obtain ⟨out,hout,herr⟩ := connectionSampleExecution_error Q hQ hQu hQp
    (preparedReferenceValueProgram source prepared eta) hvalue R1 R2 h1 h2 hR1 hR2 a tolerance ht
  refine ⟨out,hout,?_⟩
  intro j
  simpa only [Q,connection_scale q hq physicalPeriod] using herr j

/-- No external reference or connection-sampling oracle is supplied. -/
theorem sourceConnectionSamplingRun_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ b, OnCubeBoundary b → mu ≤ ‖z-b‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (a : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ prepared out, cachedMeanPreparationRun source bounds=some prepared ∧
      sourceConnectionSamplingRun source bounds eta a tolerance=some (prepared,out) ∧ ∀ j,
      |(out j : ℝ)-physicalPeriod*connection (preparedPeriodicReference v hv hu source hs prepared eta)
        (physicalPeriod • rationalSpatialPoint a) j| ≤ (tolerance : ℝ)/2 := by
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ :=
    cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb eta he B hB mu hm hg hoff hmargin
  obtain ⟨out,hout,herr⟩ := sourceConnectionSampling_error v hv hu hp source hs bounds hb
    prepared hrun eta he he1 B hB mu hm hg hoff hmargin a tolerance ht
  refine ⟨prepared,out,hrun,?_,herr⟩
  change (cachedMeanPreparationRun source bounds).bind _=_
  rw [hrun,Option.bind_some]
  change (sourceConnectionSampling source prepared eta a tolerance).bind _=_
  rw [hout,Option.bind_some]
  rfl

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
