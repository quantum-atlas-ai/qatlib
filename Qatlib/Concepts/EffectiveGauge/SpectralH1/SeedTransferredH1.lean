/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.SpectralH1.SeedTransferredProducer

set_option backward.isDefEq.respectTransparency false

/-!
# Seed Transferred H1

Spectral H1 constructions for Effective Gauge.
Proves `materializeSeedTransferredArtifact_H1_correct`, `automaticSeedTransferredArtifact_H1_correct`, `seedTransferredTarget_spec`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `materializeSeedTransferredArtifact_H1_correct` guarantee for the `SeedTransferredH1` construction; the complete source hypotheses are retained. -/
theorem materializeSeedTransferredArtifact_H1_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (toChart : SeedChart)
    (hto : originalSeedChartAccepted source (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) toChart=true)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ artifact, materializeSeedTransferredArtifact source prepared gap toChart tolerance=some artifact ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
        eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
      let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
      let C := seedChartTransition (storeReferenceFrame source prepared eta).chart toChart (sourceQuaternion v 0)
      let target := constantLeftGauge C Q
      let energy := physicalFieldH1Energy (fun X => target X-transferredGaugeArtifactField artifact X)
      energy ≤ (tolerance : ℝ)^2/4 ∧ Real.sqrt energy ≤ (tolerance : ℝ)/2 ∧
      ∀ X : Fin 3 → ℚ, ∀ accuracy : ℚ, 0<accuracy →
        ‖rationalQuaternionCast (transferredGaugeArtifactValue artifact X accuracy)-
          transferredGaugeArtifactField artifact (rationalSpatialPoint X)‖ ≤ (accuracy : ℝ)/2 := by
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
    eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
  have hQ : ContDiff ℝ ∞ Q := selectedPoissonGauge_contDiff q spec.2.1.1 spec.1 prepared.sector
  have hQu : ∀ X, ‖Q X‖=1 := selectedPoissonGauge_norm q spec.2.1.1 spec.1
    (fun X => (spec.2.1.2 X).1) prepared.sector
  let frame := storeReferenceFrame source prepared eta
  let M := frame.gaugeBounds[1]
  let delta := seedTransferArtifactAccuracy M tolerance
  have hd := (seedTransferArtifactAccuracy_spec M tolerance ht).1
  have hfrom : originalSeedChartAccepted source (prepared.derivativeBounds 1)
      (prepared.derivativeBounds 2) frame.chart=true :=
    seedChartAccepted_choose (originSpinSamples (rescaledSpinSamples (originalFirstJetPair source 0)
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)) 4)
  obtain ⟨transition,htransition,htransitionError⟩ := originalSeedTransitionRun_correct v hu source hs
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) frame.chart toChart hfrom hto
    (2*delta) (by positivity)
  let C := seedChartTransition frame.chart toChart (sourceQuaternion v 0)
  have hAC : ‖rationalQuaternionCast transition-C‖ ≤ (delta : ℝ) := by
    have h : ‖rationalQuaternionCast transition-C‖ ≤ (2 : ℝ)*(delta : ℝ)/2 := by
      simpa only [Rat.cast_mul,Rat.cast_ofNat] using htransitionError
    linarith
  have hcoarse := rescaledOriginSamples_error v (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) 4 0
  have he : |(originSpinSamples (rescaledSpinSamples (originalFirstJetPair source 0)
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)) 4 0 : ℝ)-
        (sourceQuaternion v 0).imI| ≤ (1/16 : ℝ) := by
    norm_num at hcoarse ⊢
    exact hcoarse
  have hva := seedChartAccepted_valid _ _ he frame.chart hfrom
  have hvb := seedChartAccepted_valid _ _ he toChart hto
  have hC : ‖C‖=1 := (seedChartTransition_spec frame.chart toChart (sourceQuaternion v 0)
    rfl ((spinOfVector_norm _).trans (hu 0)) hva hvb).1
  obtain ⟨base,hbase,hcert⟩ := materializeGaugeFourierArtifactFromGap_H1_correct
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff (tolerance/8) (by positivity)
  rw [← materializeStoredGaugeArtifact_output source prepared gap (tolerance/8)] at hbase
  let F := gaugeFourierArtifactField base
  have hF : ContDiff ℝ ∞ F := gaugeFourierArtifactField_contDiff base
  have herror : physicalFieldH1Energy (fun X => F X-Q X) ≤ ((tolerance : ℝ)/8)^2/4 := by
    rw [physicalFieldH1Energy_sub_comm F Q hF hQ]
    simpa only [Rat.cast_div,Rat.cast_ofNat] using hcert.1
  have hnorm (i : Fin 3) (X : SpatialPoint) : ‖spatialWordPartial Q [i] X‖ ≤ |(M : ℝ)| := by
    have hunit (j : Fin 3) (u : SpatialPoint) :
        ‖spatialWordPartial (fun x => Q (physicalPeriod • x)) [j] u‖ ≤ (M : ℝ) := by
      have h := materializeReferencePreparation_gauge_word_bound v hv hu hp source hs bounds hb prepared hrun
        eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin [j] (by norm_num) u
      have hM : M=cachedGaugeWordMajorant eta prepared 1 := storeReferenceFrame_gaugeBounds source prepared eta (1 : Fin 4)
      rw [hM]
      exact h
    exact (physicalFirstWord_of_normalized_bound Q hQ (M : ℝ) hunit i X).trans (le_abs_self _)
  have henergy : physicalFieldH1Energy Q ≤ 343*(1+3*|(M : ℝ)|^2) := by
    have h := physicalFieldH1Energy_unit_bound Q hQ hQu |(M : ℝ)| (abs_nonneg _) hnorm
    have hL : physicalPeriod ≤ 7 := by dsimp only [physicalPeriod]; linarith [Real.pi_lt_d2]
    have hL3 : physicalPeriod^3 ≤ (343 : ℝ) := by
      calc
        _ ≤ (7 : ℝ)^3 := pow_le_pow_left₀ physicalPeriod_pos.le hL 3
        _ = _ := by norm_num
    exact h.trans (mul_le_mul_of_nonneg_right hL3 (by positivity))
  have hbound := seedTransferArtifact_H1_bound M tolerance ht (rationalQuaternionCast transition) C hC
    hAC F Q hF hQ herror henergy
  let artifact : TransferredGaugeArtifact := ⟨base,transition⟩
  refine ⟨artifact,?_,?_⟩
  · change (materializeStoredGaugeArtifact source frame (tolerance/8)).bind
        (fun saved => (originalSeedTransitionRun source (prepared.derivativeBounds 1)
          (prepared.derivativeBounds 2) frame.chart toChart (2*delta)).bind
            (fun result => some (⟨saved,result⟩ : TransferredGaugeArtifact)))=some artifact
    rw [hbase]
    change (originalSeedTransitionRun source (prepared.derivativeBounds 1)
      (prepared.derivativeBounds 2) frame.chart toChart (2*delta)).bind
        (fun result => some (⟨base,result⟩ : TransferredGaugeArtifact))=some artifact
    rw [htransition]
    rfl
  · dsimp only
    have henergyFinal : physicalFieldH1Energy (fun X => C*Q X-rationalQuaternionCast transition*F X) ≤
        (tolerance : ℝ)^2/4 := by
      rw [physicalFieldH1Energy_sub_comm _ _ (contDiff_const.mul hQ) (contDiff_const.mul hF)]
      exact hbound
    refine ⟨henergyFinal,?_,?_⟩
    · change Real.sqrt (physicalFieldH1Energy (fun X => C*Q X-rationalQuaternionCast transition*F X)) ≤
        (tolerance : ℝ)/2
      apply Real.sqrt_le_iff.mpr
      refine ⟨(by positivity),?_⟩
      exact henergyFinal.trans_eq (by ring)
    · intro X accuracy hacc
      exact transferredGaugeArtifactValue_error artifact X accuracy hacc


/-- Original `automaticSeedTransferredArtifact_H1_correct` guarantee for the `SeedTransferredH1` construction; the complete source hypotheses are retained. -/
theorem automaticSeedTransferredArtifact_H1_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (toChart : SeedChart)
    (hto : ∀ prepared, cachedMeanPreparationRun source bounds=some prepared →
      originalSeedChartAccepted source (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) toChart=true)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ prepared artifact, cachedMeanPreparationRun source bounds=some prepared ∧
      automaticSeedTransferredArtifact source bounds gap toChart tolerance=some artifact ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
        eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
      let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
      let C := seedChartTransition (storeReferenceFrame source prepared eta).chart toChart (sourceQuaternion v 0)
      let target := constantLeftGauge C Q
      let energy := physicalFieldH1Energy (fun X => target X-transferredGaugeArtifactField artifact X)
      energy ≤ (tolerance : ℝ)^2/4 ∧ Real.sqrt energy ≤ (tolerance : ℝ)/2 ∧
      ∀ X : Fin 3 → ℚ, ∀ accuracy : ℚ, 0<accuracy →
        ‖rationalQuaternionCast (transferredGaugeArtifactValue artifact X accuracy)-
          transferredGaugeArtifactField artifact (rationalSpatialPoint X)‖ ≤ (accuracy : ℝ)/2 := by
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  obtain ⟨prepared,hrun,_⟩ := cachedMeanPreparationRun_correct v hv hu hp source hs bounds hb
    eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  obtain ⟨artifact,hmat,hcert⟩ := materializeSeedTransferredArtifact_H1_correct
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff toChart (hto prepared hrun) tolerance ht
  refine ⟨prepared,artifact,hrun,?_,hcert⟩
  rw [automaticSeedTransferredArtifact,hrun]
  exact hmat


/-- Original `seedTransferredTarget_spec` guarantee for the `SeedTransferredH1` construction; the complete source hypotheses are retained. -/
theorem seedTransferredTarget_spec (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (prepared : CachedMeanPreparation)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (toChart : SeedChart)
    (hto : originalSeedChartAccepted source (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) toChart=true)
 :
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
        eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
      let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
      let C := seedChartTransition (storeReferenceFrame source prepared eta).chart toChart (sourceQuaternion v 0)
      let target := constantLeftGauge C Q
      ContDiff ℝ ∞ target ∧ (∀ X, ‖target X‖=1 ∧ hopf (target X)=sourceQuaternion v X) ∧
      IsPeriodicField target ∧ IsSolenoidal target ∧
      (∀ X j, connection target X j=connection Q X j) ∧
      target 0=exactChartSeed toChart (sourceQuaternion v 0) ∧ HasSeedChartPhase toChart (target 0) := by
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)
    eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  let Q := selectedPoissonGauge q spec.2.1.1 spec.1 prepared.sector
  let frame := storeReferenceFrame source prepared eta
  have hfrom : originalSeedChartAccepted source (prepared.derivativeBounds 1)
      (prepared.derivativeBounds 2) frame.chart=true :=
    seedChartAccepted_choose (originSpinSamples (rescaledSpinSamples (originalFirstJetPair source 0)
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)) 4)
  have hcoarse := rescaledOriginSamples_error v (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) 4 0
  have he : |(originSpinSamples (rescaledSpinSamples (originalFirstJetPair source 0)
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2)) 4 0 : ℝ)-
        (sourceQuaternion v 0).imI| ≤ (1/16 : ℝ) := by
    norm_num at hcoarse ⊢
    exact hcoarse
  have hva := seedChartAccepted_valid _ _ he frame.chart hfrom
  have hvb := seedChartAccepted_valid _ _ he toChart hto
  have hQ : ContDiff ℝ ∞ Q := selectedPoissonGauge_contDiff q spec.2.1.1 spec.1 prepared.sector
  have hQu : ∀ X, ‖Q X‖=1 := selectedPoissonGauge_norm q spec.2.1.1 spec.1
    (fun X => (spec.2.1.2 X).1) prepared.sector
  have hQp : IsPeriodicField Q := selectedPoissonGauge_periodic q spec.2.1.1 spec.1 prepared.sector
  have hQs : IsSolenoidal Q := selectedPoissonGauge_solenoidal q spec.2.1.1 spec.1
    (fun X => (spec.2.1.2 X).1) prepared.sector
  have hQ0 : Q 0=exactChartSeed frame.chart (sourceQuaternion v 0) := by
    exact (selectedPoissonGauge_origin q spec.2.1.1 spec.1 prepared.sector).trans spec.2.2
  have htarget := seedChartTransfer_spec frame.chart toChart (sourceQuaternion v 0) rfl
    ((spinOfVector_norm _).trans (hu 0)) hva hvb Q hQ hQu hQp hQs hQ0
  dsimp only at htarget ⊢
  refine ⟨htarget.1,?_,htarget.2.2.1,htarget.2.2.2.1,htarget.2.2.2.2.1,
    htarget.2.2.2.2.2.1,htarget.2.2.2.2.2.2⟩
  intro X
  refine ⟨(htarget.2.1 X).1,?_⟩
  exact (htarget.2.1 X).2.trans
    ((selectedPoissonGauge_hopf q spec.2.1.1 spec.1 prepared.sector X).trans ((spec.2.1.2 X).2))

end Qatlib.Concepts.EffectiveGauge.SpectralH1
