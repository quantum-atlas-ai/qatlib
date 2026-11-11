/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCoefficientCube
import Qatlib.Concepts.EffectiveGauge.RationalFlow.FinitePoissonPlan

set_option backward.isDefEq.respectTransparency false

/-!
# Automatic Coefficient Preparation

Hopf Atlas constructions for Effective Gauge.
Defines `PoissonCoefficientPreparation`, `PoissonCoefficientPreparation.HasParameters`, `PoissonCoefficientPreparation.NumericalCertificate`.
Proves `materializePoissonCoefficientPreparation_correct`, `automaticPoissonCoefficientsFromGap_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Data and hypotheses for Poisson Coefficient Preparation in the Hopf Atlas construction. -/
structure PoissonCoefficientPreparation where
  prepared : CachedMeanPreparation
  referenceCache : CachedReferencePreparation
  cutoff : ℕ
  mesh : ℕ
  sampleAccuracy : ℚ
  modeAccuracy : ℚ
  periodAccuracy : ℚ
  period : ℚ
  data : RationalConnectionGridData
  coefficients : RationalFourierCoefficientList

/-- Definition of Has Parameters in the Hopf Atlas construction. -/
def PoissonCoefficientPreparation.HasParameters (r : PoissonCoefficientPreparation)
    (eta tolerance : ℚ) : Prop :=
  r.referenceCache=materializeReferencePreparation eta r.prepared ∧
  r.cutoff=finitePoissonCutoff r.referenceCache.connectionBounds[6] tolerance ∧
  r.mesh=finitePoissonMesh r.referenceCache.connectionBounds[0] r.referenceCache.connectionBounds[1] r.cutoff tolerance ∧
  r.sampleAccuracy=finitePoissonSampleAccuracy r.cutoff tolerance ∧
  r.modeAccuracy=finitePoissonModeAccuracy r.referenceCache.connectionBounds[0] r.cutoff tolerance ∧
  r.periodAccuracy=finitePoissonPeriodAccuracy r.referenceCache.connectionBounds[0] r.cutoff tolerance ∧
  r.period=fourierPeriodExecution r.periodAccuracy

/-- Definition of Numerical Certificate in the Hopf Atlas construction. -/
def PoissonCoefficientPreparation.NumericalCertificate (r : PoissonCoefficientPreparation)
    (tolerance : ℚ) : Prop :=
  0<r.cutoff ∧ 0<r.mesh ∧ (0<r.sampleAccuracy ∧ r.sampleAccuracy ≤ 1) ∧
  (0<r.modeAccuracy ∧ r.modeAccuracy ≤ 1) ∧ (0<r.periodAccuracy ∧ r.periodAccuracy ≤ 1) ∧
  |(r.period : ℝ)-physicalPeriod| ≤ (r.periodAccuracy : ℝ) ∧ (5 : ℝ)<r.period ∧
  3*(r.cutoff : ℚ)*r.periodAccuracy ≤ r.modeAccuracy/2 ∧
  400*r.referenceCache.connectionBounds[6] ≤ tolerance*(r.cutoff : ℚ)^3 ∧
  156*r.referenceCache.connectionBounds[6]/(r.cutoff : ℚ)^3 ≤ 39*tolerance/100 ∧
  r.data.map Prod.fst=sourceMeanGrid r.mesh ∧ r.coefficients.map Prod.fst=sourceFrequencyGrid r.cutoff

/-- General grid path. It computes every numerical parameter from the same
stored C0/C1/C6 before materializing the source grid once. -/
def materializePoissonCoefficientPreparation (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta tolerance : ℚ) : Option PoissonCoefficientPreparation :=
  let cache := materializeReferencePreparation eta prepared
  let N := finitePoissonCutoff cache.connectionBounds[6] tolerance
  let M := finitePoissonMesh cache.connectionBounds[0] cache.connectionBounds[1] N tolerance
  let s := finitePoissonSampleAccuracy N tolerance
  let d := finitePoissonModeAccuracy cache.connectionBounds[0] N tolerance
  let ell := finitePoissonPeriodAccuracy cache.connectionBounds[0] N tolerance
  let length := fourierPeriodExecution ell
  (sourceFourierCoefficientListExecution source prepared eta M s length d (sourceFrequencyGrid N)).map
    (fun result => ⟨prepared,cache,N,M,s,d,ell,length,result.1,result.2⟩)

/-- Definition of automatic Poisson Coefficients From Gap in the Hopf Atlas construction. -/
def automaticPoissonCoefficientsFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option PoissonCoefficientPreparation :=
  (cachedMeanPreparationRun source bounds).bind
    (fun prepared => materializePoissonCoefficientPreparation source prepared (referenceUnitCollar gap) tolerance)

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- Original `materializePoissonCoefficientPreparation_correct` guarantee for the `AutomaticCoefficientPreparation` construction; the complete source hypotheses are retained. -/
theorem materializePoissonCoefficientPreparation_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    ∃ result, materializePoissonCoefficientPreparation source prepared eta tolerance=some result ∧
      result.prepared=prepared ∧ result.HasParameters eta tolerance ∧ result.NumericalCertificate tolerance ∧
      let q := preparedPeriodicReference v hv hu source hs prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
      ∀ k∈Finset.Icc (-result.cutoff : SpatialFrequency) result.cutoff,
        ∃ out, (k,out)∈result.coefficients ∧ ∀ j,
          ‖normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k-rationalCircleCast (out j)‖ ≤
            (tolerance : ℝ)/(24*(finitePoissonFrequencyCount result.cutoff : ℝ)) := by
  let cache := materializeReferencePreparation eta prepared
  let C0 : ℚ := cache.connectionBounds[0]
  let C1 : ℚ := cache.connectionBounds[1]
  let C6 : ℚ := cache.connectionBounds[6]
  have hb0 := materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb prepared hrun
    eta he he1 B hB mu hm hg hoff hmargin 0 [] rfl 0 0
  have hC0 : 0 ≤ C0 := by exact_mod_cast ((norm_nonneg _).trans hb0)
  let N := finitePoissonCutoff C6 tolerance
  let M := finitePoissonMesh C0 C1 N tolerance
  let s := finitePoissonSampleAccuracy N tolerance
  let d := finitePoissonModeAccuracy C0 N tolerance
  let ell := finitePoissonPeriodAccuracy C0 N tolerance
  let length := fourierPeriodExecution ell
  have hN : 0<N := finitePoissonCutoff_pos _ _
  have hM : 0<M := finitePoissonMesh_pos _ _ _ _
  have hs' : 0<s ∧ s ≤ 1 := finitePoissonSampleAccuracy_spec N tolerance ht ht1
  have hd : 0<d ∧ d ≤ 1 := finitePoissonModeAccuracy_spec C0 hC0 N tolerance ht ht1
  have hell : 0<ell ∧ ell ≤ 1 := finitePoissonPeriodAccuracy_spec C0 hC0 N tolerance ht ht1
  have hbalance : 3*(N : ℚ)*ell ≤ d/2 := finitePoissonModePeriod_budget C0 hC0 N tolerance ht
  have hbalanceR : 3*(N : ℝ)*(ell : ℝ) ≤ (d : ℝ)/2 := by exact_mod_cast hbalance
  obtain ⟨data,coefficients,hout,hindices,hfrequencies,herror⟩ := sourceFourierCoefficientListExecution_error
    v hv hu hp source hs bounds hb prepared hrun eta he he1 B hB mu hm hg hoff hmargin
    M hM s length hs'.1 (sourceFrequencyGrid N) N (fun k hk j => sourceFrequencyGrid_real_bound N k hk j)
    d hd.1 hd.2 (ell : ℝ) (fourierPeriodExecution_error ell hell.1) hbalanceR
  let result : PoissonCoefficientPreparation := ⟨prepared,cache,N,M,s,d,ell,length,data,coefficients⟩
  have hparameters : result.HasParameters eta tolerance := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have hcertificate : result.NumericalCertificate tolerance :=
    ⟨hN,hM,hs',hd,hell,fourierPeriodExecution_error ell hell.1,
      fourierPeriodExecution_gt_five ell hell.1 hell.2,hbalance,
      finitePoissonCutoff_budget C6 tolerance ht,finitePoissonCutoff_tail_budget C6 tolerance ht,
      hindices,hfrequencies⟩
  refine ⟨result,?_,rfl,hparameters,hcertificate,?_⟩
  · change (sourceFourierCoefficientListExecution source prepared eta M s length d (sourceFrequencyGrid N)).map _=some result
    rw [hout,Option.map_some]
  · dsimp only
    intro k hk
    have hkmem : k∈sourceFrequencyGrid N := by
      apply List.mem_toFinset.mp
      rwa [sourceFrequencyGrid_toFinset]
    obtain ⟨out,houtmem,hbound⟩ := herror k hkmem
    refine ⟨out,houtmem,?_⟩
    intro j
    have hbudget := (Rat.cast_le (K := ℝ)).mpr (finitePoissonCoefficient_budget C0 C1 hC0 N tolerance ht ht1)
    push_cast at hbudget
    exact (hbound j).trans hbudget

/-- Fully automatic numerical coefficient preparation from the original
source and gap. N/M/s/d/ell and the period are outputs of this execution. -/
theorem automaticPoissonCoefficientsFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    ∃ result, automaticPoissonCoefficientsFromGap source bounds gap tolerance=some result ∧
      cachedMeanPreparationRun source bounds=some result.prepared ∧
      result.HasParameters (referenceUnitCollar gap) tolerance ∧ result.NumericalCertificate tolerance ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs result.prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (result.prepared.derivativeBounds 1) (result.prepared.derivativeBounds 2) eta collar.1 B hB (gap : ℝ)
        (Rat.cast_pos.mpr hgap) hg hoff margin
      ∀ k∈Finset.Icc (-result.cutoff : SpatialFrequency) result.cutoff,
        ∃ out, (k,out)∈result.coefficients ∧ ∀ j,
          ‖normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k-rationalCircleCast (out j)‖ ≤
            (tolerance : ℝ)/(24*(finitePoissonFrequencyCount result.cutoff : ℝ)) := by
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ := cachedMeanPreparationRun_correct
    v hv hu hp source hs bounds hb eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  obtain ⟨result,hout,hprepared,hparameters,hcertificate,herror⟩ := materializePoissonCoefficientPreparation_correct
    v hv hu hp source hs bounds hb prepared hrun eta collar.1 he1 B hB (gap : ℝ)
    (Rat.cast_pos.mpr hgap) hg hoff margin tolerance ht ht1
  refine ⟨result,?_,?_,hparameters,hcertificate,?_⟩
  · change (cachedMeanPreparationRun source bounds).bind _=some result
    rw [hrun,Option.bind_some]
    exact hout
  · simpa only [hprepared] using hrun
  · simpa only [hprepared] using herror

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
