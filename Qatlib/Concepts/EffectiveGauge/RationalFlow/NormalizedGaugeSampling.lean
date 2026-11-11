/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PreparedSourceGauge
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeWordBound

set_option backward.isDefEq.respectTransparency false

/-!
# Normalized Gauge Sampling

Rational Flow constructions for Effective Gauge.
Defines `gaugeUnitPeriodAccuracy`, `GaugeUnitSamplingPlan`, `materializeGaugeUnitSamplingPlan`.
Proves `gaugeUnitPeriodAccuracy_spec`, `normalizedGaugeSampling_error`, `materializeGaugeUnitSamplingFromGap_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of gauge Unit Period Accuracy in the Rational Flow construction. -/
def gaugeUnitPeriodAccuracy (P1 tolerance : ℚ) : ℚ := min 1 (tolerance/(12*(|P1|+1)))

/-- Data and hypotheses for Gauge Unit Sampling Plan in the Rational Flow construction. -/
structure GaugeUnitSamplingPlan where
  gauge : GeneralPoissonValueState
  tolerance : ℚ
  periodAccuracy : ℚ
  period : ℚ

/-- Definition of materialize Gauge Unit Sampling Plan in the Rational Flow construction. -/
def materializeGaugeUnitSamplingPlan (gap tolerance : ℚ) (r : GeneralPoissonValueState) : GaugeUnitSamplingPlan :=
  let P1 := cachedGaugeWordMajorant (referenceUnitCollar gap) r.preparation.prepared 1
  let ell := gaugeUnitPeriodAccuracy P1 tolerance
  ⟨r,tolerance,ell,fourierPeriodExecution ell⟩

/-- Definition of materialize Gauge Unit Sampling From Gap in the Rational Flow construction. -/
def materializeGaugeUnitSamplingFromGap (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) : Option GaugeUnitSamplingPlan :=
  (materializeSourceGaugeFromGap source prepared gap tolerance).map (materializeGaugeUnitSamplingPlan gap tolerance)

/-- Definition of source Gauge Unit Sampling in the Rational Flow construction. -/
def sourceGaugeUnitSampling (source : RationalJetSource) (gap : ℚ) (plan : GaugeUnitSamplingPlan)
    (address : Fin 3 → ℚ) : Option (Quaternion ℚ) :=
  sourceGaugePhysicalValue source gap plan.gauge (fun j => plan.period*rationalUnitWrap address j) plan.tolerance

/-- Original `gaugeUnitPeriodAccuracy_spec` guarantee for the `NormalizedGaugeSampling` construction; the complete source hypotheses are retained. -/
theorem gaugeUnitPeriodAccuracy_spec (P1 tolerance : ℚ) (ht : 0<tolerance) :
    0<gaugeUnitPeriodAccuracy P1 tolerance ∧ gaugeUnitPeriodAccuracy P1 tolerance ≤ 1 ∧
      3*|P1| * gaugeUnitPeriodAccuracy P1 tolerance ≤ tolerance/4 := by
  have hden : 0<12*(|P1|+1) := by positivity
  have hle := (le_div_iff₀ hden).mp (min_le_right (1 : ℚ) (tolerance/(12*(|P1|+1))))
  have he : 0<gaugeUnitPeriodAccuracy P1 tolerance := lt_min (by norm_num) (div_pos ht hden)
  refine ⟨he,min_le_left _ _,?_⟩
  dsimp only [gaugeUnitPeriodAccuracy] at he ⊢
  nlinarith

noncomputable section
open Set
open scoped Quaternion ContDiff

/-- Original `normalizedGaugeSampling_error` guarantee for the `NormalizedGaugeSampling` construction; the complete source hypotheses are retained. -/
theorem normalizedGaugeSampling_error (value : (Fin 3 → ℚ) → Option (Quaternion ℚ))
    (Q : QuaternionField) (hQ : ContDiff ℝ ∞ Q) (hp : IsPeriodicField Q)
    (P1 tolerance : ℚ) (ht : 0<tolerance)
    (hP1 : ∀ z j, ‖spatialWordPartial (fun u => Q (physicalPeriod • u)) [j] z‖ ≤ (P1 : ℝ))
    (hvalue : ∀ X : Fin 3 → ℚ, ∃ out, value X=some out ∧
      ‖rationalQuaternionCast out-Q (rationalSpatialPoint X)‖ ≤ (tolerance : ℝ)/2)
    (address : Fin 3 → ℚ) :
    let ell := gaugeUnitPeriodAccuracy P1 tolerance
    let length := fourierPeriodExecution ell
    ∃ out, value (fun j => length*rationalUnitWrap address j)=some out ∧
      ‖rationalQuaternionCast out-Q (physicalPeriod • rationalSpatialPoint address)‖ ≤ (tolerance : ℝ) := by
  let ell := gaugeUnitPeriodAccuracy P1 tolerance
  let length := fourierPeriodExecution ell
  let a := rationalUnitWrap address
  let X : Fin 3 → ℚ := fun j => length*a j
  let x := rationalSpatialPoint a
  let y := physicalPeriod⁻¹ • rationalSpatialPoint X
  let G : QuaternionField := fun u => Q (physicalPeriod • u)
  have hell := gaugeUnitPeriodAccuracy_spec P1 tolerance ht
  have he := fourierPeriodExecution_error ell hell.1
  have hellR : (0 : ℝ) ≤ ell := (Rat.cast_pos.mpr hell.1).le
  have hL1 : (1 : ℝ) ≤ physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  have hratio : |(length : ℝ)/physicalPeriod-1| ≤ (ell : ℝ) := by
    have hid : (length : ℝ)/physicalPeriod-1=((length : ℝ)-physicalPeriod)/physicalPeriod := by field_simp [physicalPeriod_pos.ne']
    rw [hid,abs_div,abs_of_pos physicalPeriod_pos]
    apply (div_le_iff₀ physicalPeriod_pos).mpr
    have hprod := mul_le_mul_of_nonneg_left hL1 hellR
    nlinarith
  have hcoord (j : Fin 3) : |y j-x j| ≤ (ell : ℝ) := by
    have haj : |(a j : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (rationalUnitWrap_mem address j).1]
      exact (rationalUnitWrap_mem address j).2
    have hid : y j-x j=((length : ℝ)/physicalPeriod-1)*(a j : ℝ) := by
      dsimp only [y,x,X,rationalSpatialPoint]
      push_cast
      change physicalPeriod⁻¹*((length : ℝ)*(a j : ℝ))-(a j : ℝ)=_
      ring
    rw [hid,abs_mul]
    exact (mul_le_mul hratio haj (abs_nonneg _) hellR).trans_eq (mul_one _)
  have hP : (0 : ℝ) ≤ P1 := (norm_nonneg _).trans (hP1 0 0)
  have hderiv (z : SpatialPoint) (j : Fin 3) : ‖fderiv ℝ G z (EuclideanSpace.single j 1)‖ ≤ |(P1 : ℝ)| :=
    (hP1 z j).trans (le_abs_self _)
  have hglobal := spatial_partial_norm_lipschitz G (hQ.comp (contDiff_id.const_smul physicalPeriod))
    |(P1 : ℝ)| (abs_nonneg _) hderiv y x
  have hsum : |y 0-x 0|+|y 1-x 1|+|y 2-x 2| ≤ 3*(ell : ℝ) := by
    linarith [hcoord 0,hcoord 1,hcoord 2]
  have hbudget : 3*|(P1 : ℝ)| * (ell : ℝ) ≤ (tolerance : ℝ)/4 := by exact_mod_cast hell.2.2
  have hdist : ‖G y-G x‖ ≤ (tolerance : ℝ)/4 := by
    have h := hglobal.trans (mul_le_mul_of_nonneg_left hsum (abs_nonneg _))
    nlinarith
  have htarget : G y=Q (rationalSpatialPoint X) := by
    dsimp only [G,y]
    rw [smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul]
  have hwrap : G x=Q (physicalPeriod • rationalSpatialPoint address) :=
    rationalUnitWrap_periodic G (periodicField_rescale_unit Q hp) address
  obtain ⟨out,hout,herror⟩ := hvalue X
  refine ⟨out,hout,?_⟩
  rw [← htarget] at herror
  rw [← hwrap]
  have htri := dist_triangle (rationalQuaternionCast out) (G y) (G x)
  simp only [dist_eq_norm] at htri
  exact (htri.trans (add_le_add herror hdist)).trans (by have htR : (0 : ℝ)<tolerance := Rat.cast_pos.mpr ht; linarith)

/-- Original `materializeGaugeUnitSamplingFromGap_correct` guarantee for the `NormalizedGaugeSampling` construction; the complete source hypotheses are retained. -/
theorem materializeGaugeUnitSamplingFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ plan, materializeGaugeUnitSamplingFromGap source prepared gap tolerance=some plan ∧
      plan.gauge.preparation.prepared=prepared ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs plan.gauge.preparation.prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (plan.gauge.preparation.prepared.derivativeBounds 1) (plan.gauge.preparation.prepared.derivativeBounds 2)
        eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
      ∀ address : Fin 3 → ℚ, ∃ out, sourceGaugeUnitSampling source gap plan address=some out ∧
        ‖rationalQuaternionCast out-selectedPoissonGauge q spec.2.1.1 spec.1 plan.gauge.preparation.prepared.sector
          (physicalPeriod • rationalSpatialPoint address)‖ ≤ (tolerance : ℝ) := by
  obtain ⟨r,hr,hprep,hbeta,hparameters,hcertificate,hpoint⟩ := materializeSourceGaugeFromGap_correct
    v hv hu hp source hs bounds hb prepared hrun gap hgap B hB hg hoff tolerance ht
  let plan := materializeGaugeUnitSamplingPlan gap tolerance r
  refine ⟨plan,?_,hprep,?_⟩
  · change (materializeSourceGaugeFromGap source prepared gap tolerance).map _=some plan
    rw [hr,Option.map_some]
  · let eta := referenceUnitCollar gap
    have collar := referenceUnitCollar_spec gap hgap
    have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
    have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
      have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
      simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
    let q := preparedPeriodicReference v hv hu source hs r.preparation.prepared eta
    have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (r.preparation.prepared.derivativeBounds 1) (r.preparation.prepared.derivativeBounds 2)
      eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
    let Q := selectedPoissonGauge q spec.2.1.1 spec.1 r.preparation.prepared.sector
    let P1 := cachedGaugeWordMajorant eta r.preparation.prepared 1
    have hrunr : cachedMeanPreparationRun source bounds=some r.preparation.prepared := by
      simpa only [hprep] using hrun
    have hP1 (z : SpatialPoint) (j : Fin 3) :
        ‖spatialWordPartial (fun u => Q (physicalPeriod • u)) [j] z‖ ≤ (P1 : ℝ) :=
      materializeReferencePreparation_gauge_word_bound v hv hu hp source hs bounds hb r.preparation.prepared hrunr
        eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin [j] (by norm_num) z
    dsimp only
    intro address
    exact normalizedGaugeSampling_error (fun X => sourceGaugePhysicalValue source gap r X tolerance) Q
      (selectedPoissonGauge_contDiff q spec.2.1.1 spec.1 _) (selectedPoissonGauge_periodic q spec.2.1.1 spec.1 _)
      P1 tolerance ht hP1 hpoint address

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
