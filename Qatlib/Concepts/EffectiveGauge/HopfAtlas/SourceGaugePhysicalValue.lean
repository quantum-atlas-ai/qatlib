/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.AutomaticPhysicalPoissonValue
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhysicalReferenceValue
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerGauge

set_option backward.isDefEq.respectTransparency false

/-!
# Source Gauge Physical Value

Hopf Atlas constructions for Effective Gauge.
Defines `gaugePhysicalValueAccuracy`, `rationalWindingAngle`, `automaticSourceGaugeFromGap`.
Proves `gaugePhysicalValueAccuracy_spec`, `rationalWindingAngle_cast`, `gaugeProduct_error`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of gauge Physical Value Accuracy in the Hopf Atlas construction. -/
def gaugePhysicalValueAccuracy (tolerance : ℚ) : ℚ := min (1/64) (tolerance/16)

/-- Definition of rational Winding Angle in the Hopf Atlas construction. -/
def rationalWindingAngle (n : SpatialFrequency) (X : Fin 3 → ℚ) : ℚ :=
  ∑ j : Fin 3, (n j : ℚ)*X j

/-- Definition of automatic Source Gauge From Gap in the Hopf Atlas construction. -/
def automaticSourceGaugeFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option GeneralPoissonValueState :=
  automaticPhysicalPoissonFromGap source bounds gap (gaugePhysicalValueAccuracy tolerance)

/-- Definition of source Gauge Physical Value in the Hopf Atlas construction. -/
def sourceGaugePhysicalValue (source : RationalJetSource) (gap : ℚ) (r : GeneralPoissonValueState)
    (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) := do
  let gamma := gaugePhysicalValueAccuracy tolerance
  let reference ← sourceReferencePhysicalValue source r.preparation.prepared (referenceUnitCollar gap) X gamma
  let angle := rationalWindingAngle (selectedSectorWinding r.preparation.prepared.sector) X+
    generalPoissonPhysicalPhaseValue r X gamma
  return rationalCircleQuaternion (rationalCis angle gamma).value*reference

/-- Original `gaugePhysicalValueAccuracy_spec` guarantee for the `SourceGaugePhysicalValue` construction; the complete source hypotheses are retained. -/
theorem gaugePhysicalValueAccuracy_spec (tolerance : ℚ) (ht : 0<tolerance) :
    0<gaugePhysicalValueAccuracy tolerance ∧ gaugePhysicalValueAccuracy tolerance ≤ 1/64 ∧
      gaugePhysicalValueAccuracy tolerance ≤ tolerance/16 := by
  exact ⟨lt_min (by norm_num) (div_pos ht (by norm_num)),min_le_left _ _,min_le_right _ _⟩

noncomputable section
open scoped Quaternion ContDiff

/-- Original `rationalWindingAngle_cast` guarantee for the `SourceGaugePhysicalValue` construction; the complete source hypotheses are retained. -/
theorem rationalWindingAngle_cast (n : SpatialFrequency) (X : Fin 3 → ℚ) :
    (rationalWindingAngle n X : ℝ)=windingLinear n (rationalSpatialPoint X) := by
  rw [windingLinear_apply]
  simp only [rationalWindingAngle,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast,rationalSpatialPoint]

/-- Original `gaugeProduct_error` guarantee for the `SourceGaugePhysicalValue` construction; the complete source hypotheses are retained. -/
theorem gaugeProduct_error (a b p q : ℍ) (d : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hp : ‖p‖=1) (hq : ‖q‖=1) (ha : ‖a-p‖ ≤ 3*d/2) (hb : ‖b-q‖ ≤ d/2) :
    ‖a*b-p*q‖ ≤ 3*d := by
  have haNorm : ‖a‖ ≤ 1+3*d/2 := by
    have h := norm_le_norm_sub_add a p
    rw [hp] at h
    linarith
  have hid : a*b-p*q=(a-p)*q+a*(b-q) := by noncomm_ring
  rw [hid]
  have hnorm := norm_add_le ((a-p)*q) (a*(b-q))
  rw [norm_mul,norm_mul,hq,mul_one] at hnorm
  have hprod := mul_le_mul haNorm hb (norm_nonneg _) (by positivity : 0 ≤ 1+3*d/2)
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hd1)]

/-- Conditional join only; the original-source theorem discharges both
same-state phase accuracy and physical reference success. -/
theorem sourceGaugePhysicalValue_error (source : RationalJetSource) (gap : ℚ) (r : GeneralPoissonValueState)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q)
    (hu : ∀ x, ‖q x‖=1) (X : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance)
    (hphase : |(generalPoissonPhysicalPhaseValue r X (gaugePhysicalValueAccuracy tolerance) : ℝ)-
      physicalPoissonPhase q hq hp (rationalSpatialPoint X)| ≤ (gaugePhysicalValueAccuracy tolerance : ℝ)/2)
    (hreference : ∃ out, sourceReferencePhysicalValue source r.preparation.prepared (referenceUnitCollar gap)
      X (gaugePhysicalValueAccuracy tolerance)=some out ∧
      ‖rationalQuaternionCast out-q (rationalSpatialPoint X)‖ ≤ (gaugePhysicalValueAccuracy tolerance : ℝ)/2) :
    ∃ out, sourceGaugePhysicalValue source gap r X tolerance=some out ∧
      ‖rationalQuaternionCast out-selectedPoissonGauge q hq hp r.preparation.prepared.sector
        (rationalSpatialPoint X)‖ ≤ (tolerance : ℝ)/2 := by
  let gamma := gaugePhysicalValueAccuracy tolerance
  let n := selectedSectorWinding r.preparation.prepared.sector
  let angle := rationalWindingAngle n X+generalPoissonPhysicalPhaseValue r X gamma
  let theta := windingLinear n (rationalSpatialPoint X)+physicalPoissonPhase q hq hp (rationalSpatialPoint X)
  let a := rationalCircleQuaternion (rationalCis angle gamma).value
  have hg := gaugePhysicalValueAccuracy_spec tolerance ht
  have hg1 : gamma ≤ 1 := hg.2.1.trans (by norm_num)
  have hgR : (0 : ℝ) ≤ gamma := (Rat.cast_pos.mpr hg.1).le
  have hcis : ‖rationalQuaternionCast a-phase (angle : ℝ)‖ ≤ (gamma : ℝ) :=
    (rationalCis_quaternion_error angle gamma hg.1 hg1).trans (Rat.cast_le.mpr (rationalCis_spec angle gamma hg.1 hg1).2.2.1)
  have hangle : |(angle : ℝ)-theta| ≤ (gamma : ℝ)/2 := by
    dsimp only [angle,theta]
    rw [Rat.cast_add,rationalWindingAngle_cast,add_sub_add_left_eq_sub]
    exact hphase
  have hphaseError : ‖rationalQuaternionCast a-phase theta‖ ≤ 3*(gamma : ℝ)/2 := by
    have htri := dist_triangle (rationalQuaternionCast a) (phase (angle : ℝ)) (phase theta)
    simp only [dist_eq_norm] at htri
    exact (htri.trans (add_le_add hcis ((phase_lipschitz _ _).trans hangle))).trans_eq (by ring)
  obtain ⟨reference,hrun,herror⟩ := hreference
  have htarget : selectedPoissonGauge q hq hp r.preparation.prepared.sector (rationalSpatialPoint X)=
      phase theta*q (rationalSpatialPoint X) := by
    dsimp only [selectedPoissonGauge,integerGauge,poissonCorrectedLift,theta,n]
    rw [← mul_assoc,← phase_add]
  refine ⟨a*reference,?_,?_⟩
  · change (sourceReferencePhysicalValue source r.preparation.prepared (referenceUnitCollar gap) X gamma).bind _=some (a*reference)
    rw [hrun,Option.bind_some]
    rfl
  · rw [map_mul,htarget]
    have h := gaugeProduct_error (rationalQuaternionCast a) (rationalQuaternionCast reference)
      (phase theta) (q (rationalSpatialPoint X)) (gamma : ℝ) hgR (by exact_mod_cast hg1)
      (phase_norm _) (hu _) hphaseError herror
    have hbudget : (gamma : ℝ) ≤ (tolerance : ℝ)/16 := by exact_mod_cast hg.2.2
    exact h.trans (by have htR : (0 : ℝ)<tolerance := Rat.cast_pos.mpr ht; linarith)

open Set

/-- Original `automaticSourceGaugeFromGap_correct` guarantee for the `SourceGaugePhysicalValue` construction; the complete source hypotheses are retained. -/
theorem automaticSourceGaugeFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ result, automaticSourceGaugeFromGap source bounds gap tolerance=some result ∧
      cachedMeanPreparationRun source bounds=some result.preparation.prepared ∧
      result.beta=rationalPoissonBetaList result.preparation.coefficients ∧
      result.preparation.HasParameters (referenceUnitCollar gap) (physicalPoissonValueTolerance (gaugePhysicalValueAccuracy tolerance)) ∧
      result.preparation.NumericalCertificate (physicalPoissonValueTolerance (gaugePhysicalValueAccuracy tolerance)) ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs result.preparation.prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (result.preparation.prepared.derivativeBounds 1) (result.preparation.prepared.derivativeBounds 2)
        eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
      ∀ X : Fin 3 → ℚ, ∃ out,
        sourceGaugePhysicalValue source gap result X tolerance=some out ∧
        ‖rationalQuaternionCast out-selectedPoissonGauge q spec.2.1.1 spec.1
          result.preparation.prepared.sector (rationalSpatialPoint X)‖ ≤ (tolerance : ℝ)/2 := by
  let gamma := gaugePhysicalValueAccuracy tolerance
  have hgamma := gaugePhysicalValueAccuracy_spec tolerance ht
  obtain ⟨r,hout,hrun,hbeta,hparameters,hcertificate,hphase⟩ := automaticPhysicalPoissonFromGap_correct
    v hv hu hp source hs bounds hb gap hgap B hB hg hoff gamma hgamma.1
  refine ⟨r,hout,hrun,hbeta,hparameters,hcertificate,?_⟩
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  let q := preparedPeriodicReference v hv hu source hs r.preparation.prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (r.preparation.prepared.derivativeBounds 1) (r.preparation.prepared.derivativeBounds 2) eta collar.1 B hB (gap : ℝ)
    (Rat.cast_pos.mpr hgap) hg hoff margin
  dsimp only
  intro X
  have hreference := sourceReferencePhysicalValue_error v hv hu hp source hs bounds hb r.preparation.prepared hrun
    eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin X gamma hgamma.1
  exact sourceGaugePhysicalValue_error source gap r q spec.2.1.1 spec.1 (fun x => (spec.2.1.2 x).1)
    X tolerance ht (hphase X) hreference

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
