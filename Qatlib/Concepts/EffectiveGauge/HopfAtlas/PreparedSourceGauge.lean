/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceGaugePhysicalValue

set_option backward.isDefEq.respectTransparency false

/-!
# Prepared Source Gauge

Hopf Atlas constructions for Effective Gauge.
Defines `materializeSourceGaugeFromGap`.
Proves `automaticSourceGaugeFromGap_eq`, `materializeSourceGaugeFromGap_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Retain a previously executed mean/derivative preparation. Planning an
H1 grid from its P1/P3 does not require another bound or mean execution. -/
def materializeSourceGaugeFromGap (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (gap tolerance : ℚ) : Option GeneralPoissonValueState :=
  (materializePoissonCoefficientPreparation source prepared (referenceUnitCollar gap)
    (physicalPoissonValueTolerance (gaugePhysicalValueAccuracy tolerance))).map materializeGeneralPoissonValueState

/-- Original `automaticSourceGaugeFromGap_eq` guarantee for the `PreparedSourceGauge` construction; the complete source hypotheses are retained. -/
theorem automaticSourceGaugeFromGap_eq (source : RationalJetSource) (bounds : ℕ → ℚ) (gap tolerance : ℚ) :
    automaticSourceGaugeFromGap source bounds gap tolerance=
      (cachedMeanPreparationRun source bounds).bind (fun prepared => materializeSourceGaugeFromGap source prepared gap tolerance) := by
  unfold automaticSourceGaugeFromGap automaticPhysicalPoissonFromGap automaticGeneralPoissonFromGap
    automaticPoissonCoefficientsFromGap
  cases cachedMeanPreparationRun source bounds <;> rfl

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- Original `materializeSourceGaugeFromGap_correct` guarantee for the `PreparedSourceGauge` construction; the complete source hypotheses are retained. -/
theorem materializeSourceGaugeFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ result, materializeSourceGaugeFromGap source prepared gap tolerance=some result ∧
      result.preparation.prepared=prepared ∧
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
  obtain ⟨r,hout,hrunr,hbeta,hparameters,hcertificate,hvalue⟩ := automaticSourceGaugeFromGap_correct
    v hv hu hp source hs bounds hb gap hgap B hB hg hoff tolerance ht
  have hsame : r.preparation.prepared=prepared := Option.some.inj (hrunr.symm.trans hrun)
  have hmaterialize : materializeSourceGaugeFromGap source prepared gap tolerance=some r := by
    rw [automaticSourceGaugeFromGap_eq,hrun,Option.bind_some] at hout
    exact hout
  exact ⟨r,hmaterialize,hsame,hbeta,hparameters,hcertificate,hvalue⟩

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
