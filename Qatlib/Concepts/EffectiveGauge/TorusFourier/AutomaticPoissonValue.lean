/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonPreparedValueError

set_option backward.isDefEq.respectTransparency false

/-!
# Automatic Poisson Value

Torus Fourier constructions for Effective Gauge.
Proves `automaticGeneralPoissonFromGap_correct`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Quaternion
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original-source success and uniform point accuracy for the actual saved
finite Poisson state. No lift, Fourier coefficient, modulus or solution
oracle is supplied; evaluation accepts only the saved state and address. -/
theorem automaticGeneralPoissonFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) (ht1 : tolerance ≤ 1/64) :
    ∃ result, automaticGeneralPoissonFromGap source bounds gap tolerance=some result ∧
      cachedMeanPreparationRun source bounds=some result.preparation.prepared ∧
      result.beta=rationalPoissonBetaList result.preparation.coefficients ∧
      result.preparation.HasParameters (referenceUnitCollar gap) tolerance ∧
      result.preparation.NumericalCertificate tolerance ∧
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
      ∀ address : Fin 3 → ℚ,
        |(generalPoissonStateValue result address : ℝ)-
          normalizedConnectionPoisson q spec.2.1.1 spec.1 (rationalSpatialPoint address)| ≤ (tolerance : ℝ)/2 := by
  obtain ⟨r,hout,hrun,hparameters,hcertificate,hcoefficients⟩ := automaticPoissonCoefficientsFromGap_correct
    v hv hu hp source hs bounds hb gap hgap B hB hg hoff tolerance ht ht1
  let result := materializeGeneralPoissonValueState r
  refine ⟨result,?_,hrun,rfl,hparameters,hcertificate,?_⟩
  · change (automaticPoissonCoefficientsFromGap source bounds gap tolerance).map _=some result
    rw [hout,Option.map_some]
  · let eta := referenceUnitCollar gap
    have collar := referenceUnitCollar_spec gap hgap
    have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
    have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
      have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
      simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
    let q := preparedPeriodicReference v hv hu source hs r.prepared eta
    have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (r.prepared.derivativeBounds 1) (r.prepared.derivativeBounds 2) eta collar.1 B hB (gap : ℝ)
      (Rat.cast_pos.mpr hgap) hg hoff margin
    have hC0 (j : Fin 3) (x : SpatialPoint) (_hx : InUnitCube x) :
        ‖normalizedConnectionComplex q j x‖ ≤ (r.referenceCache.connectionBounds[0] : ℝ) := by
      rw [hparameters.1]
      change ‖((normalizedConnectionReal q j x : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real]
      exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb r.prepared hrun
        eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin 0 [] rfl j x
    have hC6 (j i : Fin 3) (x : SpatialPoint) (_hx : InUnitCube x) :
        ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤
          (r.referenceCache.connectionBounds[6] : ℝ) := by
      rw [hparameters.1]
      exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb r.prepared hrun
        eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin 6 (List.replicate 6 i) (by simp) j x
    dsimp only
    intro address
    exact poissonPreparedValue_error r eta tolerance ht ht1 hparameters hcertificate q spec.2.1.1 spec.1
      hC0 hC6 hcoefficients address

end Qatlib.Concepts.EffectiveGauge.TorusFourier
