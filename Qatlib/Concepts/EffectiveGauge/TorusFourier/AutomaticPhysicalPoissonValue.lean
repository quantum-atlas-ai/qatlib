/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PhysicalPoissonPhaseValueError
import Qatlib.Concepts.EffectiveGauge.TorusFourier.AutomaticPoissonValue

set_option backward.isDefEq.respectTransparency false

/-!
# Automatic Physical Poisson Value

Torus Fourier constructions for Effective Gauge.
Defines `physicalPoissonValueTolerance`, `automaticPhysicalPoissonFromGap`.
Proves `physicalPoissonValueTolerance_spec`, `automaticPhysicalPoissonFromGap_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of physical Poisson Value Tolerance in the Torus Fourier construction. -/
def physicalPoissonValueTolerance (tolerance : ℚ) : ℚ := min (1/64) (tolerance/4)

/-- Definition of automatic Physical Poisson From Gap in the Torus Fourier construction. -/
def automaticPhysicalPoissonFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap tolerance : ℚ) : Option GeneralPoissonValueState :=
  automaticGeneralPoissonFromGap source bounds gap (physicalPoissonValueTolerance tolerance)

/-- Original `physicalPoissonValueTolerance_spec` guarantee for the `AutomaticPhysicalPoissonValue` construction; the complete source hypotheses are retained. -/
theorem physicalPoissonValueTolerance_spec (tolerance : ℚ) (ht : 0<tolerance) :
    0<physicalPoissonValueTolerance tolerance ∧ physicalPoissonValueTolerance tolerance ≤ 1/64 ∧
      physicalPoissonValueTolerance tolerance ≤ tolerance/4 := by
  exact ⟨lt_min (by norm_num) (div_pos ht (by norm_num)),min_le_left _ _,min_le_right _ _⟩

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- Fully original-source construction and source-free evaluation at any
rational physical X, targeting chi(X/L)-chi(0) of the same reference. -/
theorem automaticPhysicalPoissonFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ result, automaticPhysicalPoissonFromGap source bounds gap tolerance=some result ∧
      cachedMeanPreparationRun source bounds=some result.preparation.prepared ∧
      result.beta=rationalPoissonBetaList result.preparation.coefficients ∧
      result.preparation.HasParameters (referenceUnitCollar gap) (physicalPoissonValueTolerance tolerance) ∧
      result.preparation.NumericalCertificate (physicalPoissonValueTolerance tolerance) ∧
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
      ∀ X : Fin 3 → ℚ,
        |(generalPoissonPhysicalPhaseValue result X tolerance : ℝ)-
          physicalPoissonPhase q spec.2.1.1 spec.1 (rationalSpatialPoint X)| ≤ (tolerance : ℝ)/2 := by
  let tau := physicalPoissonValueTolerance tolerance
  have htau := physicalPoissonValueTolerance_spec tolerance ht
  obtain ⟨r,hout,hrun,hbeta,hparameters,hcertificate,hvalue⟩ := automaticGeneralPoissonFromGap_correct
    v hv hu hp source hs bounds hb gap hgap B hB hg hoff tau htau.1 htau.2.1
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
  have hC6 (j i : Fin 3) (x : SpatialPoint) (_hx : InUnitCube x) :
      ‖spatialWordPartial (normalizedConnectionReal q j) (List.replicate 6 i) x‖ ≤
        (r.preparation.referenceCache.connectionBounds[6] : ℝ) := by
    rw [hparameters.1]
    exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb r.preparation.prepared hrun
      eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin 6 (List.replicate 6 i) (by simp) j x
  dsimp only
  intro X
  have h := generalPoissonPhysicalPhaseValue_error r q spec.2.1.1 spec.1 hC6 tau hvalue X tolerance ht
  have htauR : (tau : ℝ) ≤ (tolerance : ℝ)/4 := by exact_mod_cast htau.2.2
  exact h.trans (by have htR : (0 : ℝ)<tolerance := Rat.cast_pos.mpr ht; linarith)

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
