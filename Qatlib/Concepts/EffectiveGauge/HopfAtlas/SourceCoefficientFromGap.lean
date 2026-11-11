/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCoefficientGrid
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierPeriodExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Source Coefficient From Gap

Hopf Atlas constructions for Effective Gauge.
Defines `sourceFourierCoefficientFromGap`.
Proves `sourceFourierCoefficientFromGap_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of source Fourier Coefficient From Gap in the Hopf Atlas construction. -/
def sourceFourierCoefficientFromGap (source : RationalJetSource) (bounds : ℕ → ℚ)
    (gap : ℚ) (M : ℕ) (s ell : ℚ) (k : SpatialFrequency) (d : ℚ) :
    Option (CachedMeanPreparation × RationalConnectionGridData × (Fin 3 → RationalCircleSample)) :=
  (cachedMeanPreparationRun source bounds).bind (fun prepared =>
    (sourceFourierCoefficientExecution source prepared (referenceUnitCollar gap) M s
      (fourierPeriodExecution ell) k d).map (fun result => (prepared,result)))

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- The original source, original rational gap and finite numerical
parameters suffice: neither an external reference nor a pi oracle is input. -/
theorem sourceFourierCoefficientFromGap_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (gap : ℚ) (hgap : 0<gap) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (M : ℕ) (hM : 0<M) (s : ℚ) (hspos : 0<s)
    (k : SpatialFrequency) (N : ℕ) (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (d : ℚ) (hdpos : 0<d) (hd1 : d ≤ 1) (ell : ℚ) (hellpos : 0<ell)
    (hell : 3*(N : ℝ)*(ell : ℝ) ≤ (d : ℝ)/2) :
    ∃ prepared data out, cachedMeanPreparationRun source bounds=some prepared ∧
      sourceFourierCoefficientFromGap source bounds gap M s ell k d=some (prepared,data,out) ∧
      data.map Prod.fst=sourceMeanGrid M ∧
      let eta := referenceUnitCollar gap
      let collar := referenceUnitCollar_spec gap hgap
      let margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
        have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
        simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
      let q := preparedPeriodicReference v hv hu source hs prepared eta
      let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
        (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta collar.1 B hB (gap : ℝ)
        (Rat.cast_pos.mpr hgap) hg hoff margin
      let cache := materializeReferencePreparation eta prepared
      ∀ j, ‖normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k-rationalCircleCast (out j)‖ ≤
        3*((cache.connectionBounds[1] : ℝ)+7*(N : ℝ)*(cache.connectionBounds[0] : ℝ))/(M : ℝ)+
          ((s : ℝ)+((cache.connectionBounds[0] : ℝ)+(s : ℝ))*(d : ℝ)) := by
  let eta := referenceUnitCollar gap
  have collar := referenceUnitCollar_spec gap hgap
  have margin : 7*(eta : ℝ) ≤ (gap : ℝ)/2 := by
    have h : ((7*eta : ℚ) : ℝ) ≤ ((gap/2 : ℚ) : ℝ) := Rat.cast_le.mpr collar.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  have he1 : eta ≤ 1/2 := by linarith [collar.2.1]
  obtain ⟨prepared,hrun,hlen,hlabels,hphys,hunit,hsector⟩ := cachedMeanPreparationRun_correct
    v hv hu hp source hs bounds hb eta collar.1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap) hg hoff margin
  obtain ⟨data,out,hout,hindices,herror⟩ := sourceFourierCoefficientExecution_error v hv hu hp
    source hs bounds hb prepared hrun eta collar.1 he1 B hB (gap : ℝ) (Rat.cast_pos.mpr hgap)
    hg hoff margin M hM s (fourierPeriodExecution ell) hspos k N hk d hdpos hd1 (ell : ℝ)
    (fourierPeriodExecution_error ell hellpos) hell
  refine ⟨prepared,data,out,hrun,?_,hindices,herror⟩
  change (cachedMeanPreparationRun source bounds).bind _=some (prepared,data,out)
  rw [hrun,Option.bind_some]
  change (sourceFourierCoefficientExecution source prepared eta M s (fourierPeriodExecution ell) k d).map _=_
  rw [hout,Option.map_some]

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
