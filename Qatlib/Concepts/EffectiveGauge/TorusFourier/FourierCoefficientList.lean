/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCoefficientGrid

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Coefficient List

Torus Fourier constructions for Effective Gauge.
Defines `RationalFourierCoefficientList`, `sourceFourierCoefficientListExecution`.
Proves `sourceFourierCoefficientListExecution_error`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Rational Fourier Coefficient List in the Torus Fourier construction. -/
abbrev RationalFourierCoefficientList := List (SpatialFrequency × (Fin 3 → RationalCircleSample))

/-- The source grid is outside the frequency loop. Coefficient evaluation
reads the stored data and does not invoke a source sampler again. -/
def sourceFourierCoefficientListExecution (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (M : ℕ) (s length d : ℚ) (frequencies : List SpatialFrequency) :
    Option (RationalConnectionGridData × RationalFourierCoefficientList) :=
  (connectionGridExecution
    (fun index => sourceConnectionSampling source prepared eta (sourceMeanUnitPoint M index) s)
    (sourceMeanGrid M)).map (fun data => (data,frequencies.map
      (fun k => (k,rationalFourierCoefficientsOfData M length k d data))))

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- Suppose a smooth, physically periodic unit field is constant on the part of the fundamental cube
outside `B`, and `B` is contained in the cube at least `mu > 0` from the boundary, with
`7*eta ≤ mu/2`. With accurate
all-order jets, valid positive-order bounds, and a successful cached mean preparation, take a positive
grid size `M`, a positive sampling tolerance `s`, and requested frequencies bounded by `N` in every
coordinate. If the period error is at most `ell` with `3*N*ell ≤ d/2`, `0 < d ≤ 1`, and
`0 < eta ≤ 1/2`, the run returns the sampled grid in grid order and coefficients in the requested
order. Every requested frequency has an entry whose componentwise error against the Fourier
coefficients of the reference's normalized connection is at most
`3*(C1+7*N*C0)/M + s + (C0+s)*d`, using the prepared bounds `C0` and `C1`. -/
theorem sourceFourierCoefficientListExecution_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z∈B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z∈B, ∀ a, OnCubeBoundary a → mu ≤ ‖z-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a∉B → b∉B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (M : ℕ) (hM : 0<M) (s length : ℚ) (hspos : 0<s)
    (frequencies : List SpatialFrequency) (N : ℕ)
    (hk : ∀ k∈frequencies, ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (d : ℚ) (hdpos : 0<d) (hd1 : d ≤ 1) (ell : ℝ)
    (hl : |(length : ℝ)-physicalPeriod| ≤ ell) (hell : 3*(N : ℝ)*ell ≤ (d : ℝ)/2) :
    let q := preparedPeriodicReference v hv hu source hs prepared eta
    let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
    let cache := materializeReferencePreparation eta prepared
    let C0 := (cache.connectionBounds[0] : ℝ)
    let C1 := (cache.connectionBounds[1] : ℝ)
    ∃ data coefficients,
      sourceFourierCoefficientListExecution source prepared eta M s length d frequencies=some (data,coefficients) ∧
      data.map Prod.fst=sourceMeanGrid M ∧ coefficients.map Prod.fst=frequencies ∧
      ∀ k∈frequencies, ∃ out, (k,out)∈coefficients ∧ ∀ j,
        ‖normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k-rationalCircleCast (out j)‖ ≤
          3*(C1+7*(N : ℝ)*C0)/(M : ℝ)+((s : ℝ)+(C0+(s : ℝ))*(d : ℝ)) := by
  dsimp only
  let sample := fun index => sourceConnectionSampling source prepared eta (sourceMeanUnitPoint M index) s
  have hzero : ∀ i, |((0 : SpatialFrequency) i : ℝ)| ≤ (N : ℝ) := by
    intro i
    simpa only [Pi.zero_apply,Int.cast_zero,abs_zero] using (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  obtain ⟨data0,out0,hsingle0,hindices0,herror0⟩ := sourceFourierCoefficientExecution_error
    v hv hu hp source hs bounds hb prepared hrun eta he he1 B hB mu hm hg hoff hmargin
    M hM s length hspos 0 N hzero d hdpos hd1 ell hl hell
  have hgrid : connectionGridExecution sample (sourceMeanGrid M)=some data0 := by
    change (connectionGridExecution sample (sourceMeanGrid M)).map _=some (data0,out0) at hsingle0
    cases heq : connectionGridExecution sample (sourceMeanGrid M) with
    | none => simp only [heq,Option.map_none,reduceCtorEq] at hsingle0
    | some data =>
      rw [heq,Option.map_some,Option.some.injEq] at hsingle0
      have hedata : data=data0 := congrArg Prod.fst hsingle0
      exact congrArg some hedata
  let coefficients := frequencies.map (fun k => (k,rationalFourierCoefficientsOfData M length k d data0))
  refine ⟨data0,coefficients,?_,hindices0,?_,?_⟩
  · change (connectionGridExecution sample (sourceMeanGrid M)).map _=some (data0,coefficients)
    rw [hgrid]
    rfl
  · simp only [coefficients,List.map_map,Function.comp_def,List.map_id_fun']
    rfl
  · intro k hkmem
    obtain ⟨data,out,hsingle,hindices,herror⟩ := sourceFourierCoefficientExecution_error
      v hv hu hp source hs bounds hb prepared hrun eta he he1 B hB mu hm hg hoff hmargin
      M hM s length hspos k N (hk k hkmem) d hdpos hd1 ell hl hell
    change (connectionGridExecution sample (sourceMeanGrid M)).map _=some (data,out) at hsingle
    rw [hgrid,Option.map_some,Option.some.injEq] at hsingle
    have heout : rationalFourierCoefficientsOfData M length k d data0=out := congrArg Prod.snd hsingle
    refine ⟨rationalFourierCoefficientsOfData M length k d data0,?_,?_⟩
    · exact List.mem_map.mpr ⟨k,hkmem,rfl⟩
    · rw [heout]
      exact herror

end
end Qatlib.Concepts.EffectiveGauge.TorusFourier
