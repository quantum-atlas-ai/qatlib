/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CoefficientGridExecution
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceFourierCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Source Coefficient Grid

Hopf Atlas constructions for Effective Gauge.
Proves `sourceFourierCoefficientExecution_error`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Actual source samples, actual rational modes, actual rational accumulator,
and the true Fourier integral refer to the identical prepared reference. -/
theorem sourceFourierCoefficientExecution_error (v : SpatialPoint → SpatialPoint)
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
    (k : SpatialFrequency) (N : ℕ) (hk : ∀ i, |(k i : ℝ)| ≤ (N : ℝ))
    (d : ℚ) (hdpos : 0<d) (hd1 : d ≤ 1) (ell : ℝ)
    (hl : |(length : ℝ)-physicalPeriod| ≤ ell) (hell : 3*(N : ℝ)*ell ≤ (d : ℝ)/2) :
    let q := preparedPeriodicReference v hv hu source hs prepared eta
    let spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
      (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
    let cache := materializeReferencePreparation eta prepared
    let C0 := (cache.connectionBounds[0] : ℝ)
    let C1 := (cache.connectionBounds[1] : ℝ)
    ∃ data out, sourceFourierCoefficientExecution source prepared eta M s length k d=some (data,out) ∧
      data.map Prod.fst=sourceMeanGrid M ∧ ∀ j,
      ‖normalizedConnectionFourierCoefficient q spec.2.1.1 spec.1 j k-rationalCircleCast (out j)‖ ≤
        3*(C1+7*(N : ℝ)*C0)/(M : ℝ)+((s : ℝ)+(C0+(s : ℝ))*(d : ℝ)) := by
  dsimp only
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  have spec := sourcePeriodicReference_spec v hv hu hp (originalFirstJetPair source 0)
    (OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs))
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  have hq : ContDiff ℝ ∞ q := spec.2.1.1
  let cache := materializeReferencePreparation eta prepared
  let C0 : ℝ := cache.connectionBounds[0]
  let C1 : ℝ := cache.connectionBounds[1]
  let sample := fun index => sourceConnectionSampling source prepared eta (sourceMeanUnitPoint M index) s
  have hsample (index : SourceMeanIndex) : ∃ out, sample index=some out ∧ ∀ j,
      |(out j : ℝ)-normalizedConnectionReal q j (rationalSpatialPoint (sourceMeanUnitPoint M index))| ≤ (s : ℝ)/2 :=
    sourceConnectionSampling_error v hv hu hp source hs bounds hb prepared hrun eta he he1 B hB mu hm
      hg hoff hmargin (sourceMeanUnitPoint M index) s hspos
  have hnode (index : SourceMeanIndex) (j : Fin 3) :
      ‖((connectionGridNode sample index j : ℚ) : ℂ)-normalizedConnectionComplex q j
        (rationalSpatialPoint (sourceMeanUnitPoint M index))‖ ≤ (s : ℝ) := by
    obtain ⟨value,hvalue,herror⟩ := hsample index
    simp only [connectionGridNode,hvalue,Option.getD_some]
    change ‖((value j : ℚ) : ℂ)-((normalizedConnectionReal q j
      (rationalSpatialPoint (sourceMeanUnitPoint M index)) : ℝ) : ℂ)‖ ≤ (s : ℝ)
    rw [← Complex.ofReal_ratCast,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact (herror j).trans (by have hsR : (0 : ℝ)<s := Rat.cast_pos.mpr hspos; linarith)
  have hC (r : Fin 7) (w : List (Fin 3)) (hw : w.length=r.val) (j : Fin 3) (x : SpatialPoint) :
      ‖spatialWordPartial (normalizedConnectionComplex q j) w x‖ ≤ (cache.connectionBounds[r.val] : ℝ) := by
    change ‖spatialWordPartial (fun y => Complex.ofRealCLM (normalizedConnectionReal q j y)) w x‖ ≤ _
    rw [spatialWordPartial_clm Complex.ofRealCLM (normalizedConnectionReal q j)
      (contDiff_normalizedConnectionReal q hq j)]
    change ‖((spatialWordPartial (normalizedConnectionReal q j) w x : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact materializeReferencePreparation_connection_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin r w hw j x
  have hC0 (j : Fin 3) (x : SpatialPoint) : ‖normalizedConnectionComplex q j x‖ ≤ C0 :=
    hC 0 [] rfl j x
  have hC1 (j : Fin 3) (x : SpatialPoint) (i : Fin 3) :
      ‖spatialWordPartial (normalizedConnectionComplex q j) [i] x‖ ≤ C1 := hC 1 [i] rfl j x
  have hC0pos : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0 0)
  have hC1pos : 0 ≤ C1 := (norm_nonneg _).trans (hC1 0 0 0)
  let values := connectionGridNode sample
  let data := (sourceMeanGrid M).map (fun index => (index,values index))
  let out := rationalFourierCoefficientsOfData M length k d data
  have hdata : connectionGridExecution sample (sourceMeanGrid M)=some data :=
    connectionGridExecution_eq_map sample _ (fun index _ => ⟨_,(hsample index).choose_spec.1⟩)
  refine ⟨data,out,?_,?_,?_⟩
  · change (connectionGridExecution sample (sourceMeanGrid M)).map _=some (data,out)
    rw [hdata]
    rfl
  · simp only [data,List.map_map,Function.comp_def,List.map_id_fun']
    rfl
  · intro j
    change ‖normalizedConnectionFourierCoefficient q hq spec.1 j k-
      rationalCircleCast (rationalFourierCoefficientsOfData M length k d
        ((sourceMeanGrid M).map (fun index => (index,values index))) j)‖ ≤ _
    rw [rationalFourierCoefficientsOfData_cast]
    apply sampledFourierCoefficientGrid_error M hM (normalizedConnectionComplex q j)
      (contDiff_normalizedConnectionComplex q hq j) (unitPeriodic_normalizedConnectionComplex q hq spec.1 j)
      k N hk C0 C1 hC0pos hC1pos (fun x _ => hC0 j x) (fun x _ i => hC1 j x i)
    · intro a _ b _ c _
      have he' := hnode (a,b,c) j
      rwa [sourceMeanUnitPoint_cast] at he'
    · intro a ha b hb' c hc
      have hmem := (sourceMeanGrid_mem M (a,b,c)).mpr ⟨ha,hb',hc⟩
      have hu' := sourceMeanUnitPoint_mem M hM (a,b,c) hmem
      have hk' : ∀ i, |((-k) i : ℝ)| ≤ (N : ℝ) := by
        intro i
        simpa only [Pi.neg_apply,Int.cast_neg,abs_neg] using hk i
      have he' := rationalFourierMode_error length (-k) (sourceMeanUnitPoint M (a,b,c))
        d hdpos hd1 N hk' hu' ell hl
      rw [sourceMeanUnitPoint_cast] at he'
      exact he'.trans (by linarith)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
