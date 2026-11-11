/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PhysicalPoissonAddress
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SpatialNormLipschitz
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceConnectionSampling

set_option backward.isDefEq.respectTransparency false

/-!
# Physical Reference Value

Hopf Atlas constructions for Effective Gauge.
Defines `rationalPhysicalAddressAccuracy`, `referencePhysicalValueAccuracy`, `referencePhysicalValueExecution`.
Proves `rationalPhysicalAddressAccuracy_eq`, `referencePhysicalValueExecution_error`, `sourceReferencePhysicalValue_error`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Reuse the finite address planner with derivative majorant |D|. -/
def rationalPhysicalAddressAccuracy (D : ℚ) (X : Fin 3 → ℚ) (tolerance : ℚ) : ℚ :=
  physicalPoissonAddressAccuracy (D/156) X tolerance

/-- Original `rationalPhysicalAddressAccuracy_eq` guarantee for the `PhysicalReferenceValue` construction; the complete source hypotheses are retained. -/
theorem rationalPhysicalAddressAccuracy_eq (D : ℚ) (X : Fin 3 → ℚ) (tolerance : ℚ) :
    rationalPhysicalAddressAccuracy D X tolerance=
      min 1 (tolerance/((|D|+1)*(rationalAddressMagnitude X+1))) := by
  simp only [rationalPhysicalAddressAccuracy,physicalPoissonAddressAccuracy,abs_div]
  norm_num
  rw [show (156 : ℚ)*(|D|/156)=|D| by ring]

/-- Definition of reference Physical Value Accuracy in the Hopf Atlas construction. -/
def referencePhysicalValueAccuracy (tolerance : ℚ) : ℚ := min (1/4) (tolerance/4)

/-- Definition of reference Physical Value Execution in the Hopf Atlas construction. -/
def referencePhysicalValueExecution (value : (Fin 3 → ℚ) → ℚ → Option (Quaternion ℚ))
    (R1 : ℚ) (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  let ell := rationalPhysicalAddressAccuracy R1 X tolerance
  value (rationalUnitWrap (rationalPhysicalPoissonAddress X ell)) (referencePhysicalValueAccuracy tolerance)

/-- Definition of source Reference Physical Value in the Hopf Atlas construction. -/
def sourceReferencePhysicalValue (source : RationalJetSource) (prepared : CachedMeanPreparation)
    (eta : ℚ) (X : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  referencePhysicalValueExecution (preparedReferenceValueProgram source prepared eta)
    (materializeReferencePreparation eta prepared).corrected.correctedBounds[1] X tolerance

noncomputable section
open Set
open scoped ContDiff Quaternion

/-- Original `referencePhysicalValueExecution_error` guarantee for the `PhysicalReferenceValue` construction; the complete source hypotheses are retained. -/
theorem referencePhysicalValueExecution_error
    (value : (Fin 3 → ℚ) → ℚ → Option (Quaternion ℚ))
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q) (R1 : ℚ)
    (hR : ∀ x j, ‖spatialWordPartial (fun y => q (physicalPeriod • y)) [j] x‖ ≤ (R1 : ℝ))
    (hvalue : ∀ a : Fin 3 → ℚ, (∀ j, (a j : ℝ)∈Icc 0 1) → ∀ t : ℚ, 0<t → t ≤ 1 →
      ∃ out, value a t=some out ∧
        ‖rationalQuaternionCast out-q (physicalPeriod • rationalSpatialPoint a)‖ ≤ (t : ℝ))
    (X : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ out, referencePhysicalValueExecution value R1 X tolerance=some out ∧
      ‖rationalQuaternionCast out-q (rationalSpatialPoint X)‖ ≤ (tolerance : ℝ)/2 := by
  let ell := rationalPhysicalAddressAccuracy R1 X tolerance
  let a := rationalPhysicalPoissonAddress X ell
  let x := rationalSpatialPoint a
  let y := physicalPeriod⁻¹ • rationalSpatialPoint X
  let Q : QuaternionField := fun z => q (physicalPeriod • z)
  let D : ℝ := |(R1 : ℝ)|
  let S : ℝ := rationalAddressMagnitude X
  let rho := referencePhysicalValueAccuracy tolerance
  have hrho : 0<rho ∧ rho ≤ 1 ∧ rho ≤ tolerance/4 := by
    refine ⟨lt_min (by norm_num) (div_pos ht (by norm_num)),?_,min_le_right _ _⟩
    exact (min_le_left _ _).trans (by norm_num)
  obtain ⟨out,hout,herror⟩ := hvalue (rationalUnitWrap a) (rationalUnitWrap_mem a) rho hrho.1 hrho.2.1
  have hQp : IsUnitPeriodicField Q := periodicField_rescale_unit q hp
  change ‖rationalQuaternionCast out-Q (rationalSpatialPoint (rationalUnitWrap a))‖ ≤ (rho : ℝ) at herror
  rw [rationalUnitWrap_periodic Q hQp a] at herror
  have hD : 0 ≤ D := abs_nonneg _
  have hpartial (z : SpatialPoint) (j : Fin 3) :
      ‖fderiv ℝ Q z (EuclideanSpace.single j 1)‖ ≤ D := (hR z j).trans (le_abs_self _)
  have hcoord (j : Fin 3) : |x j-y j| ≤ |(X j : ℝ)| * (ell : ℝ)/30 :=
    rationalPhysicalPoissonAddress_error (R1/156) X tolerance ht j
  have hS : S=|(X 0 : ℝ)|+|(X 1 : ℝ)|+|(X 2 : ℝ)| := by
    simp only [S,rationalAddressMagnitude,Fin.sum_univ_three,Rat.cast_add,Rat.cast_abs]
  have hsum : |x 0-y 0|+|x 1-y 1|+|x 2-y 2| ≤ S*(ell : ℝ)/30 := by
    rw [hS]
    linarith [hcoord 0,hcoord 1,hcoord 2]
  have hbudget : D*S*(ell : ℝ) ≤ (tolerance : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (physicalPoissonAddressAccuracy_budget (R1/156) X tolerance ht)
    push_cast at h
    norm_num [abs_div] at h
    rw [show (156 : ℝ)*(|(R1 : ℝ)|/156)=|(R1 : ℝ)| by ring] at h
    exact h
  have hdist : ‖Q x-Q y‖ ≤ (tolerance : ℝ)/30 := by
    have hglobal := spatial_partial_norm_lipschitz Q (hq.comp (contDiff_id.const_smul physicalPeriod)) D hD hpartial x y
    have h := hglobal.trans (mul_le_mul_of_nonneg_left hsum hD)
    nlinarith
  have htarget : Q y=q (rationalSpatialPoint X) := by
    dsimp only [Q,y]
    rw [smul_smul,mul_inv_cancel₀ physicalPeriod_pos.ne',one_smul]
  refine ⟨out,hout,?_⟩
  rw [← htarget]
  have htri := dist_triangle (rationalQuaternionCast out) (Q x) (Q y)
  simp only [dist_eq_norm] at htri
  have hrhoR : (rho : ℝ) ≤ (tolerance : ℝ)/4 := by exact_mod_cast hrho.2.2
  have htR : (0 : ℝ)<tolerance := Rat.cast_pos.mpr ht
  exact (htri.trans (add_le_add herror hdist)).trans (by linarith)

/-- Original `sourceReferencePhysicalValue_error` guarantee for the `PhysicalReferenceValue` construction; the complete source hypotheses are retained. -/
theorem sourceReferencePhysicalValue_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalAllJetAccurate v source)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds)
    (prepared : CachedMeanPreparation) (hrun : cachedMeanPreparationRun source bounds=some prepared)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (B : Set SpatialPoint)
    (hB : ∀ z ∈ B, InFundamentalCube z) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ z ∈ B, ∀ b, OnCubeBoundary b → mu ≤ ‖z-b‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (X : Fin 3 → ℚ) (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ out, sourceReferencePhysicalValue source prepared eta X tolerance=some out ∧
      ‖rationalQuaternionCast out-preparedPeriodicReference v hv hu source hs prepared eta
        (rationalSpatialPoint X)‖ ≤ (tolerance : ℝ)/2 := by
  let original := originalFirstJetPair source 0
  have hs0 := OriginalFirstJetAccurate.legacy v source (OriginalAllJetAccurate.first v source hs)
  let q := preparedPeriodicReference v hv hu source hs prepared eta
  let Q : QuaternionField := fun x => q (physicalPeriod • x)
  have hspec := sourcePeriodicReference_spec v hv hu hp original hs0
    (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) eta he B hB mu hm hg hoff hmargin
  have hq : ContDiff ℝ ∞ q := hspec.2.1.1
  have hQ : ContDiff ℝ ∞ Q := hq.comp (contDiff_id.const_smul physicalPeriod)
  have hQu : ∀ x, ‖Q x‖=1 := fun x => (hspec.2.1.2 _).1
  have hQp : IsUnitPeriodicField Q := periodicField_rescale_unit q hspec.1
  obtain ⟨packet,labels,hpacket,hlen,hlabels,hphys,hunit⟩ :=
    sourceFrameBoundRun_correct v hv hu hp bounds hb
  have hsame : (packet,labels)=(prepared.derivativeBounds,prepared.boundRequests) :=
    Option.some.inj (hpacket.symm.trans (cachedMeanPreparationRun_boundExecution source bounds prepared hrun))
  have hcache : packet=prepared.derivativeBounds := congrArg Prod.fst hsame
  rw [hcache] at hphys
  have hzero : InFundamentalCube (0 : SpatialPoint) := by
    intro j
    exact ⟨by simp,by simpa using physicalPeriod_pos.le⟩
  have hm1 : 0 ≤ prepared.derivativeBounds 1 := by
    have ht' := (norm_nonneg _).trans (hphys 1 [0] rfl 0 hzero)
    exact_mod_cast ht'
  have hm2 : 0 ≤ prepared.derivativeBounds 2 := by
    have ht' := (norm_nonneg _).trans (hphys 2 [0,0] rfl 0 hzero)
    exact_mod_cast ht'
  have hb12 : SourceRescalingBounds v (prepared.derivativeBounds 1 : ℝ)
      (prepared.derivativeBounds 2 : ℝ) := by
    constructor
    · intro x hx j
      exact hphys 1 [j] rfl x hx
    · intro x hx j
      exact hphys 2 [j,0] rfl x hx
  have hvalue (b : Fin 3 → ℚ) (hb0 : ∀ j, (b j : ℝ)∈Icc 0 1)
      (t : ℚ) (ht0 : 0<t) (ht1 : t ≤ 1) :
      ∃ out, preparedReferenceValueProgram source prepared eta b t=some out ∧
        ‖rationalQuaternionCast out-Q (rationalSpatialPoint b)‖ ≤ (t : ℝ) := by
    exact sourceReferenceValue_error v hv hu hp original hs0
      (prepared.derivativeBounds 1) (prepared.derivativeBounds 2) hm1 hm2 hb12
      B hB mu hm hg hoff eta he he1 hmargin b hb0 t ht0 ht1
  let R1 := (materializeReferencePreparation eta prepared).corrected.correctedBounds[1]
  have hR (x : SpatialPoint) (j : Fin 3) : ‖spatialWordPartial Q [j] x‖ ≤ (R1 : ℝ) :=
    materializeReferencePreparation_reference_bound v hv hu hp source hs bounds hb prepared hrun
      eta he he1 B hB mu hm hg hoff hmargin 1 [j] rfl x
  exact referencePhysicalValueExecution_error (preparedReferenceValueProgram source prepared eta)
    q hq hspec.1 R1 hR hvalue X tolerance ht

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
