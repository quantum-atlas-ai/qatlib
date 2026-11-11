/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CisApproximation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ZeroReference

set_option backward.isDefEq.respectTransparency false

/-!
# The complete rational reference-value program targets one periodic field

The standalone entry prepares a chart once, then passes it through every
branch. Its equation below is a value-only view, not a source-call ledger.
No lift, phase, circle or elementary-function oracle is an input.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for reference Value Boundary in the Hopf Atlas construction. -/
abbrev referenceValueBoundary (eta : ℚ) (a : Fin 3 → ℚ) : Prop :=
  a 1 ≤ eta ∨ 1-eta ≤ a 1 ∨ a 2 ≤ eta ∨ 1-eta ≤ a 2 ∨ 1-eta/4 ≤ a 0

/-- Definition of source Reference Angle On Chart in the Hopf Atlas construction. -/
def sourceReferenceAngleOnChart (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (chart : SeedChart) (eta x y z tolerance : ℚ) : Option RationalReferenceAngleResult :=
  let Q := ((7*m1)^2+49*m2)/2
  (rationalPhaseLog (terminalCircleSamplesOnChart source m1 m2 z chart) y Q (tolerance/32)).map (fun log =>
    let rho := rationalSmoothStep ((x-(1-eta/2))/(eta/4)) (tolerance/(64*(Q+1)))
    ⟨(1-rho.value)*log.value,log.errorBound+rho.error*Q,log,rho⟩)

/-- Original `sourceReferenceAngleOnChart_chosen` guarantee for the `ReferenceValue` construction; the complete source hypotheses are retained. -/
theorem sourceReferenceAngleOnChart_chosen (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 eta x y z tolerance : ℚ) :
    sourceReferenceAngleOnChart source m1 m2 (chosenOriginChart (rescaledSpinSamples source m1 m2)) eta x y z tolerance=
      sourceReferenceAngle source m1 m2 eta x y z tolerance := rfl

/-- Definition of reference Angle Value in the Hopf Atlas construction. -/
def referenceAngleValue (seed : Quaternion ℚ) (tolerance : ℚ) (angle : RationalReferenceAngleResult) : Quaternion ℚ :=
  rationalCircleQuaternion (rationalCis angle.value (tolerance/16)).value*seed

/-- Definition of source Reference Transition Value in the Hopf Atlas construction. -/
def sourceReferenceTransitionValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  (sourceReferenceAngle source m1 m2 eta (a 0) (a 1) (a 2) tolerance).map
    (referenceAngleValue (originSeedApproximation (rescaledSpinSamples source m1 m2) (tolerance/16)) tolerance)

/-- Definition of source Reference Value On Chart in the Hopf Atlas construction. -/
def sourceReferenceValueOnChart (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (chart : SeedChart) (eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  let samples := rescaledSpinSamples source m1 m2
  if m1=0 then some (originSeedOnChart samples chart (tolerance/8))
  else if referenceValueBoundary eta a then some (originSeedOnChart samples chart (tolerance/8))
  else if a 0 ≤ 1-eta/2 then some (rescaledLineOnChart source m1 m2 chart a tolerance)
  else (sourceReferenceAngleOnChart source m1 m2 chart eta (a 0) (a 1) (a 2) tolerance).map
    (referenceAngleValue (originSeedOnChart samples chart (tolerance/16)) tolerance)

/-- Definition of source Reference Value in the Hopf Atlas construction. -/
def sourceReferenceValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  let chart := chosenOriginChart (rescaledSpinSamples source m1 m2)
  sourceReferenceValueOnChart source m1 m2 chart eta a tolerance

/-- The original input supplies a positive physical gap. The finite program
computes its own admissible unit collar instead of asking for another oracle. -/
def sourceReferenceValueFromGap (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 gap : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  sourceReferenceValue source m1 m2 (referenceUnitCollar gap) a tolerance

/-- Equational view for error analysis. The standalone implementation above
retains one chart preparation; re-evaluating this RHS is not a fee model. -/
theorem sourceReferenceValue_eq (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 eta : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    sourceReferenceValue source m1 m2 eta a tolerance=
      if m1=0 then some (originSeedApproximation (rescaledSpinSamples source m1 m2) (tolerance/8))
      else if referenceValueBoundary eta a then some (originSeedApproximation (rescaledSpinSamples source m1 m2) (tolerance/8))
      else if a 0 ≤ 1-eta/2 then some (rescaledLineValue source m1 m2 a tolerance)
      else sourceReferenceTransitionValue source m1 m2 eta a tolerance := by
  simp only [sourceReferenceValue,sourceReferenceValueOnChart,rescaledLineOnChart_chosen,
    sourceReferenceAngleOnChart_chosen,sourceReferenceTransitionValue,originSeedApproximation]

noncomputable section
open scoped Quaternion ContDiff
open Set

/-- Original `product_error` guarantee for the `ReferenceValue` construction; the complete source hypotheses are retained. -/
private theorem product_error (a b p q : ℍ) (d s : ℝ) (hp : ‖p‖=1) (hq : ‖q‖=1)
    (ha : ‖a-p‖ ≤ d) (hb : ‖b-q‖ ≤ s) (hd : d ≤ 1) : ‖a*b-p*q‖ ≤ d+2*s := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans ha
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hb
  have hn : ‖a‖ ≤ 2 := by
    have h := (norm_le_norm_sub_add a p).trans (add_le_add ha hp.le)
    linarith
  have hid : a*b-p*q=a*(b-q)+(a-p)*q := by noncomm_ring
  calc
    _ ≤ ‖a*(b-q)‖+‖(a-p)*q‖ := by rw [hid]; exact norm_add_le _ _
    _ = ‖a‖*‖b-q‖+‖a-p‖ := by rw [norm_mul,norm_mul,hq,mul_one]
    _ ≤ 2*s+d := add_le_add (mul_le_mul hn hb (norm_nonneg _) (by norm_num)) ha
    _ = _ := by ring

/-- The transition branch now returns an actual rational quaternion, with
both finite cis and the nonunit approximate seed included in the error. -/
theorem sourceReferenceTransitionValue_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (a : Fin 3 → ℚ) (ha : ∀ j, (a j : ℝ) ∈ Icc 0 1) (htransition : 1-eta/2 ≤ a 0)
    (tau : ℚ) (ht : 0<tau) (ht1 : tau ≤ 1) :
    ∃ q, sourceReferenceTransitionValue source m1 m2 eta a tau=some q ∧
      ‖rationalQuaternionCast q-sourcePeriodicReference v hv hu source hs m1 m2 eta
        (physicalPeriod • rationalSpatialPoint a)‖ ≤ (tau : ℝ) := by
  obtain ⟨angle,hr,hangle,hbudget⟩ := sourceReferenceTransition_phase_error v hv hu hp source hs m1 m2 hm1 hm2 hb
    B hB mu hm hg hoff eta (a 0) (a 1) (a 2) tau he he1 hmargin (ha 0) (ha 1) (ha 2) htransition ht
  let seed := originSeedApproximation (rescaledSpinSamples source m1 m2) (tau/16)
  let q := referenceAngleValue seed tau angle
  have ht16 : 0<tau/16 := by positivity
  have ht16le : tau/16 ≤ 1 := by linarith
  have hecis := (rationalCis_spec angle.value (tau/16) ht16 ht16le).2.2.1
  have hcis : ‖rationalQuaternionCast (rationalCircleQuaternion (rationalCis angle.value (tau/16)).value)-
      phase (angle.value : ℝ)‖ ≤ (tau : ℝ)/16 := by
    have hbound : ((rationalCis angle.value (tau/16)).error : ℝ) ≤ (((tau/16 : ℚ) : ℝ)) := Rat.cast_le.mpr hecis
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (rationalCis_quaternion_error angle.value (tau/16) ht16 ht16le).trans hbound
  have hseed : ‖rationalQuaternionCast seed-rescaledOriginSeed v source m1 m2‖ ≤ (tau : ℝ)/16 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using rescaledOriginSeed_error v hu source hs m1 m2 (tau/16) ht16
  have hprod : ‖rationalQuaternionCast q-phase (angle.value : ℝ)*rescaledOriginSeed v source m1 m2‖ ≤
      (tau : ℝ)/16+2*((tau : ℝ)/16) := by
    change ‖rationalQuaternionCast (rationalCircleQuaternion (rationalCis angle.value (tau/16)).value*seed)-_‖ ≤ _
    rw [map_mul]
    exact product_error _ _ _ _ _ _ (phase_norm _) (rescaledOriginSeed_spec v hu source hs m1 m2).1 hcis hseed
      (by exact_mod_cast ht16le)
  have hpoint : rationalSpatialPoint ![a 0,a 1,a 2]=rationalSpatialPoint a := by ext j; fin_cases j <;> rfl
  rw [hpoint] at hangle
  refine ⟨q,?_,?_⟩
  · change (sourceReferenceAngle source m1 m2 eta (a 0) (a 1) (a 2) tau).map _=some q
    rw [hr]
    rfl
  · have hbR : (angle.error : ℝ) ≤ (tau : ℝ)/16 := by
      have h : (angle.error : ℝ) ≤ (((tau/16 : ℚ) : ℝ)) := Rat.cast_le.mpr hbudget
      simpa only [Rat.cast_div,Rat.cast_ofNat] using h
    have hsum := (norm_sub_le_norm_sub_add_norm_sub (rationalQuaternionCast q)
      (phase (angle.value : ℝ)*rescaledOriginSeed v source m1 m2)
      (sourcePeriodicReference v hv hu source hs m1 m2 eta (physicalPeriod • rationalSpatialPoint a))).trans
      (add_le_add hprod (hangle.trans hbR))
    have htR : (0 : ℝ)<tau := by exact_mod_cast ht
    linarith


/-- Every valid original source and every requested unit-cube rational point
produce a rational value of the same fixed periodic reference. All guards
succeed; the only oracle supplied is the original spin/derivative source. -/
theorem sourceReferenceValue_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (eta : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (a : Fin 3 → ℚ) (ha : ∀ j, (a j : ℝ) ∈ Icc 0 1) (tau : ℚ) (ht : 0<tau) (ht1 : tau ≤ 1) :
    ∃ q, sourceReferenceValue source m1 m2 eta a tau=some q ∧
      ‖rationalQuaternionCast q-sourcePeriodicReference v hv hu source hs m1 m2 eta
        (physicalPeriod • rationalSpatialPoint a)‖ ≤ (tau : ℝ) := by
  rw [sourceReferenceValue_eq]
  by_cases hz : m1=0
  · rw [if_pos hz]
    subst m1
    refine ⟨originSeedApproximation (rescaledSpinSamples source 0 m2) (tau/8),rfl,?_⟩
    have hb0 : SourceRescalingBounds v 0 (m2 : ℝ) := by simpa only [Rat.cast_zero] using hb
    rw [sourcePeriodicReference_zero_first v hv hu hp source hs m2 eta hb0 he B hB mu hm hg hoff hmargin _
      (scaledUnitPoint_cube _ ha)]
    exact (rescaledOriginSeed_error v hu source hs 0 m2 (tau/8) (by positivity)).trans
      (Rat.cast_le.mpr (by linarith : tau/8 ≤ tau))
  · rw [if_neg hz]
    let u := rationalSpatialPoint a
    let q₀ := rescaledOriginSeed v source m1 m2
    have h₀ : ‖q₀‖=1 := (rescaledOriginSeed_spec v hu source hs m1 m2).1
    have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
    have heR : (0 : ℝ)<eta := by exact_mod_cast he
    have he1R : (eta : ℝ) ≤ 1/2 := by
      have h : (eta : ℝ) ≤ (((1/2 : ℚ) : ℝ)) := Rat.cast_le.mpr he1
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
    have htrans : (a 1 ≤ eta ∨ 1-eta ≤ a 1 ∨ a 2 ≤ eta ∨ 1-eta ≤ a 2) →
        sourcePeriodicReference v hv hu source hs m1 m2 eta (physicalPeriod • u)=q₀ := by
      intro hside
      change periodicReference v hv q₀ h₀ (physicalPeriod*(eta : ℝ)) (physicalPeriod • u)=q₀
      apply unitReference_transverse v hv hu q₀ h₀ (spin_field_periodic hp) (eta : ℝ) heR _ hc
        (rescaledOriginSeed_spec v hu source hs m1 m2).2.1 u ha
      rcases hside with h | h | h | h
      · exact Or.inl (Rat.cast_le.mpr h)
      · apply Or.inr ∘ Or.inl
        have hh : (((1-eta : ℚ) : ℝ)) ≤ (a 1 : ℝ) := Rat.cast_le.mpr h
        simpa only [u,rationalSpatialPoint,PiLp.toLp_apply,Rat.cast_sub,Rat.cast_one] using hh
      · exact Or.inr (Or.inr (Or.inl (Rat.cast_le.mpr h)))
      · apply Or.inr ∘ Or.inr ∘ Or.inr
        have hh : (((1-eta : ℚ) : ℝ)) ≤ (a 2 : ℝ) := Rat.cast_le.mpr h
        simpa only [u,rationalSpatialPoint,PiLp.toLp_apply,Rat.cast_sub,Rat.cast_one] using hh
    by_cases hboundary : referenceValueBoundary eta a
    · rw [if_pos hboundary]
      refine ⟨originSeedApproximation (rescaledSpinSamples source m1 m2) (tau/8),rfl,?_⟩
      have htarget : sourcePeriodicReference v hv hu source hs m1 m2 eta (physicalPeriod • u)=q₀ := by
        rcases hboundary with h | h | h | h | h
        · exact htrans (Or.inl h)
        · exact htrans (Or.inr (Or.inl h))
        · exact htrans (Or.inr (Or.inr (Or.inl h)))
        · exact htrans (Or.inr (Or.inr (Or.inr h)))
        · change periodicReference v hv q₀ h₀ (physicalPeriod*(eta : ℝ)) (physicalPeriod • u)=q₀
          apply unitReference_back v hv hu q₀ h₀ (spin_field_periodic hp) (eta : ℝ) heR he1R _ hc
            (rescaledOriginSeed_spec v hu source hs m1 m2).2.1 u ha
          have hh : (((1-eta/4 : ℚ) : ℝ)) ≤ (a 0 : ℝ) := Rat.cast_le.mpr h
          simpa only [u,rationalSpatialPoint,PiLp.toLp_apply,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using hh
      rw [htarget]
      exact (rescaledOriginSeed_error v hu source hs m1 m2 (tau/8) (by positivity)).trans
        (Rat.cast_le.mpr (by linarith : tau/8 ≤ tau))
    · rw [if_neg hboundary]
      by_cases hfront : a 0 ≤ 1-eta/2
      · rw [if_pos hfront]
        refine ⟨rescaledLineValue source m1 m2 a tau,rfl,?_⟩
        have htarget : sourcePeriodicReference v hv hu source hs m1 m2 eta (physicalPeriod • u)=
            sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • u) := by
          apply unitReference_front v hv hu q₀ h₀ (spin_field_periodic hp) (eta : ℝ) heR he1R _ hc
            (rescaledOriginSeed_spec v hu source hs m1 m2).2.1 u ha
          have hh : (a 0 : ℝ) ≤ (((1-eta/2 : ℚ) : ℝ)) := Rat.cast_le.mpr hfront
          simpa only [u,rationalSpatialPoint,PiLp.toLp_apply,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using hh
        rw [htarget]
        exact rescaledLineValue_error v hv hu source hs m1 m2 hm1 hm2 hb a ha tau ht ht1
      · rw [if_neg hfront]
        exact sourceReferenceTransitionValue_error v hv hu hp source hs m1 m2 hm1 hm2 hb B hB mu hm hg hoff
          eta he he1 hmargin a ha (lt_of_not_ge hfront).le tau ht ht1

/-- Original rational derivative bounds and the physical separation bound
alone determine both the finite value program and its fixed periodic target. -/
theorem sourceReferenceValueFromGap_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (gap : ℚ) (hg0 : 0<gap)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → (gap : ℝ) ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (a : Fin 3 → ℚ) (ha : ∀ j, (a j : ℝ) ∈ Icc 0 1) (tau : ℚ) (ht : 0<tau) (ht1 : tau ≤ 1) :
    ∃ q, sourceReferenceValueFromGap source m1 m2 gap a tau=some q ∧
      ‖rationalQuaternionCast q-sourcePeriodicReference v hv hu source hs m1 m2 (referenceUnitCollar gap)
        (physicalPeriod • rationalSpatialPoint a)‖ ≤ (tau : ℝ) := by
  have hc := referenceUnitCollar_spec gap hg0
  have hmargin : 7*(referenceUnitCollar gap : ℝ) ≤ (gap : ℝ)/2 := by
    have h : (((7*referenceUnitCollar gap : ℚ) : ℝ)) ≤ (((gap/2 : ℚ) : ℝ)) := Rat.cast_le.mpr hc.2.2
    simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_div] using h
  exact sourceReferenceValue_error v hv hu hp source hs m1 m2 hm1 hm2 hb B hB (gap : ℝ) (by exact_mod_cast hg0)
    hg hoff (referenceUnitCollar gap) hc.1 (by linarith [hc.2.1]) hmargin a ha tau ht ht1

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
