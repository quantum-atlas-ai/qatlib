/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceBranches
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SmoothStepProgram

set_option backward.isDefEq.respectTransparency false

/-!
# Original source access produces the actual transition angle

Both returned subresults come from the same execution. The terminal phase
bound is derived from the original spin, not supplied as a lift modulus.
The final rational cis/product and full value branches are separate.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Data and hypotheses for Rational Reference Angle Result in the Hopf Atlas construction. -/
structure RationalReferenceAngleResult where
  value : ℚ
  error : ℚ
  phaseResult : RationalPhaseLogResult
  cutoffResult : RationalScalarResult
  deriving Repr, DecidableEq

/-- Definition of source Reference Angle in the Hopf Atlas construction. -/
def sourceReferenceAngle (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 eta x y z tolerance : ℚ) : Option RationalReferenceAngleResult :=
  let Q := ((7*m1)^2+49*m2)/2
  (sourcePhaseLog source m1 m2 y z (tolerance/32)).map (fun log =>
    let rho := rationalSmoothStep ((x-(1-eta/2))/(eta/4)) (tolerance/(64*(Q+1)))
    ⟨(1-rho.value)*log.value,log.errorBound+rho.error*Q,log,rho⟩)

noncomputable section
open scoped Quaternion ContDiff
open Set

/-- Original `rescaledTerminalPrimitive_eq` guarantee for the `ReferenceAngle` construction; the complete source hypotheses are retained. -/
theorem rescaledTerminalPrimitive_eq (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate v source) (m1 m2 y z : ℚ) :
    circleLogPrimitive (rescaledTerminalRatio v hv hu source hs m1 m2) (rationalTransversePoint y z)=
      terminalRealPhase v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1
        (physicalPeriod • rationalTransversePoint y z) := by
  have h := circleLogPrimitive_scaled
    (terminalRatio v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1)
    (contDiff_terminalRatio v hv _ _) physicalPeriod (y : ℝ) (z : ℝ)
  rw [← transversePair_scale] at h
  exact h

/-- Original `primitive_abs_bound` guarantee for the `ReferenceAngle` construction; the complete source hypotheses are retained. -/
private theorem primitive_abs_bound (k : TransversePoint → ℍ) (hk : ContDiff ℝ ∞ k)
    (hc : ∀ p, IsCircleQuaternion (k p)) (z y Q : ℝ) (hy : 0 ≤ y)
    (hd : ∀ t ∈ Icc 0 y, ‖fderiv ℝ k (transversePair (t,z)) (EuclideanSpace.single 0 1)‖ ≤ Q) :
    |circleLogPrimitive k (transversePair (y,z))| ≤ Q*y := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc 0 y) => (circleLogPrimitive_hasDerivAt hk z t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact (circleAngularRate_abs_le k _ (hc _).1).trans (hd t ht))
    (convex_Icc 0 y) (show (0 : ℝ) ∈ Icc 0 y from ⟨le_rfl,hy⟩)
    (show y ∈ Icc 0 y from ⟨hy,le_rfl⟩)
  simpa only [circleLogPrimitive_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg hy] using h

/-- Original `sourceTerminalRealPhase_bound` guarantee for the `ReferenceAngle` construction; the complete source hypotheses are retained. -/
theorem sourceTerminalRealPhase_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (y z : ℚ) (hy : (y : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1) :
    |terminalRealPhase v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1
        (physicalPeriod • rationalTransversePoint y z)| ≤ ((((7*m1)^2+49*m2)/2 : ℚ) : ℝ) := by
  rw [← rescaledTerminalPrimitive_eq v hv hu source hs m1 m2 y z]
  let k := rescaledTerminalRatio v hv hu source hs m1 m2
  let Q : ℚ := ((7*m1)^2+49*m2)/2
  have hQ : 0 ≤ (Q : ℝ) := by dsimp [Q]; push_cast; positivity
  have h := primitive_abs_bound k (contDiff_rescaledTerminalRatio v hv hu source hs m1 m2)
    (rescaledTerminalRatio_circle v hv hu hp source hs m1 m2 B hB mu hm hg hoff) (z : ℝ) (y : ℝ) (Q : ℝ) hy.1
    (fun t ht => rescaledTerminalRatio_y_bound v hv hu source hs m1 m2 hm1 hm2 hb t (z : ℝ) ⟨ht.1,ht.2.trans hy.2⟩ hz)
  exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hy.2 hQ)

/-- Original `transition_angle_error` guarantee for the `ReferenceAngle` construction; the complete source hypotheses are retained. -/
private theorem transition_angle_error (rho lambda log cutoff logError cutoffError Q : ℝ)
    (hc : cutoff ∈ Icc 0 1) (hce : 0 ≤ cutoffError)
    (hlog : |log-lambda| ≤ logError) (hcut : |cutoff-rho| ≤ cutoffError) (hlambda : |lambda| ≤ Q) :
    |(1-cutoff)*log-(1-rho)*lambda| ≤ logError+cutoffError*Q := by
  have hid : (1-cutoff)*log-(1-rho)*lambda=(1-cutoff)*(log-lambda)+(rho-cutoff)*lambda := by ring
  have hc1 : |1-cutoff| ≤ (1 : ℝ) := by rw [abs_of_nonneg (by linarith [hc.2])]; linarith [hc.1]
  calc
    _ ≤ |(1-cutoff)*(log-lambda)|+|(rho-cutoff)*lambda| := by rw [hid]; exact abs_add_le _ _
    _ = |1-cutoff| *|log-lambda|+|cutoff-rho| *|lambda| := by rw [abs_mul,abs_mul,abs_sub_comm rho cutoff]
    _ ≤ 1*logError+cutoffError*Q := add_le_add (mul_le_mul hc1 hlog (abs_nonneg _) (by norm_num))
      (mul_le_mul hcut hlambda (abs_nonneg _) hce)
    _ = _ := by ring

/-- Original `sourceReferenceAngle_spec` guarantee for the `ReferenceAngle` construction; the complete source hypotheses are retained. -/
theorem sourceReferenceAngle_spec (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (eta x y z tau : ℚ) (hy : (y : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1) (ht : 0<tau) :
    ∃ r, sourceReferenceAngle source m1 m2 eta x y z tau=some r ∧
      |(r.value : ℝ)-(1-Real.smoothTransition (((x-(1-eta/2))/(eta/4) : ℚ) : ℝ))*
        terminalRealPhase v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1
          (physicalPeriod • rationalTransversePoint y z)| ≤ (r.error : ℝ) ∧ r.error ≤ tau/16 := by
  let Q : ℚ := ((7*m1)^2+49*m2)/2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨log,hrun,hlog,helog,_⟩ := sourcePhaseLog_error v hv hu hp source hs m1 m2 hm1 hm2 hb B hB mu hm hg hoff
    y z (tau/32) hy hz (by positivity)
  let cutoff := rationalSmoothStep ((x-(1-eta/2))/(eta/4)) (tau/(64*(Q+1)))
  have hsmooth := rationalSmoothStep_spec ((x-(1-eta/2))/(eta/4)) (tau/(64*(Q+1))) (by positivity)
  have hlambda := sourceTerminalRealPhase_bound v hv hu hp source hs m1 m2 hm1 hm2 hb B hB mu hm hg hoff y z hy hz
  let r : RationalReferenceAngleResult := ⟨(1-cutoff.value)*log.value,log.errorBound+cutoff.error*Q,log,cutoff⟩
  refine ⟨r,?_,?_,?_⟩
  · change (sourcePhaseLog source m1 m2 y z (tau/32)).map _=some r
    rw [hrun]
    rfl
  · have he := transition_angle_error _ _ (log.value : ℝ) (cutoff.value : ℝ) (log.errorBound : ℝ)
      (cutoff.error : ℝ) (Q : ℝ) ⟨by exact_mod_cast hsmooth.2.1,by exact_mod_cast hsmooth.2.2.1⟩
      (by exact_mod_cast hsmooth.2.2.2.1) hlog hsmooth.1 hlambda
    change |(((1-cutoff.value)*log.value : ℚ) : ℝ)-_| ≤ ((log.errorBound+cutoff.error*Q : ℚ) : ℝ)
    push_cast at he ⊢
    exact he
  · change log.errorBound+cutoff.error*Q ≤ tau/16
    have hcut := (le_div_iff₀ (by positivity : (0 : ℚ)<64*(Q+1))).mp hsmooth.2.2.2.2
    change cutoff.error*(64*(Q+1)) ≤ tau at hcut
    have hce : 0 ≤ cutoff.error := hsmooth.2.2.2.1
    nlinarith


/-- Original `phase_lipschitz` guarantee for the `ReferenceAngle` construction; the complete source hypotheses are retained. -/
theorem phase_lipschitz (a b : ℝ) : ‖phase a-phase b‖ ≤ |a-b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 1)
    (fun t (_ : t ∈ (univ : Set ℝ)) => (phase_hasDerivAt t).hasDerivWithinAt)
    (fun t _ => by simp only [norm_mul,norm_iAxis,phase_norm,one_mul,le_refl])
    convex_univ (mem_univ b) (mem_univ a)
  simpa only [one_mul,Real.norm_eq_abs] using h

/-- A real-angle decoder of the finite program approximates the actual
periodic target in the transition region. The decoder phase is exact;
its finite rational cis approximation remains a separate obligation. -/
theorem sourceReferenceTransition_phase_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (eta x y z tau : ℚ) (he : 0<eta) (he1 : eta ≤ 1/2) (hmargin : 7*(eta : ℝ) ≤ mu/2)
    (hx : (x : ℝ) ∈ Icc 0 1) (hy : (y : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1)
    (htransition : 1-eta/2 ≤ x) (ht : 0<tau) :
    ∃ r, sourceReferenceAngle source m1 m2 eta x y z tau=some r ∧
      ‖phase (r.value : ℝ)*rescaledOriginSeed v source m1 m2-
        sourcePeriodicReference v hv hu source hs m1 m2 eta
          (physicalPeriod • rationalSpatialPoint ![x,y,z])‖ ≤ (r.error : ℝ) ∧ r.error ≤ tau/16 := by
  obtain ⟨r,hr,hangle,hbudget⟩ := sourceReferenceAngle_spec v hv hu hp source hs m1 m2 hm1 hm2 hb B hB mu hm hg hoff
    eta x y z tau hy hz ht
  have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
  have hseed := rescaledOriginSeed_spec v hu source hs m1 m2
  have he1R : (eta : ℝ) ≤ 1/2 := by
    have h : (eta : ℝ) ≤ (((1/2 : ℚ) : ℝ)) := Rat.cast_le.mpr he1
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  have htR : (1 : ℝ)-(eta : ℝ)/2 ≤ (x : ℝ) := by
    have h : (((1-eta/2 : ℚ) : ℝ)) ≤ (x : ℝ) := Rat.cast_le.mpr htransition
    simpa only [Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat] using h
  have hformula := unitReference_transition v hv hu (rescaledOriginSeed v source m1 m2) hseed.1 (spin_field_periodic hp)
    (eta : ℝ) (by exact_mod_cast he) he1R (sourceQuaternion v 0) hc hseed.2.1
    (rationalSpatialPoint ![x,y,z]) (by intro j; fin_cases j; exact hx; exact hy; exact hz)
    htR
  have hproj : transverseProjection (physicalPeriod • rationalSpatialPoint ![x,y,z])=
      physicalPeriod • rationalTransversePoint y z := by ext j; fin_cases j <;> rfl
  rw [hproj] at hformula
  refine ⟨r,hr,?_,hbudget⟩
  change ‖phase (r.value : ℝ)*rescaledOriginSeed v source m1 m2-
    periodicReference v hv (rescaledOriginSeed v source m1 m2) hseed.1 (physicalPeriod*(eta : ℝ)) _‖ ≤ _
  rw [hformula]
  have hid (t : ℝ) : phase (r.value : ℝ)*rescaledOriginSeed v source m1 m2-phase t*rescaledOriginSeed v source m1 m2=
      (phase (r.value : ℝ)-phase t)*rescaledOriginSeed v source m1 m2 := by noncomm_ring
  rw [hid,norm_mul]
  simp only [hseed.1,mul_one]
  apply (phase_lipschitz _ _).trans
  push_cast at hangle
  exact hangle

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
