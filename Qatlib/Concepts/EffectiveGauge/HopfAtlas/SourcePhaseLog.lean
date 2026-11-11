/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.TerminalRegularity

set_option backward.isDefEq.respectTransparency false

/-!
# Original spin access produces the same real terminal phase

The underlying circle curve and its derivative bound are derived from the
source. The conclusion names the real terminalRealPhase of the same exact
raw field, at the exact physical coordinates 2π*(y,z).
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of source Phase Log in the Hopf Atlas construction. -/
def sourcePhaseLog (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (m1 m2 y z tolerance : ℚ) :
    Option RationalPhaseLogResult :=
  let chart := chosenOriginChart (rescaledSpinSamples source m1 m2)
  rationalPhaseLog (terminalCircleSamplesOnChart source m1 m2 z chart) y (((7*m1)^2+49*m2)/2) tolerance

noncomputable section
open scoped Quaternion ContDiff
open Set

/-- Original `rescaledTerminalRatio_zero_y` guarantee for the `SourcePhaseLog` construction; the complete source hypotheses are retained. -/
private theorem rescaledTerminalRatio_zero_y (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (z : ℝ) (hz : z ∈ Icc 0 1) :
    rescaledTerminalRatio v hv hu source hs m1 m2 (transversePair (0,z))=1 := by
  unfold rescaledTerminalRatio
  rw [transversePair_scale,mul_zero]
  apply terminalRatio_boundary v hv hu _ _ (mu/2) (sourceQuaternion v 0)
    (support_background_collar v B hB mu hm hg hoff)
  · intro i
    fin_cases i
    · exact ⟨le_rfl,physicalPeriod_pos.le⟩
    · change 0 ≤ physicalPeriod*z ∧ physicalPeriod*z ≤ physicalPeriod
      exact ⟨mul_nonneg physicalPeriod_pos.le hz.1,
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 physicalPeriod_pos.le⟩
  · refine ⟨0,Or.inl ?_⟩
    change 0 ≤ mu/2
    positivity

/-- Original `sourcePhaseLog_error` guarantee for the `SourcePhaseLog` construction; the complete source hypotheses are retained. -/
theorem sourcePhaseLog_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (y z tau : ℚ) (hy : (y : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1) (ht : 0<tau) :
    ∃ r, sourcePhaseLog source m1 m2 y z tau=some r ∧
      |(r.value : ℝ)-terminalRealPhase v hv (rescaledOriginSeed v source m1 m2)
        (rescaledOriginSeed_spec v hu source hs m1 m2).1 (physicalPeriod • rationalTransversePoint y z)| ≤
          (r.errorBound : ℝ) ∧ r.errorBound ≤ tau ∧
      r.steps=phaseLogSteps y (((7*m1)^2+49*m2)/2) ∧ r.precision=phaseLogPrecision tau ∧
      r.terms ≤ r.steps*arctanFuel (tau/(2*(r.steps : ℚ))) := by
  let k := rescaledTerminalRatio v hv hu source hs m1 m2
  have hk : ContDiff ℝ ∞ k := contDiff_rescaledTerminalRatio v hv hu source hs m1 m2
  have hc : ∀ p, IsCircleQuaternion (k p) := rescaledTerminalRatio_circle v hv hu hp source hs m1 m2 B hB mu hm hg hoff
  have h0 : k (transversePair (0,(z : ℝ)))=1 :=
    rescaledTerminalRatio_zero_y v hv hu source hs m1 m2 B hB mu hm hg hoff (z : ℝ) hz
  let Q : ℚ := ((7*m1)^2+49*m2)/2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hder : ∀ u ∈ Icc 0 (y : ℝ),
      ‖fderiv ℝ k (transversePair (u,(z : ℝ))) (EuclideanSpace.single 0 1)‖ ≤ (Q : ℝ) := by
    intro u huI
    exact rescaledTerminalRatio_y_bound v hv hu source hs m1 m2 hm1 hm2 hb u (z : ℝ) ⟨huI.1,huI.2.trans hy.2⟩ hz
  have horacle : ∀ t : ℚ, (t : ℝ) ∈ Icc 0 (y : ℝ) → ∀ b,
      ‖rationalCircleCast (terminalCircleSamples source m1 m2 z (t,b))-
        circleComplex (k (transversePair ((t : ℝ),(z : ℝ))))‖ ≤ (2^b : ℝ)⁻¹ := by
    intro t ht b
    exact terminalCircleSamples_error v hv hu source hs m1 m2 hm1 hm2 hb t z ⟨ht.1,ht.2.trans hy.2⟩ hz b
  obtain ⟨r,hr,hvalue,he,hmeta⟩ := rationalPhaseLog_primitive k hk hc (z : ℝ) h0
    (terminalCircleSamples source m1 m2 z) y Q tau (by exact_mod_cast hy.1) hQ ht hder horacle
  have htarget : circleLogPrimitive k (transversePair ((y : ℝ),(z : ℝ)))=
      terminalRealPhase v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1
        (physicalPeriod • rationalTransversePoint y z) := by
    have h := circleLogPrimitive_scaled
      (terminalRatio v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1)
      (contDiff_terminalRatio v hv _ _) physicalPeriod (y : ℝ) (z : ℝ)
    rw [← transversePair_scale] at h
    exact h
  rw [htarget] at hvalue
  refine ⟨r,?_,hvalue,he,hmeta⟩
  simpa only [sourcePhaseLog,terminalCircleSamplesOnChart_chosen] using hr

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
