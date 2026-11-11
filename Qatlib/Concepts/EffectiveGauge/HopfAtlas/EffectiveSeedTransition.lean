/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CoarseSeedAtlas
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RescaledLine
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeedChartTransfer
import Qatlib.Concepts.EffectiveGauge.RationalFlow.TerminalCircleSamples

set_option backward.isDefEq.respectTransparency false

/-!
# Effective Seed Transition

Hopf Atlas constructions for Effective Gauge.
Defines `seedTransitionAccuracy`, `rationalSeedTransitionValue`, `rationalSeedTransitionRun`.
Proves `originSeedOnAdmittedChart_error`, `transitionProduct_error`, `rationalSeedTransitionRun_correct`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of seed Transition Accuracy in the Hopf Atlas construction. -/
def seedTransitionAccuracy (tolerance : ℚ) : ℚ := min 1 (tolerance/8)

/-- Both roots share one fine rescaled origin answer. No exact spin, real
square root or argument oracle is an input to this finite program. -/
def rationalSeedTransitionValue (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (fromChart toChart : SeedChart) (tolerance : ℚ) : Quaternion ℚ :=
  let b := seedValuePrecision (seedTransitionAccuracy tolerance)
  let sample := originSpinSamples (rescaledSpinSamples source m1 m2) b
  let fromSeed := rationalChartSeed fromChart sample b
  let toSeed := rationalChartSeed toChart sample b
  toSeed*star fromSeed

/-- Rejection means no finite overlap certificate, not chart invalidity. -/
def rationalSeedTransitionRun (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (fromChart toChart : SeedChart) (tolerance : ℚ) : Option (Quaternion ℚ) :=
  let coarse := originSpinSamples (rescaledSpinSamples source m1 m2) 4
  if seedChartAccepted coarse fromChart && seedChartAccepted coarse toChart then
    some (rationalSeedTransitionValue source m1 m2 fromChart toChart tolerance)
  else none

noncomputable section
open scoped Quaternion

/-- Original `originSeedOnAdmittedChart_error` guarantee for the `EffectiveSeedTransition` construction; the complete source hypotheses are retained. -/
theorem originSeedOnAdmittedChart_error (v : SpatialPoint → SpatialPoint) (hu : ∀ x, ‖v x‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (chart : SeedChart)
    (hc : seedChartAccepted (originSpinSamples (rescaledSpinSamples source m1 m2) 4) chart=true)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ‖rationalQuaternionCast (originSeedOnChart (rescaledSpinSamples source m1 m2) chart tolerance)-
      exactChartSeed chart (sourceQuaternion v 0)‖ ≤ (tolerance : ℝ) := by
  have hcoarse := rescaledOriginSamples_error v source hs m1 m2 4 0
  have hvalid := seedChartAccepted_valid _ (sourceQuaternion v 0)
    (by simpa only [sourceQuaternion,spinOfVector,show (2^4 : ℝ)⁻¹=(1/16 : ℝ) by norm_num] using hcoarse) chart hc
  have he := rescaledOriginSamples_error v source hs m1 m2 (seedValuePrecision tolerance)
  have herr := rationalChartSeed_error chart
    (originSpinSamples (rescaledSpinSamples source m1 m2) (seedValuePrecision tolerance))
    (sourceQuaternion v 0) ((spinOfVector_norm _).trans (hu 0)) hvalid _
    (seedValuePrecision_eight tolerance)
    (by intro j; fin_cases j <;> simpa [sourceQuaternion,spinOfVector] using he _)
  have hb : ((32*(2^seedValuePrecision tolerance : ℚ)⁻¹ : ℚ) : ℝ) ≤ (tolerance : ℝ) :=
    Rat.cast_le.mpr (seedValuePrecision_budget tolerance ht)
  push_cast at hb
  exact herr.trans hb

/-- Original `transitionProduct_error` guarantee for the `EffectiveSeedTransition` construction; the complete source hypotheses are retained. -/
private theorem transitionProduct_error (a b p q : ℍ) (delta : ℝ)
    (hp : ‖p‖=1) (hq : ‖q‖=1) (ha : ‖a-p‖ ≤ delta) (hb : ‖b-q‖ ≤ delta)
    (hd : delta ≤ 1) : ‖a*b-p*q‖ ≤ 3*delta := by
  have hn : ‖a‖ ≤ 2 := by
    have h := (norm_le_norm_sub_add a p).trans (add_le_add ha hp.le)
    linarith
  have hid : a*b-p*q=a*(b-q)+(a-p)*q := by noncomm_ring
  calc
    _ ≤ ‖a*(b-q)‖+‖(a-p)*q‖ := by rw [hid]; exact norm_add_le _ _
    _ = ‖a‖*‖b-q‖+‖a-p‖ := by rw [norm_mul,norm_mul,hq,mul_one]
    _ ≤ 2*delta+delta := add_le_add (mul_le_mul hn hb (norm_nonneg _) (by norm_num)) ha
    _ = _ := by ring

/-- Original `rationalSeedTransitionRun_correct` guarantee for the `EffectiveSeedTransition` construction; the complete source hypotheses are retained. -/
theorem rationalSeedTransitionRun_correct (v : SpatialPoint → SpatialPoint) (hu : ∀ x, ‖v x‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (a b : SeedChart)
    (ha : seedChartAccepted (originSpinSamples (rescaledSpinSamples source m1 m2) 4) a=true)
    (hb : seedChartAccepted (originSpinSamples (rescaledSpinSamples source m1 m2) 4) b=true)
    (tolerance : ℚ) (ht : 0<tolerance) :
    ∃ value, rationalSeedTransitionRun source m1 m2 a b tolerance=some value ∧
      ‖rationalQuaternionCast value-seedChartTransition a b (sourceQuaternion v 0)‖ ≤ (tolerance : ℝ)/2 := by
  let delta := seedTransitionAccuracy tolerance
  have htR : (0 : ℝ)<(tolerance : ℝ) := Rat.cast_pos.mpr ht
  have hd : 0<delta := lt_min (by norm_num) (by positivity)
  have hd1 : (delta : ℝ) ≤ 1 := by exact_mod_cast (min_le_left 1 (tolerance/8))
  have hdt : (delta : ℝ) ≤ (tolerance : ℝ)/8 := by
    have h : (((min 1 (tolerance/8) : ℚ)) : ℝ) ≤ (((tolerance/8 : ℚ)) : ℝ) :=
      Rat.cast_le.mpr (min_le_right (1 : ℚ) (tolerance/8))
    simpa only [delta,seedTransitionAccuracy,Rat.cast_div,Rat.cast_ofNat] using h
  have hA := originSeedOnAdmittedChart_error v hu source hs m1 m2 a ha delta hd
  have hB := originSeedOnAdmittedChart_error v hu source hs m1 m2 b hb delta hd
  have hcoarse := rescaledOriginSamples_error v source hs m1 m2 4 0
  have he : |(originSpinSamples (rescaledSpinSamples source m1 m2) 4 0 : ℝ)-
      (sourceQuaternion v 0).imI| ≤ (1/16 : ℝ) := by norm_num at hcoarse ⊢; exact hcoarse
  have hvalidA := seedChartAccepted_valid _ _ he a ha
  have hvalidB := seedChartAccepted_valid _ _ he b hb
  have hn : ‖sourceQuaternion v 0‖=1 := (spinOfVector_norm _).trans (hu 0)
  have hnA := (exactChartSeed_spec a (sourceQuaternion v 0) rfl hn hvalidA).1
  have hnB := (exactChartSeed_spec b (sourceQuaternion v 0) rfl hn hvalidB).1
  refine ⟨rationalSeedTransitionValue source m1 m2 a b tolerance,?_,?_⟩
  · simp only [rationalSeedTransitionRun,ha,hb,Bool.true_and,ite_true]
  · change ‖rationalQuaternionCast
        (originSeedOnChart (rescaledSpinSamples source m1 m2) b delta*
          star (originSeedOnChart (rescaledSpinSamples source m1 m2) a delta))-
        exactChartSeed b (sourceQuaternion v 0)*star (exactChartSeed a (sourceQuaternion v 0))‖ ≤ _
    rw [map_mul,rationalQuaternionCast_star]
    have hstar : ‖star (rationalQuaternionCast (originSeedOnChart (rescaledSpinSamples source m1 m2) a delta))-
        star (exactChartSeed a (sourceQuaternion v 0))‖ ≤ (delta : ℝ) := by
      simpa only [← star_sub,norm_star] using hA
    have herr := transitionProduct_error _ _ _ _ (delta : ℝ) hnB (by simpa only [norm_star] using hnA) hB hstar hd1
    exact herr.trans (by linarith)

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
