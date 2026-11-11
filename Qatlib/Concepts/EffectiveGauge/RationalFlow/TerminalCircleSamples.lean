/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.RescaledLine
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseLogPrimitive

/-! # The endpoint circle callback is produced from the same original spin -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of terminal Circle Samples in the Rational Flow construction. -/
def terminalCircleSamples (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (m1 m2 z : ℚ)
    (label : ℚ × ℕ) : RationalCircleSample :=
  let e := (2^label.2 : ℚ)⁻¹
  let q := rescaledLineValue source m1 m2 ![1,label.1,z] (e/8)
  let qc := originSeedApproximation (rescaledSpinSamples source m1 m2) (e/8)
  let ratio := q*star qc
  (ratio.re,ratio.imI)

/-- A persistent reference computes the chart once, before sampling the curve. -/
def rescaledLineOnChart (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (chart : SeedChart) (a : Fin 3 → ℚ) (tolerance : ℚ) : Quaternion ℚ :=
  let samples := rescaledSpinSamples source m1 m2
  let seed := originSeedOnChart samples chart (tolerance/8)
  if m1=0 then seed
  else seed*rationalCayleyValue
    (physicalCayleyExecution samples (a 1) (a 2) (a 0) (7*m1) (49*m2) (tolerance/4))

/-- Original `rescaledLineOnChart_chosen` guarantee for the `TerminalCircleSamples` construction; the complete source hypotheses are retained. -/
theorem rescaledLineOnChart_chosen (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (a : Fin 3 → ℚ) (tolerance : ℚ) :
    rescaledLineOnChart source m1 m2 (chosenOriginChart (rescaledSpinSamples source m1 m2)) a tolerance=
      rescaledLineValue source m1 m2 a tolerance := by
  simp only [rescaledLineOnChart,rescaledLineValue,seededPhysicalValue,originSeedApproximation]

/-- Definition of terminal Circle Samples On Chart in the Rational Flow construction. -/
def terminalCircleSamplesOnChart (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 z : ℚ) (chart : SeedChart) (label : ℚ × ℕ) : RationalCircleSample :=
  let e := (2^label.2 : ℚ)⁻¹
  let q := rescaledLineOnChart source m1 m2 chart ![1,label.1,z] (e/8)
  let qc := originSeedOnChart (rescaledSpinSamples source m1 m2) chart (e/8)
  let ratio := q*star qc
  (ratio.re,ratio.imI)

/-- Original `terminalCircleSamplesOnChart_chosen` guarantee for the `TerminalCircleSamples` construction; the complete source hypotheses are retained. -/
theorem terminalCircleSamplesOnChart_chosen (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 z : ℚ) :
    terminalCircleSamplesOnChart source m1 m2 z (chosenOriginChart (rescaledSpinSamples source m1 m2))=
      terminalCircleSamples source m1 m2 z := by
  funext label
  simp only [terminalCircleSamplesOnChart,terminalCircleSamples,rescaledLineOnChart_chosen,originSeedApproximation]

noncomputable section
open scoped Quaternion ContDiff ComplexConjugate
open Set

/-- Definition of rescaled Terminal Ratio in the Rational Flow construction. -/
def rescaledTerminalRatio (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate v source) (m1 m2 : ℚ) (p : TransversePoint) : ℍ :=
  terminalRatio v hv (rescaledOriginSeed v source m1 m2) (rescaledOriginSeed_spec v hu source hs m1 m2).1
    (physicalPeriod • p)

/-- Original `rationalQuaternionCast_star` guarantee for the `TerminalCircleSamples` construction; the complete source hypotheses are retained. -/
theorem rationalQuaternionCast_star (q : Quaternion ℚ) : rationalQuaternionCast (star q)=star (rationalQuaternionCast q) := by
  apply Quaternion.ext <;> simp [rationalQuaternionCast]

/-- Original `rescaledRaw_finish` guarantee for the `TerminalCircleSamples` construction; the complete source hypotheses are retained. -/
private theorem rescaledRaw_finish (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (t z : ℚ) :
    sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • rationalSpatialPoint ![1,t,z])=
      sourceLiftPaths v hv q₀ h₀ (physicalPeriod • rationalTransversePoint t z) transportFinish := by
  have hpos : sourcePositionInverse (physicalPeriod • rationalSpatialPoint ![1,t,z])=
      (physicalPeriod • rationalTransversePoint t z,(transportFinish : ℝ)) := by
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · change physicalPeriod*((1 : ℚ) : ℝ)=physicalPeriod
      simp
  rw [sourceLiftSpatialExtension,hpos,sourceLiftExtension_eq v hv hu q₀ h₀ _ transportFinish]

/-- Original `contDiff_rescaledTerminalRatio` guarantee for the `TerminalCircleSamples` construction; the complete source hypotheses are retained. -/
theorem contDiff_rescaledTerminalRatio (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate v source) (m1 m2 : ℚ) :
    ContDiff ℝ ∞ (rescaledTerminalRatio v hv hu source hs m1 m2) :=
  (contDiff_terminalRatio v hv _ _).comp (contDiff_id.const_smul physicalPeriod)

/-- Original `rescaledTerminalRatio_circle` guarantee for the `TerminalCircleSamples` construction; the complete source hypotheses are retained. -/
theorem rescaledTerminalRatio_circle (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source) (m1 m2 : ℚ)
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b) :
    ∀ p, IsCircleQuaternion (rescaledTerminalRatio v hv hu source hs m1 m2 p) :=
  fun p => terminalRatio_circle v hv hu _ _ (spin_field_periodic hp) (mu/2) (by positivity)
    (sourceQuaternion v 0) (support_background_collar v B hB mu hm hg hoff)
    (rescaledOriginSeed_spec v hu source hs m1 m2).2.1 (physicalPeriod • p)

/-- The callback approximates the actual endpoint ratio of the fixed raw
field, despite both returned quaternions being nonunit rational values. -/
theorem terminalCircleSamples_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hb : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (t z : ℚ) (ht : (t : ℝ) ∈ Icc 0 1) (hz : (z : ℝ) ∈ Icc 0 1) (b : ℕ) :
    ‖rationalCircleCast (terminalCircleSamples source m1 m2 z (t,b))-
      circleComplex (rescaledTerminalRatio v hv hu source hs m1 m2 (rationalTransversePoint t z))‖ ≤ (2^b : ℝ)⁻¹ := by
  let e : ℚ := (2^b : ℚ)⁻¹
  let q₀ := rescaledOriginSeed v source m1 m2
  have h₀ : ‖q₀‖=1 := (rescaledOriginSeed_spec v hu source hs m1 m2).1
  let q := sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • rationalSpatialPoint ![1,t,z])
  let a := rationalQuaternionCast (rescaledLineValue source m1 m2 ![1,t,z] (e/8))
  let c := rationalQuaternionCast (originSeedApproximation (rescaledSpinSamples source m1 m2) (e/8))
  have he0 : (0 : ℝ) ≤ e := by dsimp [e]; positivity
  have he1 : (e : ℝ) ≤ 1 := by
    have h : e ≤ (1 : ℚ) := (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
    exact_mod_cast h
  have hqn : ‖q‖=1 := sourceLiftSpatialExtension_unit v hv q₀ h₀ _
  have ha : ‖a-q‖ ≤ (e : ℝ)/8 := by
    have h := rescaledLineValue_error v hv hu source hs m1 m2 hm1 hm2 hb ![1,t,z]
      (by intro i; fin_cases i; exact ⟨by norm_num,by norm_num⟩; exact ht; exact hz) (e/8) (by dsimp [e]; positivity)
      (by dsimp [e]; have hpow : (1 : ℚ) ≤ 2^b := one_le_pow₀ (by norm_num); have hi := (inv_le_one₀ (by positivity)).mpr hpow; linarith)
    simpa only [Rat.cast_div,Rat.cast_ofNat] using h
  have hc : ‖c-q₀‖ ≤ (e : ℝ)/8 := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using rescaledOriginSeed_error v hu source hs m1 m2 (e/8) (by dsimp [e]; positivity)
  have hcn : ‖c‖ ≤ 1+(e : ℝ)/8 := by
    have h := (norm_le_norm_sub_add c q₀).trans (add_le_add hc h₀.le)
    linarith
  have hprod : ‖a*star c-q*star q₀‖ ≤ (e : ℝ) := by
    have hid : a*star c-q*star q₀=(a-q)*star c+q*star (c-q₀) := by rw [star_sub]; noncomm_ring
    calc
      _ ≤ ‖(a-q)*star c‖+‖q*star (c-q₀)‖ := by rw [hid]; exact norm_add_le _ _
      _ = ‖a-q‖*‖c‖+‖q‖*‖c-q₀‖ := by rw [norm_mul,norm_mul,Quaternion.norm_star,Quaternion.norm_star]
      _ ≤ ((e : ℝ)/8)*(1+(e : ℝ)/8)+(e : ℝ)/8 := by
        rw [hqn,one_mul]
        exact add_le_add (mul_le_mul ha hcn (norm_nonneg _) (by positivity)) hc
      _ ≤ (e : ℝ) := by nlinarith
  have htrue : rescaledTerminalRatio v hv hu source hs m1 m2 (rationalTransversePoint t z)=q*star q₀ := by
    dsimp [rescaledTerminalRatio,terminalRatio,fibreRatio,q]
    rw [rescaledRaw_finish v hv hu]
  have hcast : rationalCircleCast (terminalCircleSamples source m1 m2 z (t,b))=circleComplex (a*star c) := by
    change circleComplex (rationalQuaternionCast
      (rescaledLineValue source m1 m2 ![1,t,z] (e/8)*star
        (originSeedApproximation (rescaledSpinSamples source m1 m2) (e/8))))=circleComplex (a*star c)
    rw [map_mul,rationalQuaternionCast_star]
  rw [hcast,htrue,← circleComplex_sub]
  apply (circleComplex_norm_le _).trans
  simpa only [e,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hprod

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
