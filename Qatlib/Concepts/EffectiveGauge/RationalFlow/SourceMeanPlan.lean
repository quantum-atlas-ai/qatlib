/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanError

set_option backward.isDefEq.respectTransparency false

/-!
# Source Mean Plan

Rational Flow constructions for Effective Gauge.
Defines `sourceMeanDerivativeBudget`, `sourceMeanMesh`, `sourceMeanSampleBits`.
Proves `sourceMeanMesh_pos`, `sourceMeanMesh_budget`, `sourceMeanSampleBits_budget`.
-/


set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of source Mean Derivative Budget in the Rational Flow construction. -/
def sourceMeanDerivativeBudget (m1 m2 : ℚ) : ℚ := (7*m1)^2/2+(7*m1)*(49*m2)

/-- Definition of source Mean Mesh in the Rational Flow construction. -/
def sourceMeanMesh (m1 m2 tolerance : ℚ) : ℕ :=
  max 1 (Nat.ceil (12*sourceMeanDerivativeBudget m1 m2/tolerance))

/-- Definition of source Mean Sample Bits in the Rational Flow construction. -/
def sourceMeanSampleBits (m1 tolerance : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil (max 64 (8*(7*m1+1)^2/tolerance)))

/-- Definition of source Mean Length Bits in the Rational Flow construction. -/
def sourceMeanLengthBits (m1 tolerance : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil (64*((7*m1)^2+1)/tolerance))

/-- Original `sourceMeanMesh_pos` guarantee for the `SourceMeanPlan` construction; the complete source hypotheses are retained. -/
theorem sourceMeanMesh_pos (m1 m2 tolerance : ℚ) : 0<sourceMeanMesh m1 m2 tolerance := by
  exact lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)

/-- Original `sourceMeanMesh_budget` guarantee for the `SourceMeanPlan` construction; the complete source hypotheses are retained. -/
theorem sourceMeanMesh_budget (m1 m2 tolerance : ℚ) (ht : 0<tolerance) :
    3*sourceMeanDerivativeBudget m1 m2/(sourceMeanMesh m1 m2 tolerance : ℚ) ≤ tolerance/4 := by
  have hn : (0 : ℚ)<sourceMeanMesh m1 m2 tolerance := by exact_mod_cast sourceMeanMesh_pos m1 m2 tolerance
  have hceil : 12*sourceMeanDerivativeBudget m1 m2/tolerance ≤ (sourceMeanMesh m1 m2 tolerance : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 (Nat.ceil (12*sourceMeanDerivativeBudget m1 m2/tolerance)))
  have hh := (div_le_iff₀ ht).mp hceil
  apply (div_le_iff₀ hn).mpr
  nlinarith

/-- Original `sourceMeanSampleBits_budget` guarantee for the `SourceMeanPlan` construction; the complete source hypotheses are retained. -/
theorem sourceMeanSampleBits_budget (m1 tolerance : ℚ) (ht : 0<tolerance) :
    (2^sourceMeanSampleBits m1 tolerance : ℚ)⁻¹ ≤ 1/64 ∧
      2*(2^sourceMeanSampleBits m1 tolerance : ℚ)⁻¹*(7*m1+1)^2 ≤ tolerance/4 := by
  have hp : Nat.ceil (max 64 (8*(7*m1+1)^2/tolerance)) ≤ 2^sourceMeanSampleBits m1 tolerance :=
    Nat.le_pow_clog (by decide) _
  have htarget : max 64 (8*(7*m1+1)^2/tolerance) ≤ (2^sourceMeanSampleBits m1 tolerance : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have h64 := (le_max_left _ _).trans htarget
  have hrate := (le_max_right _ _).trans htarget
  constructor
  · simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ)<64) h64
  · have hh := (div_le_iff₀ ht).mp hrate
    have he := mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℚ) ≤ (2^sourceMeanSampleBits m1 tolerance : ℚ)⁻¹)
    have hi : (2^sourceMeanSampleBits m1 tolerance : ℚ)*(2^sourceMeanSampleBits m1 tolerance : ℚ)⁻¹=1 := by
      exact mul_inv_cancel₀ (by positivity)
    have hcancel : (2^sourceMeanSampleBits m1 tolerance : ℚ)*tolerance*
        (2^sourceMeanSampleBits m1 tolerance : ℚ)⁻¹=tolerance := by
      rw [mul_right_comm,hi,one_mul]
    rw [hcancel] at he
    nlinarith

/-- Original `sourceMeanLengthBits_budget` guarantee for the `SourceMeanPlan` construction; the complete source hypotheses are retained. -/
theorem sourceMeanLengthBits_budget (m1 tolerance : ℚ) (ht : 0<tolerance) :
    ((7*m1)^2+1)*(2^sourceMeanLengthBits m1 tolerance : ℚ)⁻¹ ≤ tolerance/64 := by
  have hp : Nat.ceil (64*((7*m1)^2+1)/tolerance) ≤ 2^sourceMeanLengthBits m1 tolerance :=
    Nat.le_pow_clog (by decide) _
  have htarget : 64*((7*m1)^2+1)/tolerance ≤ (2^sourceMeanLengthBits m1 tolerance : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hp)
  have hh := (div_le_iff₀ ht).mp htarget
  have he := mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℚ) ≤ (2^sourceMeanLengthBits m1 tolerance : ℚ)⁻¹)
  have hi : (2^sourceMeanLengthBits m1 tolerance : ℚ)*(2^sourceMeanLengthBits m1 tolerance : ℚ)⁻¹=1 := by
    exact mul_inv_cancel₀ (by positivity)
  have hcancel : (2^sourceMeanLengthBits m1 tolerance : ℚ)*tolerance*
      (2^sourceMeanLengthBits m1 tolerance : ℚ)⁻¹=tolerance := by
    rw [mul_right_comm,hi,one_mul]
  rw [hcancel] at he
  nlinarith

/-- Definition of source Mean Planned Unit Execution in the Rational Flow construction. -/
def sourceMeanPlannedUnitExecution (source : RationalJetSource) (m1 m2 tolerance : ℚ) :
    Option (Fin 3 → ℚ) :=
  sourceMeanUnitExecution source m1 m2 (sourceMeanMesh m1 m2 tolerance)
    (sourceMeanSampleBits m1 tolerance)

noncomputable section
open scoped ContDiff

/-- Original `sourceMeanPlannedUnitExecution_error` guarantee for the `SourceMeanPlan` construction; the complete source hypotheses are retained. -/
theorem sourceMeanPlannedUnitExecution_error (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (m1 m2 tolerance : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (ht : 0<tolerance)
    (hb : SourceAllRescalingBounds v (m1 : ℝ) (m2 : ℝ)) :
    ∃ result, sourceMeanPlannedUnitExecution source m1 m2 tolerance=some result ∧ ∀ j,
      |(result j : ℝ)+unitCubeIntegral
        (sourceCurvatureMoment (unitCoordinateSpin v) (sourceMeanMomentAxis j) j)| ≤ (tolerance : ℝ)/2 := by
  have hsamp := sourceMeanSampleBits_budget m1 tolerance ht
  have hprec : (2^sourceMeanSampleBits m1 tolerance : ℝ)⁻¹ ≤ 1/64 := by
    simpa only [Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_div,Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr hsamp.1
  obtain ⟨result,hex,herr⟩ := sourceMeanUnitExecution_error v hv hu source hs m1 m2 hm1 hm2 hb
    (sourceMeanMesh m1 m2 tolerance) (sourceMeanSampleBits m1 tolerance)
    (sourceMeanMesh_pos m1 m2 tolerance) hprec
  refine ⟨result,hex,?_⟩
  have hq := sourceMeanMesh_budget m1 m2 tolerance ht
  dsimp only [sourceMeanDerivativeBudget] at hq
  have hqR : 3*((7*(m1 : ℝ))^2/2+(7*(m1 : ℝ))*(49*(m2 : ℝ)))/
      (sourceMeanMesh m1 m2 tolerance : ℝ) ≤ (tolerance : ℝ)/4 := by exact_mod_cast hq
  have hsR : 2*(2^sourceMeanSampleBits m1 tolerance : ℝ)⁻¹*(7*(m1 : ℝ)+1)^2 ≤
      (tolerance : ℝ)/4 := by
    simpa only [Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr hsamp.2
  intro j
  exact (herr j).trans (by linarith)

end

end Qatlib.Concepts.EffectiveGauge.RationalFlow
