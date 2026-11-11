/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FrequencyShell
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Mode Bounds

Torus Fourier constructions for Effective Gauge.
Proves `frequency_coordinate_abs_le_radius`, `frequencyLinear_norm_le`, `fourierModeExponent_norm_le`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `frequency_coordinate_abs_le_radius` guarantee for the `FourierModeBounds` construction; the complete source hypotheses are retained. -/
theorem frequency_coordinate_abs_le_radius (k : SpatialFrequency) (i : Fin 3) :
    |(k i : ℝ)| ≤ (frequencyRadius k : ℝ) := by
  have h := (frequencyRadius_le_iff k (frequencyRadius k)).mp le_rfl i
  have hR : ((k i).natAbs : ℝ) ≤ (frequencyRadius k : ℝ) := by exact_mod_cast h
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hR

/-- Original `frequencyLinear_norm_le` guarantee for the `FourierModeBounds` construction; the complete source hypotheses are retained. -/
theorem frequencyLinear_norm_le (k : SpatialFrequency) :
    ‖frequencyLinear k‖ ≤ 3*(frequencyRadius k : ℝ) := by
  apply (frequencyLinear k).opNorm_le_bound (by positivity)
  intro x
  rw [frequencyLinear_apply]
  calc
    ‖∑ j : Fin 3, (k j : ℝ)*x j‖ ≤ ∑ j : Fin 3, ‖(k j : ℝ)*x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (frequencyRadius k : ℝ)*‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (frequency_coordinate_abs_le_radius k j) (PiLp.norm_apply_le x j)
        (norm_nonneg _) (Nat.cast_nonneg _)
    _ = (3*(frequencyRadius k : ℝ))*‖x‖ := by simp; ring

/-- Original `fourierModeExponent_norm_le` guarantee for the `FourierModeBounds` construction; the complete source hypotheses are retained. -/
theorem fourierModeExponent_norm_le (k : SpatialFrequency) :
    ‖fourierModeExponent k‖ ≤ 3*physicalPeriod*(frequencyRadius k : ℝ) := by
  have hp : 0 ≤ physicalPeriod := physicalPeriod_pos.le
  apply (fourierModeExponent k).opNorm_le_bound (by positivity)
  intro x
  have h := (frequencyLinear k).le_opNorm x
  calc
    ‖fourierModeExponent k x‖ = physicalPeriod*‖frequencyLinear k x‖ := by
      simp [fourierModeExponent,Complex.norm_real,Real.norm_of_nonneg hp]
    _ ≤ physicalPeriod*(3*(frequencyRadius k : ℝ)*‖x‖) := by
      gcongr
      exact h.trans (mul_le_mul_of_nonneg_right (frequencyLinear_norm_le k) (norm_nonneg x))
    _ = (3*physicalPeriod*(frequencyRadius k : ℝ))*‖x‖ := by ring

/-- The derivative of the actual mode, as a real continuous linear map. -/
theorem unitFourierMode_fderiv (k : SpatialFrequency) :
    fderiv ℝ (unitFourierMode k)=fun x => unitFourierMode k x • fourierModeExponent k := by
  funext x
  exact (fourierModeExponent k).hasFDerivAt.cexp.fderiv

/-- Uniform bounds on full multilinear derivatives, needed for termwise
 differentiation. A list of coordinate identities alone is insufficient. -/
theorem unitFourierMode_iteratedFDeriv_norm_le (k : SpatialFrequency) (n : ℕ) (x : SpatialPoint) :
    ‖iteratedFDeriv ℝ n (unitFourierMode k) x‖ ≤ ‖fourierModeExponent k‖^n := by
  let B : ℂ →L[ℝ] (SpatialPoint →L[ℝ] ℂ) :=
    (ContinuousLinearMap.lsmul ℝ ℂ).flip (fourierModeExponent k)
  have hB : ‖B‖ ≤ ‖fourierModeExponent k‖ := by
    apply B.opNorm_le_bound (norm_nonneg _)
    intro z
    change ‖z • fourierModeExponent k‖ ≤ ‖fourierModeExponent k‖*‖z‖
    rw [norm_smul,mul_comm]
  induction n with
  | zero => simp [norm_iteratedFDeriv_zero,unitFourierMode_norm]
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv,unitFourierMode_fderiv]
    change ‖iteratedFDeriv ℝ n (B ∘ unitFourierMode k) x‖ ≤ _
    calc
      _ ≤ ‖B‖*‖iteratedFDeriv ℝ n (unitFourierMode k) x‖ :=
        B.norm_iteratedFDeriv_comp_left (contDiff_unitFourierMode k).contDiffAt
          (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      _ ≤ ‖fourierModeExponent k‖*‖fourierModeExponent k‖^n :=
        mul_le_mul hB ih (norm_nonneg _) (norm_nonneg _)
      _ = ‖fourierModeExponent k‖^(n+1) := by ring

end Qatlib.Concepts.EffectiveGauge.TorusFourier
