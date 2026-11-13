/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.SpectralAnalysis.SpectralReduction

/-!
# Critical two-level amplitude

This module defines the critical energy, slope, and time scales in terms of two lattice-sum
parameters. It evaluates the explicit two-level amplitude at the critical time, as used in the
analysis of [ChildsGoldstone2004].

## Main statements

* `critEnergy_mul_critTime`: the critical phase is `Real.pi / 2`.
* `two_level_amplitude_optimum`: the amplitude norm at the critical time is `S₁ / Real.sqrt S₂`.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults

/-- The critical energy scale `S₁ / Real.sqrt (S₂ * N)`. -/
noncomputable def critEnergy (S₁ S₂ : ℝ) (N : ℕ) : ℝ := S₁ / Real.sqrt (S₂ * (N : ℝ))

/-- The critical slope scale `2 * S₂ / S₁ ^ 2`. -/
noncomputable def critSlope (S₁ S₂ : ℝ) : ℝ := 2 * S₂ / S₁ ^ 2

/-- The critical time scale `Real.pi * Real.sqrt (S₂ * N) / (2 * S₁)`. -/
noncomputable def critTime (S₁ S₂ : ℝ) (N : ℕ) : ℝ :=
  Real.pi * Real.sqrt (S₂ * (N : ℝ)) / (2 * S₁)

/-- The critical energy is positive when both lattice-sum parameters and the natural size `N`
are positive. -/
theorem critEnergy_pos {S₁ S₂ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) (N : ℕ) (hN : 0 < N) :
    0 < critEnergy S₁ S₂ N := by
  unfold critEnergy
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact div_pos h₁ (Real.sqrt_pos.mpr (mul_pos h₂ hNpos))

/-- The critical slope is positive when both lattice-sum parameters are positive. -/
theorem critSlope_pos {S₁ S₂ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) : 0 < critSlope S₁ S₂ := by
  unfold critSlope
  have hS1 : (0 : ℝ) < S₁ ^ 2 := by positivity
  positivity

/-- For positive lattice-sum parameters and positive natural size, the product of critical
energy and critical time is `Real.pi / 2`. -/
theorem critEnergy_mul_critTime {S₁ S₂ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) (N : ℕ) (hN : 0 < N) :
    critEnergy S₁ S₂ N * critTime S₁ S₂ N = Real.pi / 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt (S₂ * (N : ℝ)) := Real.sqrt_pos.mpr (mul_pos h₂ hNpos)
  have hA : Real.sqrt (S₂ * (N : ℝ)) ≠ 0 := ne_of_gt hsq
  have hS1 : S₁ ≠ 0 := ne_of_gt h₁
  unfold critEnergy critTime
  rw [div_mul_div_comm]
  field_simp [hA, hS1]

/-- For positive `N`, `S₁`, and `S₂`, the displayed two-level amplitude at the critical energy,
slope, and time has norm `S₁ / Real.sqrt S₂` [ChildsGoldstone2004]. -/
theorem two_level_amplitude_optimum (N : ℕ) (hN : 0 < N) (S₁ S₂ : ℝ)
    (h₁ : 0 < S₁) (h₂ : 0 < S₂) :
    ‖-(((Real.sqrt (N : ℝ) : ℂ))⁻¹) *
        ((-(((critEnergy S₁ S₂ N * critSlope S₁ S₂ : ℝ) : ℂ)⁻¹)) *
            Complex.exp (Complex.I * ((critTime S₁ S₂ N * critEnergy S₁ S₂ N : ℝ) : ℂ)) +
          (((critEnergy S₁ S₂ N * critSlope S₁ S₂ : ℝ) : ℂ)⁻¹) *
            Complex.exp (-(Complex.I * ((critTime S₁ S₂ N * critEnergy S₁ S₂ N : ℝ) : ℂ))))‖
      = S₁ / Real.sqrt S₂ := by
  have hE : 0 < critEnergy S₁ S₂ N := critEnergy_pos h₁ h₂ N hN
  have hF' : 0 < critSlope S₁ S₂ := critSlope_pos h₁ h₂
  rw [two_level_amplitude_value N hN (critEnergy S₁ S₂ N) (critSlope S₁ S₂)
    (critTime S₁ S₂ N) hE hF']
  have hphase : critEnergy S₁ S₂ N * critTime S₁ S₂ N = Real.pi / 2 :=
    critEnergy_mul_critTime h₁ h₂ N hN
  rw [hphase, Real.sin_pi_div_two, abs_one, mul_one]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsq : 0 < Real.sqrt (S₂ * (N : ℝ)) := Real.sqrt_pos.mpr (mul_pos h₂ hNpos)
  have hsq2 : 0 < Real.sqrt S₂ := Real.sqrt_pos.mpr h₂
  unfold critEnergy critSlope
  rw [Real.sqrt_mul h₂.le]
  have hA : Real.sqrt S₂ * Real.sqrt (N : ℝ) ≠ 0 :=
    ne_of_gt (mul_pos hsq2 hsqN)
  have hS1 : S₁ ≠ 0 := ne_of_gt h₁
  have hN0 : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt hsqN
  have hS20 : Real.sqrt S₂ ≠ 0 := ne_of_gt hsq2
  field_simp [hA, hS1, hN0, hS20]
  rw [Real.sq_sqrt h₂.le]

end Qatlib.Papers.SpatialSearch03.MainResults
