/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Gaussian band mass estimates

Defines the standard normal density and its integral over a symmetric band. Explicit upper and
lower linear bounds on the band mass provide the Gaussian estimates used alongside the
perceptron analysis in [WiebeKapoorSvore2016].

## Main statements

* `band_mass_linear_bounds`: There are positive absolute constants bounding the symmetric
  Gaussian band mass above and below by constant multiples of `γ` on the interval `[0, 1]`.
* `band_mass_lower_coefficient`: For `0 ≤ γ ≤ 1`, the symmetric Gaussian band mass is at least
  `γ / sqrt (2 * pi)`.

## References

* [Wiebe et al., 2016][WiebeKapoorSvore2016]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPerceptron16.GaussianBand

open MeasureTheory intervalIntegral

/-- The standard normal density `exp (-x^2 / 2) / sqrt (2 * pi)`. -/
def stdNormalDensity (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- The interval integral of the standard normal density from `-γ` to `γ`. -/
def gaussianBandMass (γ : ℝ) : ℝ := ∫ x in (-γ)..γ, stdNormalDensity x

/-- The standard normal density is nonnegative at every real argument. -/
theorem stdNormalDensity_nonneg (x : ℝ) : 0 ≤ stdNormalDensity x := by
  unfold stdNormalDensity
  positivity

/-- The standard normal density is continuous. -/
theorem continuous_stdNormalDensity : Continuous stdNormalDensity := by
  unfold stdNormalDensity
  fun_prop

/-- The standard normal density is interval integrable between any two real endpoints. -/
theorem intervalIntegrable_stdNormalDensity (a b : ℝ) :
    IntervalIntegrable stdNormalDensity volume a b :=
  continuous_stdNormalDensity.intervalIntegrable _ _

/-- For nonnegative `γ`, the symmetric band mass is at most `2 * γ / sqrt (2 * pi)`. -/
theorem gaussianBandMass_upper (γ : ℝ) (hγ : 0 ≤ γ) :
    gaussianBandMass γ ≤ 2 * (Real.sqrt (2 * Real.pi))⁻¹ * γ := by
  have hpt : ∀ x ∈ Set.Icc (-γ) γ, stdNormalDensity x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x _
    unfold stdNormalDensity
    have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg x]
    have hcoef : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
      have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      positivity
    calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)
        ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 := by
          apply mul_le_mul_of_nonneg_left hexp hcoef
      _ = (Real.sqrt (2 * Real.pi))⁻¹ := by ring
  have hmono := intervalIntegral.integral_mono_on (show -γ ≤ γ by linarith)
    (intervalIntegrable_stdNormalDensity _ _) intervalIntegrable_const hpt
  have hconst : (∫ _x in (-γ)..γ, (Real.sqrt (2 * Real.pi))⁻¹)
      = 2 * (Real.sqrt (2 * Real.pi))⁻¹ * γ := by
    rw [intervalIntegral.integral_const]
    simp
    ring
  calc gaussianBandMass γ ≤ ∫ _x in (-γ)..γ, (Real.sqrt (2 * Real.pi))⁻¹ := hmono
    _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ * γ := hconst

/-- For `0 ≤ γ ≤ 1`, the symmetric band mass is at least `2 * exp (-1 / 2) * γ / sqrt (2 * pi)`. -/
theorem gaussianBandMass_lower (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    2 * Real.exp (-(1 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ * γ ≤ gaussianBandMass γ := by
  have hpt : ∀ x ∈ Set.Icc (-γ) γ,
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2)) ≤ stdNormalDensity x := by
    intro x hx
    unfold stdNormalDensity
    apply mul_le_mul_of_nonneg_left _ (by
      have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
      positivity)
    apply Real.exp_le_exp_of_le
    have hx2 : x ^ 2 ≤ 1 := by
      rw [Set.mem_Icc] at hx
      nlinarith [hx.1, hx.2]
    nlinarith
  have hmono := intervalIntegral.integral_mono_on (show -γ ≤ γ by linarith)
    intervalIntegrable_const (intervalIntegrable_stdNormalDensity _ _) hpt
  have hconst : (∫ _x in (-γ)..γ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2)))
      = 2 * Real.exp (-(1 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ * γ := by
    rw [intervalIntegral.integral_const]
    simp
    ring
  calc (2 * Real.exp (-(1 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ * γ)
      = ∫ _x in (-γ)..γ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2)) := hconst.symm
    _ ≤ gaussianBandMass γ := hmono

/-- There are positive absolute constants bounding the symmetric Gaussian band mass above and
below by constant multiples of `γ` on the interval `[0, 1]`. -/
theorem band_mass_linear_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
        c₁ * γ ≤ gaussianBandMass γ ∧ gaussianBandMass γ ≤ c₂ * γ := by
  refine ⟨2 * Real.exp (-(1 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹,
    2 * (Real.sqrt (2 * Real.pi))⁻¹, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have h1 : (0 : ℝ) < Real.exp (-(1 / 2)) := Real.exp_pos _
    positivity
  · have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  · intro γ hγ0 hγ1
    exact ⟨gaussianBandMass_lower γ hγ0 hγ1, gaussianBandMass_upper γ hγ0⟩

/-- For `0 ≤ γ ≤ 1`, the symmetric Gaussian band mass is at least `γ / sqrt (2 * pi)`. -/
theorem band_mass_lower_coefficient (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (Real.sqrt (2 * Real.pi))⁻¹ * γ ≤ gaussianBandMass γ := by
  have hexp_half : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    have := Real.one_sub_le_exp_neg (1 / 2 : ℝ)
    linarith
  have h2e : (1 : ℝ) ≤ 2 * Real.exp (-(1 / 2)) := by linarith
  have hcoef : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * γ := by
    have : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hlower := gaussianBandMass_lower γ hγ0 hγ1
  calc (Real.sqrt (2 * Real.pi))⁻¹ * γ
      = 1 * ((Real.sqrt (2 * Real.pi))⁻¹ * γ) := by ring
    _ ≤ (2 * Real.exp (-(1 / 2))) * ((Real.sqrt (2 * Real.pi))⁻¹ * γ) := by
        apply mul_le_mul_of_nonneg_right h2e hcoef
    _ = 2 * Real.exp (-(1 / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ * γ := by ring
    _ ≤ gaussianBandMass γ := hlower

end Qatlib.Papers.QPerceptron16.GaussianBand
