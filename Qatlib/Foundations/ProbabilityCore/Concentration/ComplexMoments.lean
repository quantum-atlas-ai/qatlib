/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift
public import Mathlib.MeasureTheory.Integral.Gamma

@[expose] public section


/-! # Actual radial moments of the standard complex Gaussian

Demand: LinearOptics10 Gaussian Fock and permanent moment bridges. Polar
integration gives every integral of normSq(z)^k against the actual plane
density as k factorial. No moment value or Gaussian law is an assumption.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMoments
open Qatlib.Foundations.ProbabilityCore.Concentration.ComplexShift

/-- The actual scalar Gaussian power integral is Gamma(alpha+1) throughout alpha>-1. -/
theorem radialPower (alpha : ℝ) (ha : -1 < alpha) :
    (∫ z : ℂ, Complex.normSq z ^ alpha * density z ∂volume) =
      Real.Gamma (alpha+1) := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2*alpha)
    (by norm_num) (by linarith)
  have hc : (fun z : ℂ => Complex.normSq z ^ alpha * density z) =
      fun z => Real.pi⁻¹ * (‖z‖ ^ (2*alpha) * Real.exp (-‖z‖^(2 : ℝ))) := by
    funext z
    have he : (‖z‖^2 : ℝ)^alpha = ‖z‖^(2*alpha) :=
      (Real.rpow_natCast_mul (norm_nonneg z) 2 alpha).symm
    simp only [density, Complex.normSq_eq_norm_sq, he, Real.rpow_two]
    ring
  rw [hc, integral_const_mul, h]
  have hg : ((2*alpha+2)/2) = alpha+1 := by ring
  rw [hg]
  field_simp

/-- Every actual nonnegative integer radial moment of the standard complex Gaussian is factorial. -/
theorem radialMoment (k : ℕ) :
    (∫ z : ℂ, Complex.normSq z ^ k * density z ∂volume) = (k.factorial : ℝ) := by
  have h := Complex.integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2*(k : ℝ))
    (by norm_num) (by have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k; linarith)
  have hc : (fun z : ℂ => Complex.normSq z ^ k * density z) =
      fun z => Real.pi⁻¹ * (‖z‖ ^ (2*(k : ℝ)) * Real.exp (-‖z‖^(2 : ℝ))) := by
    funext z
    rw [density, Complex.normSq_eq_norm_sq, ← pow_mul, ← Real.rpow_natCast,
      Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.rpow_two]
    ring
  rw [hc, integral_const_mul, h]
  have hg : ((2*(k : ℝ)+2)/2) = (k : ℝ)+1 := by ring
  rw [hg, Real.Gamma_nat_eq_factorial]
  field_simp

end Qatlib.Foundations.ProbabilityCore.Concentration.ComplexMoments
