/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The time-dependent radial kernel of the Hopf pulse

[IrvineBouwmeester2008KnottedLight], equation (4) and Supplementary
Methods 1. Adding the positive-frequency factor `exp (-i k t)` to
the radial Laplace–sine kernel gives a complex rational function at
all real times.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open MeasureTheory

/-- The time-phased Laplace–sine integral has a rational expression for
every real radius and time, including zero radius. -/
theorem integral_hopf_time_mul_sin (r t : ℝ) :
    (∫ k in Set.Ioi (0 : ℝ), Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) *
      (Real.sin (r * k) : ℂ)) = (r : ℂ) / ((1 + Complex.I * (t : ℂ)) ^ 2 + (r : ℂ) ^ 2) := by
  let z : ℂ := 1 + Complex.I * (t : ℂ)
  let a : ℂ := -z + Complex.I * (r : ℂ)
  let b : ℂ := -z - Complex.I * (r : ℂ)
  have ha : a.re < 0 := by
    simp [a, z, Complex.add_re, Complex.mul_re]
  have hb : b.re < 0 := by
    simp [b, z, Complex.sub_re, Complex.add_re, Complex.mul_re]
  have ha₀ : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hb₀ : b ≠ 0 := by
    intro h
    simp [h] at hb
  change (∫ k in Set.Ioi (0 : ℝ), Complex.exp (-z * (k : ℂ)) *
    (Real.sin (r * k) : ℂ)) = (r : ℂ) / (z ^ 2 + (r : ℂ) ^ 2)
  have hintegrand : (fun k : ℝ => Complex.exp (-z * (k : ℂ)) * (Real.sin (r * k) : ℂ)) =
      fun k : ℝ => (Complex.I / 2) * (Complex.exp (b * (k : ℂ)) - Complex.exp (a * (k : ℂ))) := by
    funext k
    have hplus : a * (k : ℂ) = -z * (k : ℂ) + ((r * k : ℝ) : ℂ) * Complex.I := by
      dsimp [a]
      push_cast
      ring
    have hminus : b * (k : ℂ) = -z * (k : ℂ) + -((r * k : ℝ) : ℂ) * Complex.I := by
      dsimp [b]
      push_cast
      ring
    rw [Complex.ofReal_sin, Complex.sin, hminus, hplus, Complex.exp_add, Complex.exp_add]
    ring
  have hproduct : a * b = z ^ 2 + (r : ℂ) ^ 2 := by
    dsimp [a, b]
    linear_combination -((r : ℂ) ^ 2) * Complex.I_mul_I
  have hdiff : b - a = -(2 : ℂ) * Complex.I * (r : ℂ) := by
    dsimp [a, b]
    ring
  rw [hintegrand, integral_const_mul,
    integral_sub (integrableOn_exp_mul_complex_Ioi hb 0) (integrableOn_exp_mul_complex_Ioi ha 0),
    integral_exp_mul_complex_Ioi hb, integral_exp_mul_complex_Ioi ha]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  calc
    _ = (Complex.I / 2) * ((b - a) / (a * b)) := by
      field_simp [ha₀, hb₀]
      ring
    _ = (r : ℂ) / (z ^ 2 + (r : ℂ) ^ 2) := by
      rw [← hproduct, hdiff, ← mul_div_assoc]
      congr 1
      linear_combination -(r : ℂ) * Complex.I_mul_I

end Qatlib.Papers.KnottedLight08.CurlEigenstate
