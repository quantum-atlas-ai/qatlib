/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalDerivatives
public import Qatlib.Papers.KnotLight13.Bateman.Construction

/-! Regression consumers for the actual spacetime partials and Bateman compatibility
of the rational pair. The witness point (1, 2, 3, 4) is nondegenerate: the common
denominator never vanishes on real space-time, the partials match independently
computed values, and the field is computed there to be a nonzero null field.
The compatibility premise is shown to be indispensable by the preserved
coordinate-gradient counterexample. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnotLight13.Bateman
open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnotLight13.TorusFamily

-- The common denominator stays invertible at the witness point.
example : complexDenominator 1 2 3 4 ≠ 0 := complex_denominator_ne_zero 1 2 3 4

-- The x partial of α at the witness point matches its independently computed value.
example : (alphaGradient 1 2 3 4) 0 = (-(316 : ℂ) - Complex.I * 188) / 4225 := by
  have hne : ((-63 : ℂ) - Complex.I * 16) ≠ 0 := by
    intro h
    have h2 : Complex.normSq ((-63 : ℂ) - Complex.I * 16) = 0 := by
      rw [h]
      simp
    norm_num [Complex.normSq_apply] at h2
  have hw2 : complexDenominator 1 2 3 4 ^ 2 = ((-63 : ℂ) - Complex.I * 16) := by
    apply Complex.ext
    · simp [complexDenominator, radialAux, pow_two, Complex.mul_re, Complex.mul_im]
      norm_num
    · simp [complexDenominator, radialAux, pow_two, Complex.mul_re, Complex.mul_im]
      norm_num
  have hx : alphaXNumerator 1 2 3 4 = ((4 : ℂ) + Complex.I * 4) := by
    have h4 : alphaCommonFactor 3 4 = 1 + Complex.I := by
      norm_num [alphaCommonFactor]
    rw [alphaXNumerator, h4]
    push_cast
    ring
  show alphaXNumerator 1 2 3 4 / complexDenominator 1 2 3 4 ^ 2 = _
  rw [hx, hw2, div_eq_div_iff hne (by norm_num)]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [Complex.mul_re, Complex.mul_im]
    norm_num

-- The t partial of β at the witness point matches its independently computed value.
example : betaTimePartial 1 2 3 4 = ((72 : ℂ) + Complex.I * 2396) / 4225 := by
  have hne : ((-63 : ℂ) - Complex.I * 16) ≠ 0 := by
    intro h
    have h2 : Complex.normSq ((-63 : ℂ) - Complex.I * 16) = 0 := by
      rw [h]
      simp
    norm_num [Complex.normSq_apply] at h2
  have hw2 : complexDenominator 1 2 3 4 ^ 2 = ((-63 : ℂ) - Complex.I * 16) := by
    apply Complex.ext
    · simp [complexDenominator, radialAux, pow_two, Complex.mul_re, Complex.mul_im]
      norm_num
    · simp [complexDenominator, radialAux, pow_two, Complex.mul_re, Complex.mul_im]
      norm_num
  have ht : betaTNumerator 1 2 3 4 = ((8 : ℂ) - Complex.I * 36) := by
    apply Complex.ext
    · simp [betaTNumerator, betaReducedNumerator, Complex.mul_re, Complex.mul_im]
      norm_num
    · simp [betaTNumerator, betaReducedNumerator, Complex.mul_re, Complex.mul_im]
      norm_num
  show betaTNumerator 1 2 3 4 / complexDenominator 1 2 3 4 ^ 2 = _
  rw [ht, hw2, div_eq_div_iff hne (by norm_num)]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [Complex.mul_re, Complex.mul_im]
    norm_num

-- The full Bateman relation holds at the witness point, in every component.
example (j : Fin 3) :
    cross3 (alphaGradient 1 2 3 4) (betaGradient 1 2 3 4) j =
      Complex.I * (alphaTimePartial 1 2 3 4 * betaGradient 1 2 3 4 j
        - betaTimePartial 1 2 3 4 * alphaGradient 1 2 3 4 j) :=
  bateman_rational_component 1 2 3 4 j

-- The actual field is null at the witness point and its real parts are
-- perpendicular with equal squared magnitudes.
example : dot3 (rationalField 1 2 3 4) (rationalField 1 2 3 4) = 0 :=
  rational_field_null 1 2 3 4

example : dot3 (fun j => (rationalField 1 2 3 4 j).re) (fun j => (rationalField 1 2 3 4 j).im) = 0 ∧
    squaredLength (fun j => (rationalField 1 2 3 4 j).re) =
      squaredLength (fun j => (rationalField 1 2 3 4 j).im) :=
  rational_field_real_invariants 1 2 3 4

-- The witness field is genuinely nonzero: its first numerator component is
-- computed explicitly and does not vanish.
example : cross3 (alphaGradientNumerators 1 2 3 4) (betaGradientNumerators 1 2 3 4) 0 =
    (-(76 : ℂ) + Complex.I * 88) := by
  apply Complex.ext
  · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator,
      betaXNumerator, betaYNumerator, betaZNumerator,
      alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator,
      betaXNumerator, betaYNumerator, betaZNumerator,
      alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num

example : (-(76 : ℂ) + Complex.I * 88) ≠ 0 := by
  intro h
  have h2 : Complex.normSq ((-(76 : ℂ) + Complex.I * 88)) = 0 := by
    rw [h]
    simp
  norm_num [Complex.normSq_apply] at h2

-- Bateman compatibility is a real premise: coordinate gradients give a non-null field.
example : dot3 (cross3 (![1, 0, 0] : Fin 3 → ℂ) ![0, 1, 0])
    (cross3 (![1, 0, 0] : Fin 3 → ℂ) ![0, 1, 0]) ≠ 0 := arbitrary_cross_not_null
