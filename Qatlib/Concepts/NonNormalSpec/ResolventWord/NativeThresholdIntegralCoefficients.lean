/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralDefs
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralAmplification

/-!
# Semantics of rational threshold coefficients

Rational coefficient lists implement composition, threshold polynomials, and integration with
zero constant term. The results identify their real polynomial interpretations with
`thresholdPolynomial` and `integratedThresholdPolynomial`, supporting polynomial transformations
in the setting of [GilyenSuLowWiebe2019]

## Main statements

* `rationalPolynomialCompose_semantics`: identifies list composition with polynomial
  composition.
* `rationalIntegralCoefficients_semantics`: identifies scaled integration with
  `thresholdIntegralPrimitive`.
* `rationalIntegratedThresholdCoefficients_semantics`: identifies the native amplifier
  coefficients.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

open Polynomial

/-- Interpreting the rational composition coefficient list over the reals gives the composition
of the two interpreted polynomials. -/
theorem rationalPolynomialCompose_semantics (xs ys : List ℚ) :
    realTarget (rationalPolynomialCompose xs ys) =
      (realTarget xs).comp (realTarget ys) := by
  induction xs with
  | nil => simp [rationalPolynomialCompose]
  | cons x xs ih =>
    rw [rationalPolynomialCompose, realTarget_add, realTarget_mul, ih]
    simp only [realTarget_cons, realTarget_nil, mul_zero, add_zero,
      Polynomial.add_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp]
    ring

/-- The real interpretation of the rational threshold coefficient list is `thresholdPolynomial`
at the cast threshold. -/
theorem rationalThresholdCoefficients_semantics (τ : ℚ) (k : ℕ) :
    realTarget (rationalThresholdCoefficients τ k) = thresholdPolynomial (τ : ℝ) k := by
  rw [rationalThresholdCoefficients, realTarget_div, realTarget_add,
    rationalPolynomialCompose_semantics, rationalSignCoefficients_semantics]
  apply Polynomial.funext
  intro x
  simp [realTarget_cons, Polynomial.eval_comp, thresholdPolynomial_eval]
  ring

/-- The coefficient at index `n + 1` of the scaled integral list is `γ` times the original
coefficient at index `n`, divided by `n + 1`. -/
theorem rationalIntegralCoefficients_getD_succ (γ : ℚ) (xs : List ℚ) (n : ℕ) :
    (rationalIntegralCoefficients γ xs).getD (n + 1) 0 =
      γ * xs.getD n 0 / (n + 1 : ℚ) := by
  rw [rationalIntegralCoefficients, List.getD_cons_succ]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx]
  cases xs[n]? <;> simp

/-- Differentiating the real interpretation of the integral coefficient list gives `γ` times the
original real polynomial. -/
theorem rationalIntegralCoefficients_derivative (γ : ℚ) (xs : List ℚ) :
    (realTarget (rationalIntegralCoefficients γ xs)).derivative =
      Polynomial.C (γ : ℝ) * realTarget xs := by
  ext n
  rw [Polynomial.coeff_derivative, realTarget_coeff,
    rationalIntegralCoefficients_getD_succ, Polynomial.coeff_C_mul, realTarget_coeff]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
  exact div_mul_cancel₀ _ (by positivity)

/-- The real polynomial represented by the integral coefficient list vanishes at zero. -/
@[simp] theorem rationalIntegralCoefficients_eval_zero (γ : ℚ) (xs : List ℚ) :
    (realTarget (rationalIntegralCoefficients γ xs)).eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, realTarget_coeff]
  simp [rationalIntegralCoefficients]

/-- The integral coefficient list represents `γ` times the zero constant term primitive of the
original real polynomial. -/
theorem rationalIntegralCoefficients_semantics (γ : ℚ) (xs : List ℚ) :
    realTarget (rationalIntegralCoefficients γ xs) =
      Polynomial.C (γ : ℝ) * thresholdIntegralPrimitive (realTarget xs) := by
  let q := realTarget (rationalIntegralCoefficients γ xs) -
    Polynomial.C (γ : ℝ) * thresholdIntegralPrimitive (realTarget xs)
  have hder : q.derivative = 0 := by
    simp only [q, Polynomial.derivative_sub, rationalIntegralCoefficients_derivative,
      Polynomial.derivative_C_mul, thresholdIntegralPrimitive_derivative, sub_self]
  have hz : q.eval 0 = 0 := by
    simp [q]
  have hq : q = 0 := by
    calc
      q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hder
      _ = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero, hz]; simp
  exact sub_eq_zero.mp hq

/-- The real interpretation of the rational integrated threshold coefficients is the
corresponding integrated threshold polynomial. -/
theorem rationalIntegratedThresholdCoefficients_semantics (γ δ : ℚ) (k : ℕ) :
    realTarget (rationalIntegratedThresholdCoefficients γ δ k) =
      integratedThresholdPolynomial (γ : ℝ) (δ : ℝ) k := by
  rw [rationalIntegratedThresholdCoefficients, rationalIntegralCoefficients_semantics,
    realTarget_sub, rationalThresholdCoefficients_semantics]
  simp only [realTarget_cons, realTarget_nil, Rat.cast_one, Polynomial.C_1,
    mul_zero, add_zero]
  have hcast : (((1 - δ / 2) / γ : ℚ) : ℝ) =
      (1 - (δ : ℝ) / 2) / (γ : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  rfl

end Qatlib.Concepts.NonNormalSpec.ResolventWord
