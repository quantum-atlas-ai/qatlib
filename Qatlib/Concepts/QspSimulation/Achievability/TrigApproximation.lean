/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Qatlib.Concepts.QspSimulation.Achievability.ExponentialPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.BigOperators

/-!
# Real trigonometric Taylor approximations

This module extracts real cosine and sine approximants from the finite Taylor polynomial for
`exp (-I * t * x)`. The definitions `cosineTaylorPolynomial` and `sineTaylorPolynomial` take the
real and negated imaginary coefficients, respectively. Their parity, degree bounds, and uniform
errors on `[-1, 1]` prepare bounded real polynomials for phase synthesis. Taylor approximation
of Hamiltonian evolution is the underlying approach in [BerryEtAl2015Taylor].

Both polynomials inherit the common bound `exponentialTaylorError`. When this bound is below
one, their quarter-scaled versions have absolute value strictly below one half;
`trigTaylor_exists_degree` supplies a common truncation index for any positive target error.

## Main statements

* `exponentialTaylorPolynomial_eval_eq_trig` splits the complex polynomial into the real cosine
  and sine components.
* `cosineTaylorPolynomial_comp_neg_X` and `sineTaylorPolynomial_comp_neg_X` establish even and
  odd parity.
* `cosineTaylorPolynomial_error_le` and `sineTaylorPolynomial_error_le` transfer the exponential
  remainder bound to both real approximants.
* `scaledCosineTaylorPolynomial_abs_lt_half` and `scaledSineTaylorPolynomial_abs_lt_half`
  provide the strict boundedness needed after scaling.
* `trigTaylor_exists_degree` gives simultaneous uniform approximation with the scaled
  boundedness conditions.

## References

* [Berry, Childs, Cleve, Kothari, and Somma, 2015][BerryEtAl2015Taylor]
-/

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial Filter
open scoped BigOperators Topology ComplexConjugate

/-- The real polynomial formed from the real parts of the first `n` exponential Taylor
coefficients for time `t`. -/
noncomputable def cosineTaylorPolynomial (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, monomial k (exponentialTaylorCoefficient t k).re

/-- The real polynomial formed from the negated imaginary parts of the first `n` exponential
Taylor coefficients for time `t`. -/
noncomputable def sineTaylorPolynomial (t : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, monomial k (-(exponentialTaylorCoefficient t k).im)

/-- At a real argument, the cosine Taylor polynomial equals the real part of the complex
exponential Taylor polynomial. -/
theorem cosineTaylorPolynomial_eval (t : ℝ) (n : ℕ) (x : ℝ) :
    (cosineTaylorPolynomial t n).eval x =
      ((exponentialTaylorPolynomial t n).eval (x : ℂ)).re := by
  simp [cosineTaylorPolynomial, Polynomial.eval_finsetSum,
    exponentialTaylorPolynomial_eval, Complex.re_sum, ← Complex.ofReal_pow, Complex.mul_re]

/-- At a real argument, the sine Taylor polynomial equals the negated imaginary part of the
complex exponential Taylor polynomial. -/
theorem sineTaylorPolynomial_eval (t : ℝ) (n : ℕ) (x : ℝ) :
    (sineTaylorPolynomial t n).eval x =
      -((exponentialTaylorPolynomial t n).eval (x : ℂ)).im := by
  simp [sineTaylorPolynomial, Polynomial.eval_finsetSum,
    exponentialTaylorPolynomial_eval, Complex.im_sum, ← Complex.ofReal_pow,
    Complex.mul_im, Finset.sum_neg_distrib]

/-- At a real argument, the exponential Taylor polynomial is the cosine approximant minus `I`
times the sine approximant. -/
theorem exponentialTaylorPolynomial_eval_eq_trig (t : ℝ) (n : ℕ) (x : ℝ) :
    (exponentialTaylorPolynomial t n).eval (x : ℂ) =
      (((cosineTaylorPolynomial t n).eval x : ℝ) : ℂ) -
        Complex.I * (((sineTaylorPolynomial t n).eval x : ℝ) : ℂ) := by
  rw [cosineTaylorPolynomial_eval, sineTaylorPolynomial_eval]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Negating a real argument conjugates the value of the exponential Taylor polynomial. -/
theorem exponentialTaylorPolynomial_eval_neg_conj (t : ℝ) (n : ℕ) (x : ℝ) :
    (exponentialTaylorPolynomial t n).eval (-x : ℂ) =
      conj ((exponentialTaylorPolynomial t n).eval (x : ℂ)) := by
  simp [exponentialTaylorPolynomial_eval_sum, _root_.map_sum, _root_.map_pow, _root_.map_mul]

/-- The cosine Taylor polynomial has the same value at opposite real arguments. -/
theorem cosineTaylorPolynomial_eval_neg (t : ℝ) (n : ℕ) (x : ℝ) :
    (cosineTaylorPolynomial t n).eval (-x) = (cosineTaylorPolynomial t n).eval x := by
  rw [cosineTaylorPolynomial_eval, cosineTaylorPolynomial_eval]
  simpa using congrArg Complex.re (exponentialTaylorPolynomial_eval_neg_conj t n x)

/-- The sine Taylor polynomial changes sign when its real argument is negated. -/
theorem sineTaylorPolynomial_eval_neg (t : ℝ) (n : ℕ) (x : ℝ) :
    (sineTaylorPolynomial t n).eval (-x) = -(sineTaylorPolynomial t n).eval x := by
  simp only [sineTaylorPolynomial_eval, Complex.ofReal_neg,
    exponentialTaylorPolynomial_eval_neg_conj, Complex.conj_im, neg_neg]

/-- Composition of the cosine Taylor polynomial with `-X` leaves it unchanged, expressing even
parity. -/
theorem cosineTaylorPolynomial_comp_neg_X (t : ℝ) (n : ℕ) :
    (cosineTaylorPolynomial t n).comp (-X) = cosineTaylorPolynomial t n := by
  apply Polynomial.funext
  intro x
  simpa using cosineTaylorPolynomial_eval_neg t n x

/-- Composition of the sine Taylor polynomial with `-X` negates it, expressing odd parity. -/
theorem sineTaylorPolynomial_comp_neg_X (t : ℝ) (n : ℕ) :
    (sineTaylorPolynomial t n).comp (-X) = -sineTaylorPolynomial t n := by
  apply Polynomial.funext
  intro x
  simpa using sineTaylorPolynomial_eval_neg t n x

/-- The natural degree of the cosine Taylor polynomial with `n` terms is at most `n - 1`. -/
theorem cosineTaylorPolynomial_natDegree_le (t : ℝ) (n : ℕ) :
    (cosineTaylorPolynomial t n).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (by
    have hkn := Finset.mem_range.mp hk
    omega)

/-- The natural degree of the sine Taylor polynomial with `n` terms is at most `n - 1`. -/
theorem sineTaylorPolynomial_natDegree_le (t : ℝ) (n : ℕ) :
    (sineTaylorPolynomial t n).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (by
    have hkn := Finset.mem_range.mp hk
    omega)

/-- The real part of `exp (-I * t * x)` is `cos (t * x)` for real `t` and `x`. -/
theorem exponentialTarget_re (t x : ℝ) :
    (Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))).re = Real.cos (t * x) := by
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

/-- The imaginary part of `exp (-I * t * x)` is `-sin (t * x)` for real `t` and `x`. -/
theorem exponentialTarget_im (t x : ℝ) :
    (Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))).im = -Real.sin (t * x) := by
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]

/-- If `2 * |t| ≤ n + 1`, the cosine approximation error on `[-1, 1]` is at most
`exponentialTaylorError t n`. -/
theorem cosineTaylorPolynomial_error_le (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(cosineTaylorPolynomial t n).eval x - Real.cos (t * x)| ≤
      exponentialTaylorError t n := by
  have h := (Complex.abs_re_le_norm
    ((exponentialTaylorPolynomial t n).eval (x : ℂ) -
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)))).trans
        (exponentialTaylorPolynomial_error_le t n hn hx)
  simpa only [Complex.sub_re, exponentialTarget_re, cosineTaylorPolynomial_eval] using h

/-- If `2 * |t| ≤ n + 1`, the sine approximation error on `[-1, 1]` is at most
`exponentialTaylorError t n`. -/
theorem sineTaylorPolynomial_error_le (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(sineTaylorPolynomial t n).eval x - Real.sin (t * x)| ≤
      exponentialTaylorError t n := by
  rw [sineTaylorPolynomial_eval]
  have he : -((exponentialTaylorPolynomial t n).eval (x : ℂ)).im - Real.sin (t * x) =
      -(((exponentialTaylorPolynomial t n).eval (x : ℂ) -
        Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))).im) := by
    rw [Complex.sub_im, exponentialTarget_im]
    ring
  rw [he, abs_neg]
  exact (Complex.abs_im_le_norm _).trans (exponentialTaylorPolynomial_error_le t n hn hx)

/-- Under the time-cutoff condition and remainder bound below one, the cosine Taylor polynomial
has absolute value below two on `[-1, 1]`. -/
theorem cosineTaylorPolynomial_abs_lt_two (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) (hE : exponentialTaylorError t n < 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(cosineTaylorPolynomial t n).eval x| < 2 := by
  have h := abs_le.mp (cosineTaylorPolynomial_error_le t n hn hx)
  apply abs_lt.mpr
  constructor
  · linarith [Real.neg_one_le_cos (t * x)]
  · linarith [Real.cos_le_one (t * x)]

/-- Under the time-cutoff condition and remainder bound below one, the sine Taylor polynomial
has absolute value below two on `[-1, 1]`. -/
theorem sineTaylorPolynomial_abs_lt_two (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) (hE : exponentialTaylorError t n < 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(sineTaylorPolynomial t n).eval x| < 2 := by
  have h := abs_le.mp (sineTaylorPolynomial_error_le t n hn hx)
  apply abs_lt.mpr
  constructor
  · linarith [Real.neg_one_le_sin (t * x)]
  · linarith [Real.sin_le_one (t * x)]

/-- Under the time-cutoff condition and remainder bound below one, the quarter-scaled cosine
Taylor polynomial has absolute value below one half on `[-1, 1]`. -/
theorem scaledCosineTaylorPolynomial_abs_lt_half (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) (hE : exponentialTaylorError t n < 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(C (1 / 4 : ℝ) * cosineTaylorPolynomial t n).eval x| < 1 / 2 := by
  have h := cosineTaylorPolynomial_abs_lt_two t n hn hE hx
  simp only [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
  norm_num
  linarith

/-- Under the time-cutoff condition and remainder bound below one, the quarter-scaled sine
Taylor polynomial has absolute value below one half on `[-1, 1]`. -/
theorem scaledSineTaylorPolynomial_abs_lt_half (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) (hE : exponentialTaylorError t n < 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(C (1 / 4 : ℝ) * sineTaylorPolynomial t n).eval x| < 1 / 2 := by
  have h := sineTaylorPolynomial_abs_lt_two t n hn hE hx
  simp only [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
  norm_num
  linarith

/-- The absolute error between one quarter of `a` and one quarter of `b` is one quarter of their
absolute difference. -/
private theorem quarter_abs_sub (a b : ℝ) :
    |(1 / 4) * a - b / 4| = |a - b| / 4 := by
  rw [show (1 / 4) * a - b / 4 = (a - b) / 4 by ring, abs_div]
  norm_num

/-- Under the time-cutoff condition, quarter scaling bounds the cosine approximation error on
`[-1, 1]` by one quarter of `exponentialTaylorError t n`. -/
theorem scaledCosineTaylorPolynomial_error_le (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(C (1 / 4 : ℝ) * cosineTaylorPolynomial t n).eval x - Real.cos (t * x) / 4| ≤
      exponentialTaylorError t n / 4 := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, quarter_abs_sub]
  exact div_le_div_of_nonneg_right (cosineTaylorPolynomial_error_le t n hn hx) (by norm_num)

/-- Under the time-cutoff condition, quarter scaling bounds the sine approximation error on
`[-1, 1]` by one quarter of `exponentialTaylorError t n`. -/
theorem scaledSineTaylorPolynomial_error_le (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(C (1 / 4 : ℝ) * sineTaylorPolynomial t n).eval x - Real.sin (t * x) / 4| ≤
      exponentialTaylorError t n / 4 := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, quarter_abs_sub]
  exact div_le_div_of_nonneg_right (sineTaylorPolynomial_error_le t n hn hx) (by norm_num)

/-- For every real time and positive tolerance, a common truncation index gives uniform cosine
and sine errors below that tolerance on `[-1, 1]`, with both quarter-scaled polynomials
bounded strictly by one half. -/
theorem trigTaylor_exists_degree (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(cosineTaylorPolynomial t n).eval x - Real.cos (t * x)| < ε ∧
      |(sineTaylorPolynomial t n).eval x - Real.sin (t * x)| < ε ∧
      |(C (1 / 4 : ℝ) * cosineTaylorPolynomial t n).eval x| < 1 / 2 ∧
      |(C (1 / 4 : ℝ) * sineTaylorPolynomial t n).eval x| < 1 / 2 := by
  obtain ⟨N, hN⟩ := exponentialTaylor_eventually_error_lt t (lt_min hε zero_lt_one)
  have hs := hN N le_rfl
  have hEε : exponentialTaylorError t N < ε := hs.2.1.trans_le (min_le_left _ _)
  have hE1 : exponentialTaylorError t N < 1 := hs.2.1.trans_le (min_le_right _ _)
  refine ⟨N, fun x hx => ?_⟩
  exact ⟨(cosineTaylorPolynomial_error_le t N hs.1 hx).trans_lt hEε,
    (sineTaylorPolynomial_error_le t N hs.1 hx).trans_lt hEε,
    scaledCosineTaylorPolynomial_abs_lt_half t N hs.1 hE1 hx,
    scaledSineTaylorPolynomial_abs_lt_half t N hs.1 hE1 hx⟩

end Qatlib.Concepts.QspSimulation.Achievability
