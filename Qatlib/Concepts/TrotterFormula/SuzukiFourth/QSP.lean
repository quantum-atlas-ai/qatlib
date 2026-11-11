/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.Phase

/-!
# Polynomial responses for quantum signal processing

This module defines a recursive pair of complex response polynomials and proves their
recurrences, parity, and degree bounds. For unit-modulus base and phase parameters, the pair
satisfies a weighted squared-norm identity, following the polynomial-response viewpoint of
quantum signal processing [LowChuang2017].

On the real interval `[-1, 1]`, the weighted identity bounds the squared norm of the first
response by one.

## Main statements

* `response`: the recursive response pair with initial value `(C base, 0)`.
* `response_parity`: opposite parity of the two response components.
* `response_degree`: degree bounds in terms of the phase-list length.
* `response_normalization`: the weighted squared-norm identity.
* `response_normSq_le_one`: the first-component bound on `[-1, 1]`.

## References

* [Low and Chuang, 2017][LowChuang2017]
* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.TrotterFormula.SuzukiFourth

open Matrix Polynomial

/-- The pair of complex polynomials obtained from initial pair `(C base, 0)` by recursively
applying the phase-weighted response update along the list. -/
noncomputable def response (base : ℂ) : List ℂ → Polynomial ℂ × Polynomial ℂ
  | [] => (C base, 0)
  | z :: zs =>
    let pq := response base zs
    (C z * (X * pq.1 + (1 - X ^ 2) * pq.2),
      C (star z) * (pq.1 - X * pq.2))

/-- The first polynomial component of `response base zs`. -/
noncomputable def responseP (base : ℂ) (zs : List ℂ) : Polynomial ℂ := (response base zs).1

/-- The second polynomial component of `response base zs`. -/
noncomputable def responseQ (base : ℂ) (zs : List ℂ) : Polynomial ℂ := (response base zs).2

/-- The first response for an empty phase list is the constant polynomial `C base`. -/
@[simp] theorem responseP_nil (base : ℂ) : responseP base [] = C base := rfl

/-- The second response for an empty phase list is zero. -/
@[simp] theorem responseQ_nil (base : ℂ) : responseQ base [] = 0 := rfl

/-- Prepending `z` updates the first response to `C z * (X * P + (1 - X²) * Q)`. -/
@[simp] theorem responseP_cons (base z : ℂ) (zs : List ℂ) :
    responseP base (z :: zs) =
      C z * (X * responseP base zs + (1 - X ^ 2) * responseQ base zs) := rfl

/-- Prepending `z` updates the second response to `C (star z) * (P - X * Q)`. -/
@[simp] theorem responseQ_cons (base z : ℂ) (zs : List ℂ) :
    responseQ base (z :: zs) = C (star z) * (responseP base zs - X * responseQ base zs) := rfl

/-- For a singleton list `[z]`, the first response is `C (z * base) * X`. -/
theorem responseP_singleton (base z : ℂ) :
    responseP base [z] = C (z * base) * X := by
  simp [responseP_cons]
  ring

/-- Negating the evaluation point multiplies the first response by `(-1) ^ zs.length` and the
second by its negative. -/
theorem response_parity (base : ℂ) (zs : List ℂ) (x : ℂ) :
    (responseP base zs).eval (-x) = (-1) ^ zs.length * (responseP base zs).eval x ∧
    (responseQ base zs).eval (-x) = -((-1) ^ zs.length) * (responseQ base zs).eval x := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [responseP_cons, responseQ_cons, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_pow, List.length_cons, pow_succ]
    rw [ih.1, ih.2]
    constructor <;> ring

/-- Multiplying a complex polynomial by a constant polynomial does not increase its natural
degree. -/
private theorem scalar_natDegree_le (c : ℂ) (p : Polynomial ℂ) :
    (C c * p).natDegree ≤ p.natDegree := by
  calc
    (C c * p).natDegree ≤ (C c).natDegree + p.natDegree := by
      apply Polynomial.natDegree_mul_le
    _ = p.natDegree := by simp

/-- The first response has natural degree at most the list length, and the second is zero or has
natural degree plus one at most that length. -/
theorem response_degree (base : ℂ) (zs : List ℂ) :
    (responseP base zs).natDegree ≤ zs.length ∧
    (responseQ base zs = 0 ∨ (responseQ base zs).natDegree + 1 ≤ zs.length) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hx : (X * responseP base zs).natDegree ≤ zs.length + 1 := by
      calc
        (X * responseP base zs).natDegree ≤
            (X : Polynomial ℂ).natDegree + (responseP base zs).natDegree := by
          apply Polynomial.natDegree_mul_le
        _ ≤ zs.length + 1 := by simp only [Polynomial.natDegree_X]; omega
    have hxq : (X * responseQ base zs).natDegree ≤ zs.length := by
      rcases ih.2 with hq | hq
      · simp [hq]
      · calc
          (X * responseQ base zs).natDegree ≤
              (X : Polynomial ℂ).natDegree + (responseQ base zs).natDegree := by
            apply Polynomial.natDegree_mul_le
          _ ≤ zs.length := by simp only [Polynomial.natDegree_X]; omega
    have hfactor : (1 - X ^ 2 : Polynomial ℂ).natDegree ≤ 2 := by
      calc
        (1 - X ^ 2 : Polynomial ℂ).natDegree ≤
            max (1 : Polynomial ℂ).natDegree ((X : Polynomial ℂ) ^ 2).natDegree := by
          apply Polynomial.natDegree_sub_le
        _ ≤ 2 := by simp
    have hq2 : ((1 - X ^ 2) * responseQ base zs).natDegree ≤ zs.length + 1 := by
      rcases ih.2 with hq | hq
      · simp [hq]
      · calc
          ((1 - X ^ 2) * responseQ base zs).natDegree ≤
              (1 - X ^ 2 : Polynomial ℂ).natDegree + (responseQ base zs).natDegree := by
            apply Polynomial.natDegree_mul_le
          _ ≤ zs.length + 1 := by omega
    constructor
    · rw [responseP_cons, List.length_cons]
      exact (scalar_natDegree_le _ _).trans
        ((Polynomial.natDegree_add_le _ _).trans (max_le hx hq2))
    · right
      rw [responseQ_cons, List.length_cons]
      have hqnew : (C (star z) * (responseP base zs - X * responseQ base zs)).natDegree ≤
          zs.length := by
        exact (scalar_natDegree_le _ _).trans
          ((Polynomial.natDegree_sub_le _ _).trans (max_le ih.1 hxq))
      omega

/-- A complex number satisfying `IsPhase` has squared norm one. -/
theorem IsPhase.normSq {z : ℂ} (hz : IsPhase z) : Complex.normSq z = 1 := by
  have hr := congrArg Complex.re hz
  simpa [Complex.normSq_apply, Complex.mul_re] using hr

/-- For a unit-modulus phase and real `x`, one response update preserves the quantity `normSq p
+ (1 - x²) * normSq q`. -/
private theorem step_normSq {z : ℂ} (hz : IsPhase z) (x : ℝ) (p q : ℂ) :
    Complex.normSq (z * ((x : ℂ) * p + (1 - (x : ℂ) ^ 2) * q)) +
      (1 - x ^ 2) * Complex.normSq (star z * (p - (x : ℂ) * q)) =
      Complex.normSq p + (1 - x ^ 2) * Complex.normSq q := by
  have hs : IsPhase (star z) := by
    unfold IsPhase at hz ⊢
    simpa only [star_star, mul_comm] using hz
  rw [Complex.normSq_mul, Complex.normSq_mul, IsPhase.normSq hz, IsPhase.normSq hs, one_mul,
      one_mul]
  simp only [Complex.normSq_apply, pow_two, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

/-- For a unit-modulus base and phase list, the response evaluations at every real `x` satisfy
`normSq P(x) + (1 - x²) * normSq Q(x) = 1`. -/
theorem response_normalization {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) (x : ℝ) :
    Complex.normSq ((responseP base zs).eval (x : ℂ)) +
      (1 - x ^ 2) * Complex.normSq ((responseQ base zs).eval (x : ℂ)) = 1 := by
  induction zs with
  | nil => simpa using IsPhase.normSq hb
  | cons z zs ih =>
    simp only [responseP_cons, responseQ_cons, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_pow]
    rw [step_normSq (hzs z (by simp))]
    exact ih (fun w hw => hzs w (List.mem_cons_of_mem z hw))

/-- For a unit-modulus base and phase list, the first response evaluated at a real `x ∈ [-1, 1]`
has squared norm at most one. -/
theorem response_normSq_le_one {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    Complex.normSq ((responseP base zs).eval (x : ℂ)) ≤ 1 := by
  have hi := response_normalization hb zs hzs x
  have hd : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hq := Complex.normSq_nonneg ((responseQ base zs).eval (x : ℂ))
  nlinarith [mul_nonneg hd hq]

end Qatlib.Concepts.TrotterFormula.SuzukiFourth
