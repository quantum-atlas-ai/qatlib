/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Taylor polynomials for Hamiltonian phases

This module constructs the first `n` Taylor terms of the scalar phase exponential with argument
minus the imaginary unit times time times the signal. It gives coefficient and degree formulas
and a uniform error bound on the interval from minus one to one. Truncated exponential series
are a standard approximation ingredient in Hamiltonian simulation [BerryEtAl2015Taylor].

## Main statements

* `exponentialTaylorCoefficient` and `exponentialTaylorPolynomial` define the coefficients and
  finite polynomial.
* `exponentialTaylorPolynomial_natDegree` gives the exact degree for nonzero time and positive
  truncation length.
* `exponentialTaylorPolynomial_error_le` bounds the error by `exponentialTaylorError` when `2 *
  |t|` is at most `n + 1`.
* `exponentialTaylor_eventually_error_lt` and `exponentialTaylorPolynomial_tendstoUniformlyOn`
  establish arbitrarily small uniform error and uniform convergence.

## References

* [Berry, Childs, Cleve, Kothari, and Somma, 2015][BerryEtAl2015Taylor], *Simulating Hamiltonian
  Dynamics with a Truncated Taylor Series*.
-/

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial Filter
open scoped BigOperators Topology

/-- The coefficient `exponentialTaylorCoefficient t k` is the `k`th power of minus the imaginary
unit times `t`, divided by `k.factorial`. -/
noncomputable def exponentialTaylorCoefficient (t : ℝ) (k : ℕ) : ℂ :=
  (-Complex.I * (t : ℂ)) ^ k / (k.factorial : ℂ)

/-- The polynomial `exponentialTaylorPolynomial t n` sums the monomials with coefficients
`exponentialTaylorCoefficient t k` over indices `k < n`. -/
noncomputable def exponentialTaylorPolynomial (t : ℝ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n, monomial k (exponentialTaylorCoefficient t k)

/-- The zero-term truncation `exponentialTaylorPolynomial t 0` is the zero polynomial. -/
@[simp] theorem exponentialTaylorPolynomial_zero (t : ℝ) :
    exponentialTaylorPolynomial t 0 = 0 := by
  simp [exponentialTaylorPolynomial]

/-- The one-term truncation `exponentialTaylorPolynomial t 1` is the constant polynomial one. -/
@[simp] theorem exponentialTaylorPolynomial_one (t : ℝ) :
    exponentialTaylorPolynomial t 1 = 1 := by
  simp [exponentialTaylorPolynomial, exponentialTaylorCoefficient]

/-- Evaluation of `exponentialTaylorPolynomial t n` at `z` is the sum of
`exponentialTaylorCoefficient t k * z ^ k` over indices `k < n`. -/
theorem exponentialTaylorPolynomial_eval (t : ℝ) (n : ℕ) (z : ℂ) :
    (exponentialTaylorPolynomial t n).eval z =
      ∑ k ∈ Finset.range n, exponentialTaylorCoefficient t k * z ^ k := by
  simp [exponentialTaylorPolynomial, Polynomial.eval_finsetSum]

/-- Evaluation of `exponentialTaylorPolynomial t n` at `z` is the first `n` terms of the
exponential series for minus the imaginary unit times `t` times `z`. -/
theorem exponentialTaylorPolynomial_eval_sum (t : ℝ) (n : ℕ) (z : ℂ) :
    (exponentialTaylorPolynomial t n).eval z =
      ∑ k ∈ Finset.range n, (-Complex.I * (t : ℂ) * z) ^ k / (k.factorial : ℂ) := by
  rw [exponentialTaylorPolynomial_eval]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [exponentialTaylorCoefficient, mul_pow]
  ring

/-- The coefficient at index `k` of `exponentialTaylorPolynomial t n` is
`exponentialTaylorCoefficient t k` when `k < n`, and zero otherwise. -/
theorem exponentialTaylorPolynomial_coeff (t : ℝ) (n k : ℕ) :
    (exponentialTaylorPolynomial t n).coeff k =
      if k < n then exponentialTaylorCoefficient t k else 0 := by
  simp [exponentialTaylorPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]

/-- The natural degree of `exponentialTaylorPolynomial t n` is at most `n - 1`. -/
theorem exponentialTaylorPolynomial_natDegree_le (t : ℝ) (n : ℕ) :
    (exponentialTaylorPolynomial t n).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (by
    have hkn := Finset.mem_range.mp hk
    omega)

/-- For nonzero time `t`, every coefficient `exponentialTaylorCoefficient t k` is nonzero. -/
theorem exponentialTaylorCoefficient_ne_zero {t : ℝ} (ht : t ≠ 0) (k : ℕ) :
    exponentialTaylorCoefficient t k ≠ 0 := by
  apply div_ne_zero
  · exact pow_ne_zero k (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr ht))
  · exact_mod_cast Nat.factorial_ne_zero k

/-- For nonzero time `t` and positive truncation length `n`, the natural degree of
`exponentialTaylorPolynomial t n` is exactly `n - 1`. -/
theorem exponentialTaylorPolynomial_natDegree {t : ℝ} (ht : t ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    (exponentialTaylorPolynomial t n).natDegree = n - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (exponentialTaylorPolynomial_natDegree_le t n)
  rw [exponentialTaylorPolynomial_coeff, if_pos (by omega : n - 1 < n)]
  exact exponentialTaylorCoefficient_ne_zero ht _

/-- The scalar bound `exponentialTaylorError t n` is twice the `n`th power of the absolute value
of `t`, divided by `n.factorial`. -/
noncomputable def exponentialTaylorError (t : ℝ) (n : ℕ) : ℝ :=
  |t| ^ n / (n.factorial : ℝ) * 2

/-- The bound `exponentialTaylorError t n` is nonnegative for all real times and truncation
lengths. -/
theorem exponentialTaylorError_nonneg (t : ℝ) (n : ℕ) :
    0 ≤ exponentialTaylorError t n := by
  unfold exponentialTaylorError
  positivity

/-- For real `x` between minus one and one, the norm of minus the imaginary unit times `t` times
`x` is at most the absolute value of `t`. -/
theorem exponentialArgument_norm_le (t : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖-Complex.I * (t : ℂ) * (x : ℂ)‖ ≤ |t| := by
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left hxabs (abs_nonneg t)

/-- If `2 * |t| ≤ n + 1` and real `x` lies between minus one and one, the error of
`exponentialTaylorPolynomial t n` in approximating the phase exponential at `x` is at most
`exponentialTaylorError t n`. -/
theorem exponentialTaylorPolynomial_error_le (t : ℝ) (n : ℕ)
    (hn : 2 * |t| ≤ (n : ℝ) + 1) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(exponentialTaylorPolynomial t n).eval (x : ℂ) -
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))‖ ≤ exponentialTaylorError t n := by
  have hz := exponentialArgument_norm_le t hx
  have hratio : ‖-Complex.I * (t : ℂ) * (x : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n.succ : ℝ))).2
    simp only [Nat.cast_succ]
    nlinarith
  rw [exponentialTaylorPolynomial_eval_sum, norm_sub_rev, exponentialTaylorError]
  calc
    _ ≤ ‖-Complex.I * (t : ℂ) * (x : ℂ)‖ ^ n / (n.factorial : ℝ) * 2 :=
      Complex.exp_bound' hratio
    _ ≤ |t| ^ n / (n.factorial : ℝ) * 2 := by gcongr

/-- For each fixed real time `t`, the sequence `exponentialTaylorError t n` tends to zero as `n`
tends to infinity. -/
theorem tendsto_exponentialTaylorError (t : ℝ) :
    Tendsto (fun n : ℕ => exponentialTaylorError t n) atTop (𝓝 0) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop |t|).mul_const 2
  simpa [exponentialTaylorError] using h

/-- For each positive tolerance and fixed time `t`, all sufficiently large truncation lengths
satisfy the cutoff condition and make both `exponentialTaylorError` and the
phase-exponential approximation error strictly smaller than that tolerance throughout the
interval from minus one to one. -/
theorem exponentialTaylor_eventually_error_lt (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      2 * |t| ≤ (n : ℝ) + 1 ∧ exponentialTaylorError t n < ε ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖(exponentialTaylorPolynomial t n).eval (x : ℂ) -
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))‖ < ε := by
  have he : ∀ᶠ n : ℕ in atTop, exponentialTaylorError t n < ε :=
    (tendsto_order.mp (tendsto_exponentialTaylorError t)).2 ε hε
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp he
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * |t|)
  refine ⟨max K M, fun n hn => ?_⟩
  have hnK : K ≤ n := (le_max_left K M).trans hn
  have hnM : M ≤ n := (le_max_right K M).trans hn
  have hnMr : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
  have hcut : 2 * |t| ≤ (n : ℝ) + 1 := by linarith
  exact ⟨hcut, hK n hnK, fun x hx =>
    (exponentialTaylorPolynomial_error_le t n hcut hx).trans_lt (hK n hnK)⟩

/-- For each fixed time `t`, evaluations of `exponentialTaylorPolynomial t n` converge uniformly
on the interval from minus one to one to the exponential with argument minus the imaginary
unit times `t` times the signal. -/
theorem exponentialTaylorPolynomial_tendstoUniformlyOn (t : ℝ) :
    TendstoUniformlyOn
      (fun n (x : ℝ) => (exponentialTaylorPolynomial t n).eval (x : ℂ))
      (fun x : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)))
      atTop (Set.Icc (-1 : ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exponentialTaylor_eventually_error_lt t hε
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn x hx => ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact (hN n hn).2.2 x hx

end Qatlib.Concepts.QspSimulation.Achievability
