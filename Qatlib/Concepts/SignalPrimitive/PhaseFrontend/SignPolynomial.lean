/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Iterated Cubic Sign Polynomials

`signPolynomial` starts at `X` and iterates `p` to `(3*p - p^3)/2`, producing bounded odd
polynomials of degree `3^k`. These polynomials supply an explicit sign-approximation family for
singular value transformation consumers in the setting of [GilyenSuLowWiebe2019].

The residual `1 - p_k(x)^2` contracts at least quadratically on `[-1, 1]`. On the region `delta
<= |x| <= 1`, the sign error is bounded by `signPolynomialError delta k = (1 - delta^2)^(2^k)`,
which tends to zero for `0 < delta <= 1`; the module concludes uniform convergence on that
region.

## Main statements

- `signPolynomial_natDegree` gives the exact degree.
- `signPolynomial_abs_le_one` and `signPolynomial_sign` give boundedness and sign preservation.
- `signPolynomial_error_le` gives the gap-dependent approximation bound.
- `signPolynomial_tendstoUniformlyOn` gives uniform convergence away from zero.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019], *Quantum singular value transformation and
  beyond: exponential improvements for quantum matrix arithmetics*.
-/

namespace Qatlib.Concepts.SignalPrimitive.PhaseFrontend

open Polynomial Filter
open scoped Topology

/-- The real polynomial sequence starting at `X` and iterating the cubic map `p ↦ (3*p -
p^3)/2`. -/
noncomputable def signPolynomial : ℕ → Polynomial ℝ
  | 0 => X
  | k + 1 => C (1 / 2) * (C 3 * signPolynomial k - signPolynomial k ^ 3)

/-- The initial sign polynomial is `X`. -/
@[simp] theorem signPolynomial_zero : signPolynomial 0 = X := rfl

/-- Evaluation of the next sign polynomial applies the scalar cubic map `u ↦ (3*u - u^3)/2` to
the current value. -/
theorem signPolynomial_eval_succ (k : ℕ) (x : ℝ) :
    (signPolynomial (k + 1)).eval x =
      (3 * (signPolynomial k).eval x - ((signPolynomial k).eval x) ^ 3) / 2 := by
  simp only [signPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_pow]
  ring

/-- Every sign polynomial vanishes at zero. -/
@[simp] theorem signPolynomial_eval_zero (k : ℕ) : (signPolynomial k).eval 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [signPolynomial_eval_succ, ih]; norm_num

/-- Every sign polynomial takes the value one at one. -/
@[simp] theorem signPolynomial_eval_one (k : ℕ) : (signPolynomial k).eval 1 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [signPolynomial_eval_succ, ih]; norm_num

/-- Every sign polynomial is odd as a real-valued function. -/
theorem signPolynomial_eval_neg (k : ℕ) (x : ℝ) :
    (signPolynomial k).eval (-x) = -(signPolynomial k).eval x := by
  induction k with
  | zero => simp
  | succ k ih => rw [signPolynomial_eval_succ, signPolynomial_eval_succ, ih]; ring

/-- Composition with `-X` negates each sign polynomial. -/
theorem signPolynomial_comp_neg_X (k : ℕ) :
    (signPolynomial k).comp (-X) = -signPolynomial k := by
  apply Polynomial.funext
  intro x
  simpa using signPolynomial_eval_neg k x

/-- The exact natural degree of the `k`th sign polynomial is `3^k`. -/
theorem signPolynomial_natDegree (k : ℕ) : (signPolynomial k).natDegree = 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [signPolynomial, Polynomial.natDegree_C_mul (by norm_num : (1 / 2 : ℝ) ≠ 0),
      Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · rw [Polynomial.natDegree_pow, ih, pow_succ]
      omega
    · rw [Polynomial.natDegree_C_mul (by norm_num : (3 : ℝ) ≠ 0),
        Polynomial.natDegree_pow, ih]
      have hp : 0 < (3 : ℕ) ^ k := pow_pos (by decide) k
      omega

/-- Each sign polynomial maps `[0, 1]` into `[0, 1]`. -/
theorem signPolynomial_eval_mem_Icc_zero_one (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : (signPolynomial k).eval x ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [signPolynomial_eval_succ]
    have hfactor : 0 ≤ 3 - ((signPolynomial k).eval x) ^ 2 := by nlinarith [ih.1, ih.2]
    have hprod := mul_nonneg ih.1 hfactor
    have htop := mul_nonneg (sq_nonneg (1 - (signPolynomial k).eval x))
      (by linarith [ih.1] : 0 ≤ 2 + (signPolynomial k).eval x)
    constructor <;> nlinarith

/-- Each sign polynomial has absolute value at most one on `[-1, 1]`. -/
theorem signPolynomial_abs_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(signPolynomial k).eval x| ≤ 1 := by
  by_cases hx0 : 0 ≤ x
  · have h := signPolynomial_eval_mem_Icc_zero_one k ⟨hx0, hx.2⟩
    rw [abs_of_nonneg h.1]
    exact h.2
  · have h := signPolynomial_eval_mem_Icc_zero_one k (x := -x)
      ⟨by linarith, by linarith [hx.1]⟩
    rw [signPolynomial_eval_neg] at h
    exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

/-- For an input in `[0, 1]`, every sign polynomial value is at least the input. -/
theorem le_signPolynomial_eval (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ≤ (signPolynomial k).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy := signPolynomial_eval_mem_Icc_zero_one k hx
    have hprod := mul_nonneg hy.1
      (by nlinarith [hy.1, hy.2] : 0 ≤ 1 - ((signPolynomial k).eval x) ^ 2)
    rw [signPolynomial_eval_succ]
    nlinarith

/-- Every sign polynomial is strictly positive on `(0, 1]`. -/
theorem signPolynomial_eval_pos (k : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 < (signPolynomial k).eval x :=
  hx0.trans_le (le_signPolynomial_eval k ⟨hx0.le, hx1⟩)

/-- On `[-1, 1]`, each sign polynomial preserves the real sign of its input. -/
theorem signPolynomial_sign (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sign ((signPolynomial k).eval x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hp := signPolynomial_eval_pos k (x := -x) (by linarith) (by linarith [hx.1])
    rw [signPolynomial_eval_neg] at hp
    rw [Real.sign_of_neg (by linarith : (signPolynomial k).eval x < 0), Real.sign_of_neg hneg]
  · simp
  · rw [Real.sign_of_pos (signPolynomial_eval_pos k hpos hx.2), Real.sign_of_pos hpos]

/-- The residual `1 - p_(k+1)(x)^2` equals `(1 - p_k(x)^2)^2 * (4 - p_k(x)^2)/4`. -/
theorem signPolynomial_residual_succ (k : ℕ) (x : ℝ) :
    1 - ((signPolynomial (k + 1)).eval x) ^ 2 =
      (1 - ((signPolynomial k).eval x) ^ 2) ^ 2 *
        (4 - ((signPolynomial k).eval x) ^ 2) / 4 := by
  rw [signPolynomial_eval_succ]
  ring

/-- For every real input, the residual `1 - p_(k+1)(x)^2` is at most `(1 - p_k(x)^2)^2`. -/
theorem signPolynomial_residual_succ_le (k : ℕ) (x : ℝ) :
    1 - ((signPolynomial (k + 1)).eval x) ^ 2 ≤
      (1 - ((signPolynomial k).eval x) ^ 2) ^ 2 := by
  rw [signPolynomial_residual_succ]
  have h := mul_nonneg (sq_nonneg (1 - ((signPolynomial k).eval x) ^ 2))
    (sq_nonneg ((signPolynomial k).eval x))
  nlinarith

/-- For `x` in `[-1, 1]`, the residual `1 - p_k(x)^2` is at most `(1 - x^2)^(2^k)`. -/
theorem signPolynomial_residual_le (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    1 - ((signPolynomial k).eval x) ^ 2 ≤ (1 - x ^ 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ha := abs_le.mp (signPolynomial_abs_le_one k hx)
    have hr : 0 ≤ 1 - ((signPolynomial k).eval x) ^ 2 := by nlinarith [ha.1, ha.2]
    calc
      1 - ((signPolynomial (k + 1)).eval x) ^ 2 ≤
          (1 - ((signPolynomial k).eval x) ^ 2) ^ 2 := signPolynomial_residual_succ_le k x
      _ ≤ ((1 - x ^ 2) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ hr ih 2
      _ = (1 - x ^ 2) ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]

/-- For `0 < x ≤ 1`, the error from the real sign function is at most the residual `1 -
p_k(x)^2`. -/
private theorem signPolynomial_positive_error_le_residual (k : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |Real.sign x - (signPolynomial k).eval x| ≤ 1 - ((signPolynomial k).eval x) ^ 2 := by
  have hy := signPolynomial_eval_mem_Icc_zero_one k ⟨hx0.le, hx1⟩
  rw [Real.sign_of_pos hx0, abs_of_nonneg (by linarith [hy.2])]
  have hprod := mul_nonneg hy.1 (by linarith [hy.2] : 0 ≤ 1 - (signPolynomial k).eval x)
  nlinarith

/-- On `[-1, 1]`, the error from the real sign function is at most the residual `1 - p_k(x)^2`. -/
theorem signPolynomial_error_le_residual (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |Real.sign x - (signPolynomial k).eval x| ≤ 1 - ((signPolynomial k).eval x) ^ 2 := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have h := signPolynomial_positive_error_le_residual k (x := -x)
      (by linarith) (by linarith [hx.1])
    rw [Real.sign_neg, signPolynomial_eval_neg, neg_sq] at h
    have he : -Real.sign x - -(signPolynomial k).eval x =
        -(Real.sign x - (signPolynomial k).eval x) := by ring
    rw [he, abs_neg] at h
    exact h
  · simp
  · exact signPolynomial_positive_error_le_residual k hpos hx.2

/-- The explicit gap-dependent error expression `(1 - δ^2)^(2^k)`. -/
noncomputable def signPolynomialError (δ : ℝ) (k : ℕ) : ℝ := (1 - δ ^ 2) ^ (2 ^ k)

/-- For a positive gap `δ` and `δ ≤ |x| ≤ 1`, the sign approximation error is at most
`signPolynomialError δ k`. -/
theorem signPolynomial_error_le (k : ℕ) {δ x : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ |x|) (hx : |x| ≤ 1) :
    |Real.sign x - (signPolynomial k).eval x| ≤ signPolynomialError δ k := by
  have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hq : 0 ≤ 1 - x ^ 2 := by nlinarith [hxI.1, hxI.2]
  have hs : δ ^ 2 ≤ x ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hδ.le hgap 2
  exact (signPolynomial_error_le_residual k hxI).trans
    ((signPolynomial_residual_le k hxI).trans
      (pow_le_pow_left₀ hq (by linarith : 1 - x ^ 2 ≤ 1 - δ ^ 2) (2 ^ k)))

/-- For `0 < δ ≤ 1`, the explicit sign polynomial error tends to zero as the iteration index
tends to infinity. -/
theorem tendsto_signPolynomialError {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun k : ℕ => signPolynomialError δ k) atTop (𝓝 0) := by
  have hq0 : 0 ≤ 1 - δ ^ 2 := by nlinarith
  have hq1 : 1 - δ ^ 2 < 1 := by nlinarith [sq_pos_of_pos hδ]
  have hp : Tendsto (fun k : ℕ => (2 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hp

/-- For `0 < δ ≤ 1` and positive tolerance, all sufficiently late sign polynomials approximate
the sign function within that tolerance uniformly for `δ ≤ |x| ≤ 1`. -/
theorem signPolynomial_eventually_error_lt {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 →
      |Real.sign x - (signPolynomial k).eval x| < ε := by
  have he : ∀ᶠ k : ℕ in atTop, signPolynomialError δ k < ε :=
    (tendsto_order.mp (tendsto_signPolynomialError hδ hδ1)).2 ε hε
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp he
  exact ⟨K, fun k hk x hgap hx => (signPolynomial_error_le k hδ hgap hx).trans_lt (hK k hk)⟩

/-- For `0 < δ ≤ 1`, the evaluated sign polynomials converge uniformly to `Real.sign` on the set
`δ ≤ |x| ≤ 1`. -/
theorem signPolynomial_tendstoUniformlyOn {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    TendstoUniformlyOn (fun k (x : ℝ) => (signPolynomial k).eval x) Real.sign atTop
      {x : ℝ | δ ≤ |x| ∧ |x| ≤ 1} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := signPolynomial_eventually_error_lt hδ hδ1 hε
  apply Filter.eventually_atTop.mpr
  refine ⟨K, fun k hk x hx => ?_⟩
  simpa only [Real.dist_eq] using hK k hk x hx.1 hx.2

end Qatlib.Concepts.SignalPrimitive.PhaseFrontend
