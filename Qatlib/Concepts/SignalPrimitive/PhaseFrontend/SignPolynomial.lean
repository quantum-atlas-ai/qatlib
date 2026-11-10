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

namespace Qatlib.Concepts.SignalPrimitive.PhaseFrontend

open Polynomial Filter
open scoped Topology

noncomputable def signPolynomial : ℕ → Polynomial ℝ
  | 0 => X
  | k + 1 => C (1 / 2) * (C 3 * signPolynomial k - signPolynomial k ^ 3)

@[simp] theorem signPolynomial_zero : signPolynomial 0 = X := rfl

theorem signPolynomial_eval_succ (k : ℕ) (x : ℝ) :
    (signPolynomial (k + 1)).eval x =
      (3 * (signPolynomial k).eval x - ((signPolynomial k).eval x) ^ 3) / 2 := by
  simp only [signPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_pow]
  ring

@[simp] theorem signPolynomial_eval_zero (k : ℕ) : (signPolynomial k).eval 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [signPolynomial_eval_succ, ih]; norm_num

@[simp] theorem signPolynomial_eval_one (k : ℕ) : (signPolynomial k).eval 1 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [signPolynomial_eval_succ, ih]; norm_num

theorem signPolynomial_eval_neg (k : ℕ) (x : ℝ) :
    (signPolynomial k).eval (-x) = -(signPolynomial k).eval x := by
  induction k with
  | zero => simp
  | succ k ih => rw [signPolynomial_eval_succ, signPolynomial_eval_succ, ih]; ring

theorem signPolynomial_comp_neg_X (k : ℕ) :
    (signPolynomial k).comp (-X) = -signPolynomial k := by
  apply Polynomial.funext
  intro x
  simpa using signPolynomial_eval_neg k x

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

theorem signPolynomial_eval_pos (k : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 < (signPolynomial k).eval x :=
  hx0.trans_le (le_signPolynomial_eval k ⟨hx0.le, hx1⟩)

theorem signPolynomial_sign (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sign ((signPolynomial k).eval x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hp := signPolynomial_eval_pos k (x := -x) (by linarith) (by linarith [hx.1])
    rw [signPolynomial_eval_neg] at hp
    rw [Real.sign_of_neg (by linarith : (signPolynomial k).eval x < 0), Real.sign_of_neg hneg]
  · simp
  · rw [Real.sign_of_pos (signPolynomial_eval_pos k hpos hx.2), Real.sign_of_pos hpos]

theorem signPolynomial_residual_succ (k : ℕ) (x : ℝ) :
    1 - ((signPolynomial (k + 1)).eval x) ^ 2 =
      (1 - ((signPolynomial k).eval x) ^ 2) ^ 2 *
        (4 - ((signPolynomial k).eval x) ^ 2) / 4 := by
  rw [signPolynomial_eval_succ]
  ring

theorem signPolynomial_residual_succ_le (k : ℕ) (x : ℝ) :
    1 - ((signPolynomial (k + 1)).eval x) ^ 2 ≤
      (1 - ((signPolynomial k).eval x) ^ 2) ^ 2 := by
  rw [signPolynomial_residual_succ]
  have h := mul_nonneg (sq_nonneg (1 - ((signPolynomial k).eval x) ^ 2))
    (sq_nonneg ((signPolynomial k).eval x))
  nlinarith

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

private theorem signPolynomial_positive_error_le_residual (k : ℕ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |Real.sign x - (signPolynomial k).eval x| ≤ 1 - ((signPolynomial k).eval x) ^ 2 := by
  have hy := signPolynomial_eval_mem_Icc_zero_one k ⟨hx0.le, hx1⟩
  rw [Real.sign_of_pos hx0, abs_of_nonneg (by linarith [hy.2])]
  have hprod := mul_nonneg hy.1 (by linarith [hy.2] : 0 ≤ 1 - (signPolynomial k).eval x)
  nlinarith

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

noncomputable def signPolynomialError (δ : ℝ) (k : ℕ) : ℝ := (1 - δ ^ 2) ^ (2 ^ k)

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

theorem tendsto_signPolynomialError {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun k : ℕ => signPolynomialError δ k) atTop (𝓝 0) := by
  have hq0 : 0 ≤ 1 - δ ^ 2 := by nlinarith
  have hq1 : 1 - δ ^ 2 < 1 := by nlinarith [sq_pos_of_pos hδ]
  have hp : Tendsto (fun k : ℕ => (2 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hp

theorem signPolynomial_eventually_error_lt {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ x : ℝ, δ ≤ |x| → |x| ≤ 1 →
      |Real.sign x - (signPolynomial k).eval x| < ε := by
  have he : ∀ᶠ k : ℕ in atTop, signPolynomialError δ k < ε :=
    (tendsto_order.mp (tendsto_signPolynomialError hδ hδ1)).2 ε hε
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp he
  exact ⟨K, fun k hk x hgap hx => (signPolynomial_error_le k hδ hgap hx).trans_lt (hK k hk)⟩

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
