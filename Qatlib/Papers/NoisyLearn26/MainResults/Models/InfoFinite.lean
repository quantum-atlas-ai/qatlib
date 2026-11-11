/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite chi-squared divergence and product tests

Defines `chiSq` and independent product weights `prodDist` on finite spaces. The module proves
the product divergence identity and derives event-advantage and sample lower bounds from a bound
on the single-sample chi-squared expression. See [CotlerGongKannan2025] for the surrounding
analysis.

## Main statements

* `chiSq_prod`: For normalized weights and strictly positive `q`, the `N`-fold product
  chi-squared expression equals `(1 + chiSq p q) ^ N - 1`.
* `product_advantage_bound`: A single-sample bound `chiSq p q ≤ Δ` bounds the absolute
  difference of any product-event weights by `√((1 + Δ)^N - 1)`, under normalization and
  positivity of `q`.
* `product_samples_lower_bound`: A product event separating the normalized weights at thresholds
  `2 / 3` and `1 / 3` forces `log(10 / 9) / Δ ≤ N` under the stated positivity and chi-squared
  assumptions.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.InfoFinite

open Qatlib.Papers.NoisyLearn26.MainResults

open scoped BigOperators

variable {X : Type*} [Fintype X]

/-- The finite chi-squared expression `∑ x, (p x - q x)² / q x`. -/
def chiSq (p q : X → ℝ) : ℝ := ∑ x, (p x - q x) ^ 2 / q x

/-- The product weight on `N` samples, given by `∏ i, p (x i)`. -/
def prodDist {X : Type*} (p : X → ℝ) (N : ℕ) : (Fin N → X) → ℝ :=
  fun x => ∏ i, p (x i)

/-- The chi-squared expression is nonnegative when all reference weights are nonnegative. -/
theorem chiSq_nonneg (p q : X → ℝ) (hq : ∀ x, 0 ≤ q x) : 0 ≤ chiSq p q := by
  unfold chiSq
  exact Finset.sum_nonneg (fun x _ => div_nonneg (sq_nonneg _) (hq x))

/-- With strictly positive reference weights, the squared difference of event weights is bounded
by `chiSq p q` times the reference weight of the event. -/
theorem sq_event_diff_le (p q : X → ℝ) (hq : ∀ x, 0 < q x) (E : Finset X) :
    (∑ x ∈ E, (p x - q x)) ^ 2 ≤ chiSq p q * (∑ x ∈ E, q x) := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsumpos : 0 < ∑ x ∈ E, q x := Finset.sum_pos (fun x _ => hq x) hne
  have htitu :
      (∑ x ∈ E, (p x - q x)) ^ 2 / (∑ x ∈ E, q x) ≤
        ∑ x ∈ E, (p x - q x) ^ 2 / q x :=
    Finset.sq_sum_div_le_sum_sq_div E (fun x => p x - q x) (fun x _ => hq x)
  have hdiv : (∑ x ∈ E, (p x - q x)) ^ 2 ≤
      (∑ x ∈ E, (p x - q x) ^ 2 / q x) * (∑ x ∈ E, q x) := by
    have h := (div_le_iff₀ hsumpos).1 htitu
    linarith [h]
  have hmono : (∑ x ∈ E, (p x - q x) ^ 2 / q x) ≤ chiSq p q := by
    unfold chiSq
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) ?_
    intro x _ _
    exact div_nonneg (sq_nonneg _) (le_of_lt (hq x))
  exact hdiv.trans (mul_le_mul_of_nonneg_right hmono (le_of_lt hsumpos))

/-- For normalized weights and strictly positive `q`, the sum `∑ x, p x² / q x` equals `1 +
chiSq p q`. -/
theorem sum_sq_div (p q : X → ℝ) (hq : ∀ x, 0 < q x) (hp : ∑ x, p x = 1)
    (hq1 : ∑ x, q x = 1) :
    (∑ x, p x ^ 2 / q x) = 1 + chiSq p q := by
  have hpoint : ∀ x, p x ^ 2 / q x = (p x - q x) ^ 2 / q x + 2 * p x - q x := by
    intro x
    have hx : q x ≠ 0 := (hq x).ne'
    field_simp
    ring_nf
  calc (∑ x, p x ^ 2 / q x)
      = ∑ x, ((p x - q x) ^ 2 / q x + 2 * p x - q x) :=
        Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (∑ x, (p x - q x) ^ 2 / q x) + (∑ x, 2 * p x) - (∑ x, q x) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ x, (p x - q x) ^ 2 / q x) + 2 * (∑ x, p x) - (∑ x, q x) := by
        rw [← Finset.mul_sum]
    _ = chiSq p q + 2 * 1 - 1 := by rw [hp, hq1]; rfl
    _ = 1 + chiSq p q := by linarith

/-- If `q` sums to one, its `N`-fold product weights also sum to one. -/
theorem sum_prodDist (q : X → ℝ) (hq1 : ∑ x, q x = 1) (N : ℕ) :
    (∑ x : Fin N → X, prodDist q N x) = 1 := by
  unfold prodDist
  rw [(Fintype.sum_pow q N).symm, hq1, one_pow]

/-- For normalized weights and strictly positive `q`, the `N`-fold product chi-squared
expression equals `(1 + chiSq p q) ^ N - 1`. -/
theorem chiSq_prod (p q : X → ℝ) (hq : ∀ x, 0 < q x) (hp : ∑ x, p x = 1)
    (hq1 : ∑ x, q x = 1) (N : ℕ) :
    chiSq (prodDist p N) (prodDist q N) = (1 + chiSq p q) ^ N - 1 := by
  have hqne : ∀ x, q x ≠ 0 := fun x => (hq x).ne'
  have hqprod : ∀ x : Fin N → X, prodDist q N x ≠ 0 := by
    intro x
    unfold prodDist
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hqne (x i))
  have hpoint : ∀ x : Fin N → X,
      (prodDist p N x - prodDist q N x) ^ 2 / prodDist q N x =
        (∏ i, p (x i) ^ 2 / q (x i)) - 2 * prodDist p N x + prodDist q N x := by
    intro x
    have hsplit : (∏ i, p (x i) ^ 2 / q (x i)) = (prodDist p N x) ^ 2 / prodDist q N x := by
      unfold prodDist
      rw [Finset.prod_div_distrib, Finset.prod_pow]
    rw [hsplit]
    have hqx : prodDist q N x ≠ 0 := hqprod x
    field_simp
    ring
  have hsum : (∑ x : Fin N → X, ((∏ i, p (x i) ^ 2 / q (x i)) - 2 * prodDist p N x +
        prodDist q N x)) =
      (∑ x : Fin N → X, ∏ i, p (x i) ^ 2 / q (x i)) -
        2 * (∑ x : Fin N → X, prodDist p N x) + (∑ x : Fin N → X, prodDist q N x) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : (∑ x : Fin N → X, ∏ i, p (x i) ^ 2 / q (x i)) =
      (∑ x, p x ^ 2 / q x) ^ N := by
    rw [(Fintype.sum_pow (fun x => p x ^ 2 / q x) N).symm]
  have h2 : (∑ x : Fin N → X, ∏ i, p (x i)) = (∑ x, p x) ^ N := by
    rw [(Fintype.sum_pow (fun x => p x) N).symm]
  have h3 : (∑ x : Fin N → X, ∏ i, q (x i)) = (∑ x, q x) ^ N := by
    rw [(Fintype.sum_pow (fun x => q x) N).symm]
  change (∑ x : Fin N → X, (prodDist p N x - prodDist q N x) ^ 2 / prodDist q N x) =
    (1 + chiSq p q) ^ N - 1
  have h2' : (∑ x : Fin N → X, prodDist p N x) = 1 := by
    unfold prodDist
    rw [(Fintype.sum_pow (fun x => p x) N).symm, hp, one_pow]
  have h3' : (∑ x : Fin N → X, prodDist q N x) = 1 := sum_prodDist q hq1 N
  rw [Finset.sum_congr rfl (fun x _ => hpoint x), hsum, h1, h2', h3',
    sum_sq_div p q hq hp hq1]
  ring

/-- A single-sample bound `chiSq p q ≤ Δ` bounds the absolute difference of any product-event
weights by `√((1 + Δ)^N - 1)`, under normalization and positivity of `q`
[CotlerGongKannan2025]. -/
theorem product_advantage_bound (p q : X → ℝ) (hq : ∀ x, 0 < q x)
    (hp : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (Δ : ℝ)
    (hchi : chiSq p q ≤ Δ) (N : ℕ) (E : Finset (Fin N → X)) :
    |∑ x ∈ E, (prodDist p N x - prodDist q N x)| ≤
      Real.sqrt ((1 + Δ) ^ N - 1) := by
  have hDelta : 0 ≤ Δ := le_trans (chiSq_nonneg p q (fun x => le_of_lt (hq x))) hchi
  have hprodpos : ∀ x, 0 < prodDist q N x := by
    intro x
    unfold prodDist
    exact Finset.prod_pos (fun i _ => hq (x i))
  have hsq := sq_event_diff_le (prodDist p N) (prodDist q N) hprodpos E
  have hchiN : chiSq (prodDist p N) (prodDist q N) = (1 + chiSq p q) ^ N - 1 :=
    chiSq_prod p q hq hp hq1 N
  have hle : chiSq (prodDist p N) (prodDist q N) ≤ (1 + Δ) ^ N - 1 := by
    rw [hchiN]
    have hbase : 1 + chiSq p q ≤ 1 + Δ := by linarith
    have hbasepos : 0 ≤ 1 + chiSq p q := by
      have := chiSq_nonneg p q (fun x => le_of_lt (hq x)); linarith
    have hpow : (1 + chiSq p q) ^ N ≤ (1 + Δ) ^ N :=
      pow_le_pow_left₀ hbasepos hbase N
    have hb : (1 : ℝ) ≤ 1 + chiSq p q := by
      have := chiSq_nonneg p q (fun x => le_of_lt (hq x)); linarith
    have h1 : (1 : ℝ) ≤ (1 + chiSq p q) ^ N := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb N
    linarith
  have htot : (∑ x, prodDist q N x) = 1 := sum_prodDist q hq1 N
  have hqsub : (∑ x ∈ E, prodDist q N x) ≤ 1 := by
    rw [← htot]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      (fun x _ _ => le_of_lt (hprodpos x))
  have hnonne : 0 ≤ (1 + Δ) ^ N - 1 := by
    have hb : (1 : ℝ) ≤ 1 + Δ := by linarith [hDelta]
    have h1 : (1 : ℝ) ≤ (1 + Δ) ^ N := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb N
    linarith
  have hsqle : (∑ x ∈ E, (prodDist p N x - prodDist q N x)) ^ 2 ≤ (1 + Δ) ^ N - 1 := by
    refine hsq.trans ?_
    calc chiSq (prodDist p N) (prodDist q N) * (∑ x ∈ E, prodDist q N x)
        ≤ ((1 + Δ) ^ N - 1) * (∑ x ∈ E, prodDist q N x) :=
          mul_le_mul_of_nonneg_right hle
            (Finset.sum_nonneg (fun x _ => le_of_lt (hprodpos x)))
      _ ≤ ((1 + Δ) ^ N - 1) * 1 := mul_le_mul_of_nonneg_left hqsub hnonne
      _ = (1 + Δ) ^ N - 1 := by ring
  calc |∑ x ∈ E, (prodDist p N x - prodDist q N x)|
      = Real.sqrt ((∑ x ∈ E, (prodDist p N x - prodDist q N x)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((1 + Δ) ^ N - 1) := Real.sqrt_le_sqrt hsqle

/-- A product event with acceptance weights at least `2 / 3` for `p` and at most `1 / 3` for `q`
forces `log(10 / 9) ≤ N * log(1 + Δ)` under the stated chi-squared bound
[CotlerGongKannan2025]. -/
theorem product_test_lower_bound (p q : X → ℝ) (hq : ∀ x, 0 < q x)
    (hp : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (Δ : ℝ) (hchi : chiSq p q ≤ Δ)
    (N : ℕ) (E : Finset (Fin N → X))
    (hyes : (2 : ℝ) / 3 ≤ ∑ x ∈ E, prodDist p N x)
    (hno : (∑ x ∈ E, prodDist q N x) ≤ (1 : ℝ) / 3) :
    Real.log (10 / 9) ≤ (N : ℝ) * Real.log (1 + Δ) := by
  have hDelta : 0 ≤ Δ := le_trans (chiSq_nonneg p q (fun x => le_of_lt (hq x))) hchi
  have hbound := product_advantage_bound p q hq hp hq1 Δ hchi N E
  have hdiff : (1 : ℝ) / 3 ≤ ∑ x ∈ E, (prodDist p N x - prodDist q N x) := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hdiff_abs : (1 : ℝ) / 3 ≤ |∑ x ∈ E, (prodDist p N x - prodDist q N x)| := by
    rw [abs_of_nonneg (by linarith)]
    exact hdiff
  have hsqrt : (1 : ℝ) / 3 ≤ Real.sqrt ((1 + Δ) ^ N - 1) := hdiff_abs.trans hbound
  have harg : (0 : ℝ) ≤ (1 + Δ) ^ N - 1 := by
    have hb : (1 : ℝ) ≤ 1 + Δ := by linarith [hDelta]
    have h1 : (1 : ℝ) ≤ (1 + Δ) ^ N := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb N
    linarith
  have hsq : (1 : ℝ) / 9 ≤ (1 + Δ) ^ N - 1 := by
    have h := Real.sq_sqrt harg
    nlinarith [hsqrt, h]
  have hbase : 0 < 1 + Δ := by
    have := chiSq_nonneg p q (fun x => le_of_lt (hq x)); linarith
  have hpow : (10 : ℝ) / 9 ≤ (1 + Δ) ^ N := by linarith
  have hlog : Real.log (10 / 9) ≤ Real.log ((1 + Δ) ^ N) :=
    Real.log_le_log (by norm_num) hpow
  rw [Real.log_pow] at hlog
  exact hlog

/-- A product event separating the normalized weights at thresholds `2 / 3` and `1 / 3` forces
`log(10 / 9) / Δ ≤ N` under the stated positivity and chi-squared assumptions
[CotlerGongKannan2025]. -/
theorem product_samples_lower_bound (p q : X → ℝ) (hq : ∀ x, 0 < q x)
    (hp : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (Δ : ℝ) (hchi : chiSq p q ≤ Δ)
    (N : ℕ) (E : Finset (Fin N → X))
    (hyes : (2 : ℝ) / 3 ≤ ∑ x ∈ E, prodDist p N x)
    (hno : (∑ x ∈ E, prodDist q N x) ≤ (1 : ℝ) / 3) :
    Real.log (10 / 9) / Δ ≤ (N : ℝ) := by
  have hDelta : 0 ≤ Δ := le_trans (chiSq_nonneg p q (fun x => le_of_lt (hq x))) hchi
  rcases lt_or_eq_of_le hDelta with hpos | h0
  · have hbase : 0 < 1 + Δ := by linarith
    have hlogineq := product_test_lower_bound p q hq hp hq1 Δ hchi N E hyes hno
    have hlogbound : Real.log (1 + Δ) ≤ Δ := by
      have := Real.log_le_sub_one_of_pos hbase
      linarith
    rw [div_le_iff₀ hpos]
    exact hlogineq.trans (mul_le_mul_of_nonneg_left hlogbound (Nat.cast_nonneg N))
  · rw [← h0]
    simp only [div_zero]
    exact Nat.cast_nonneg N

end Qatlib.Papers.NoisyLearn26.MainResults.InfoFinite
