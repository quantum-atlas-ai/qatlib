/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Scalar sums for noisy shadow lower bounds

Develops binomial and even-binomial identities controlling noise-weighted sums with coefficients
in `[0, 1]`. The module also rewrites single-block factors as powers of two and proves the
finite Euclidean sum estimate `delta_c_bound`. See [CotlerGongKannan2025] for the surrounding
analysis.

## Main statements

* `four_lemma`: For noise in `[0, 1]` and `0 ≤ K a ≤ 1`, the stated noise-weighted binomial sum
  is at most `fLambda lam ^ n`.
* `five_lemma`: For noise in `[0, 1]` and coefficients `K` in `[0, 1]`, the stated even-indexed
  sum is at most `((3^n + 1) / 2) * (1 - lam)^(2n)`.
* `delta_c_bound`: For a finite nonnegative array, the squared Euclidean norm of the sum of its
  rows is at most the square of the sum of their Euclidean norms.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.ShadowNoise

open Qatlib.Papers.NoisyLearn26.MainResults

open scoped BigOperators

/-- The finite chi-squared expression `∑ x, (p x - q x)² / q x`. -/
def chiSq {X : Type*} [Fintype X] (p q : X → ℝ) : ℝ := ∑ x, (p x - q x) ^ 2 / q x

/-- The noise polynomial `fLambda lam` is positive for `lam` in `[0, 1]`. -/
theorem fLambda_pos' {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 < fLambda lam := by
  unfold fLambda
  nlinarith [sq_nonneg (lam - 1)]

/-- The binomial sum `∑ a ≤ n, choose n a * x^a * y^(n-a)` equals `(x + y)^n`. -/
theorem binomial_expansion (x y : ℝ) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * x ^ a * y ^ (n - a)) = (x + y) ^ n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The binomial sum with factors `lam * (2 - lam) / 2` and `(1 - lam)²` equals `fLambda lam ^
n` [CotlerGongKannan2025]. -/
theorem swap_expansion (lam : ℝ) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * (lam * (2 - lam) / 2) ^ a * ((1 - lam) ^ 2) ^ (n - a)) =
      fLambda lam ^ n := by
  rw [binomial_expansion]
  have h : lam * (2 - lam) / 2 + (1 - lam) ^ 2 = fLambda lam := by
    unfold fLambda
    ring
  rw [h]

/-- For noise in `[0, 1]` and `0 ≤ K a ≤ 1`, the stated noise-weighted binomial sum is at most
`fLambda lam ^ n` [CotlerGongKannan2025]. -/
theorem four_lemma {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ℕ → ℝ) (hK0 : ∀ a, 0 ≤ K a) (hK1 : ∀ a, K a ≤ 1) :
    (∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * (lam * (2 - lam) / 2) ^ a * ((1 - lam) ^ 2) ^ (n - a) * K a) ≤
      fLambda lam ^ n := by
  have hx : 0 ≤ lam * (2 - lam) / 2 := by nlinarith
  have hy : 0 ≤ (1 - lam) ^ 2 := sq_nonneg _
  have hnonneg : ∀ a ∈ Finset.range (n + 1),
      0 ≤ (n.choose a : ℝ) * (lam * (2 - lam) / 2) ^ a * ((1 - lam) ^ 2) ^ (n - a) :=
    fun a _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx a))
      (pow_nonneg hy (n - a))
  calc (∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * (lam * (2 - lam) / 2) ^ a * ((1 - lam) ^ 2) ^ (n - a) * K a)
      ≤ ∑ a ∈ Finset.range (n + 1),
        (n.choose a : ℝ) * (lam * (2 - lam) / 2) ^ a * ((1 - lam) ^ 2) ^ (n - a) := by
        apply Finset.sum_le_sum
        intro a ha
        have hc := hnonneg a ha
        have hk := hK1 a
        have := mul_le_mul_of_nonneg_left hk hc
        simpa using this
    _ = fLambda lam ^ n := swap_expansion lam n

/-- The even-indexed binomial sum is `((x + y)^n + (y - x)^n) / 2` [CotlerGongKannan2025]. -/
theorem sum_even_choose (x y : ℝ) (n : ℕ) :
    (∑ a ∈ (Finset.range (n + 1)).filter (fun a => Even a),
        (n.choose a : ℝ) * x ^ a * y ^ (n - a)) =
      ((x + y) ^ n + (y - x) ^ n) / 2 := by
  have hpar : ∀ a : ℕ, (if Even a then (1 : ℝ) else 0) = (1 + (-1 : ℝ) ^ a) / 2 := by
    intro a
    rcases Nat.even_or_odd a with h | h
    · rw [if_pos h, h.neg_one_pow]; norm_num
    · rw [if_neg (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]; norm_num
  have hxy :
      (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * x ^ a * y ^ (n - a)) = (x + y) ^ n :=
    binomial_expansion x y n
  have hyx :
      (∑ a ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ a * ((n.choose a : ℝ) * x ^ a * y ^ (n - a))) = (y - x) ^ n := by
    rw [show y - x = -x + y by ring, add_pow]
    apply Finset.sum_congr rfl
    intro a _
    rw [neg_pow]
    ring
  rw [Finset.sum_filter]
  calc (∑ a ∈ Finset.range (n + 1),
        if Even a then (n.choose a : ℝ) * x ^ a * y ^ (n - a) else 0)
      = ∑ a ∈ Finset.range (n + 1),
          (n.choose a : ℝ) * x ^ a * y ^ (n - a) * ((1 + (-1 : ℝ) ^ a) / 2) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : Even a
        · rw [if_pos h, ← hpar a, if_pos h, mul_one]
        · rw [if_neg h, ← hpar a, if_neg h, mul_zero]
    _ = ∑ a ∈ Finset.range (n + 1),
          ((n.choose a : ℝ) * x ^ a * y ^ (n - a) / 2 +
            (-1 : ℝ) ^ a * ((n.choose a : ℝ) * x ^ a * y ^ (n - a)) / 2) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * x ^ a * y ^ (n - a)) / 2 +
        (∑ a ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ a * ((n.choose a : ℝ) * x ^ a * y ^ (n - a))) / 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    _ = ((x + y) ^ n + (y - x) ^ n) / 2 := by
        rw [hxy, hyx]
        ring

/-- For noise in `[0, 1]` and coefficients `K` in `[0, 1]`, the stated even-indexed sum is at
most `((3^n + 1) / 2) * (1 - lam)^(2n)` [CotlerGongKannan2025]. -/
theorem five_lemma {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ℕ → ℝ) (hK0 : ∀ a, 0 ≤ K a) (hK1 : ∀ a, K a ≤ 1) :
    (∑ a ∈ (Finset.range (n + 1)).filter (fun a => Even a),
        (n.choose a : ℝ) * ((1 - lam) ^ 2) ^ a * (2 * (1 - lam) ^ 2) ^ (n - a) * K a) ≤
      ((3 : ℝ) ^ n + 1) / 2 * (1 - lam) ^ (2 * n) := by
  have hx : (0 : ℝ) ≤ (1 - lam) ^ 2 := sq_nonneg _
  have hy : (0 : ℝ) ≤ 2 * (1 - lam) ^ 2 := mul_nonneg (by norm_num) hx
  have hnonneg : ∀ a ∈ (Finset.range (n + 1)).filter (fun a => Even a),
      0 ≤ (n.choose a : ℝ) * ((1 - lam) ^ 2) ^ a * (2 * (1 - lam) ^ 2) ^ (n - a) :=
    fun a _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx a))
      (pow_nonneg hy (n - a))
  calc (∑ a ∈ (Finset.range (n + 1)).filter (fun a => Even a),
        (n.choose a : ℝ) * ((1 - lam) ^ 2) ^ a * (2 * (1 - lam) ^ 2) ^ (n - a) * K a)
      ≤ ∑ a ∈ (Finset.range (n + 1)).filter (fun a => Even a),
        (n.choose a : ℝ) * ((1 - lam) ^ 2) ^ a * (2 * (1 - lam) ^ 2) ^ (n - a) := by
        apply Finset.sum_le_sum
        intro a ha
        have hc := hnonneg a ha
        have hk := hK1 a
        have := mul_le_mul_of_nonneg_left hk hc
        simpa using this
    _ = (((1 - lam) ^ 2 + 2 * (1 - lam) ^ 2) ^ n + (2 * (1 - lam) ^ 2 - (1 - lam) ^ 2) ^ n) / 2 :=
        sum_even_choose ((1 - lam) ^ 2) (2 * (1 - lam) ^ 2) n
    _ = ((3 : ℝ) ^ n + 1) / 2 * (1 - lam) ^ (2 * n) := by
        have hsum : (1 - lam) ^ 2 + 2 * (1 - lam) ^ 2 = 3 * (1 - lam) ^ 2 := by ring
        have hdiff : 2 * (1 - lam) ^ 2 - (1 - lam) ^ 2 = (1 - lam) ^ 2 := by ring
        rw [hsum, hdiff, mul_pow, ← pow_mul]
        ring

/-- For noise in `[0, 1]`, `fLambda lam ^ n / 2^n` equals `2^(-n * (1 - logb 2 (fLambda lam)))`
[CotlerGongKannan2025]. -/
theorem single_block_bound {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    fLambda lam ^ (n : ℝ) / 2 ^ (n : ℝ) =
      (2 : ℝ) ^ (-(n : ℝ) * (1 - Real.logb 2 (fLambda lam))) := by
  have hF : (0 : ℝ) < fLambda lam := fLambda_pos' h0 h1
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_def_of_pos hF, Real.rpow_def_of_pos h2, Real.rpow_def_of_pos h2,
    Real.logb, ← Real.exp_sub]
  congr 1
  field_simp
  ring

/-- For noise in `[0, 1]`, multiplying the single-block factor by `2^k` adds `k` to its base-two
exponent [CotlerGongKannan2025]. -/
theorem single_block_bound_multi {n k : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (2 : ℝ) ^ (k : ℝ) * fLambda lam ^ (n : ℝ) / 2 ^ (n : ℝ) =
      (2 : ℝ) ^ ((k : ℝ) - (n : ℝ) * (1 - Real.logb 2 (fLambda lam))) := by
  have h := single_block_bound (n := n) h0 h1
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  calc (2 : ℝ) ^ (k : ℝ) * fLambda lam ^ (n : ℝ) / 2 ^ (n : ℝ) =
        2 ^ (k : ℝ) * (fLambda lam ^ (n : ℝ) / 2 ^ (n : ℝ)) := by ring
    _ = 2 ^ (k : ℝ) * (2 : ℝ) ^ (-(n : ℝ) * (1 - Real.logb 2 (fLambda lam))) := by rw [h]
    _ = 2 ^ (k : ℝ) / 2 ^ ((n : ℝ) * (1 - Real.logb 2 (fLambda lam))) := by
        rw [show -(n : ℝ) * (1 - Real.logb 2 (fLambda lam)) =
          -((n : ℝ) * (1 - Real.logb 2 (fLambda lam))) by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- For a finite nonnegative array, the squared Euclidean norm of the sum of its rows is at most
the square of the sum of their Euclidean norms [CotlerGongKannan2025]. -/
theorem delta_c_bound {ι σ : Type*} [Fintype ι] [Fintype σ] (x : ι → σ → ℝ)
    (hx : ∀ i j, 0 ≤ x i j) :
    (∑ j, (∑ i, x i j) ^ 2) ≤ (∑ i, Real.sqrt (∑ j, (x i j) ^ 2)) ^ 2 := by
  have hS : ∀ i, 0 ≤ ∑ j, (x i j) ^ 2 := fun i =>
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hpt : ∀ i k,
      (∑ j, x i j * x k j) ≤
        Real.sqrt (∑ j, (x i j) ^ 2) * Real.sqrt (∑ j, (x k j) ^ 2) := by
    intro i k
    have hcs : (∑ j, x i j * x k j) ^ 2 ≤
        (∑ j, (x i j) ^ 2) * (∑ j, (x k j) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => x i j) (fun j => x k j)
    calc (∑ j, x i j * x k j)
        ≤ Real.sqrt ((∑ j, (x i j) ^ 2) * (∑ j, (x k j) ^ 2)) := Real.le_sqrt_of_sq_le hcs
      _ = Real.sqrt (∑ j, (x i j) ^ 2) * Real.sqrt (∑ j, (x k j) ^ 2) :=
          Real.sqrt_mul (hS i) _
  calc (∑ j, (∑ i, x i j) ^ 2)
      = ∑ j, ∑ i, ∑ k, x i j * x k j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ∑ j, x i j * x k j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ ≤ ∑ i, ∑ k,
          Real.sqrt (∑ j, (x i j) ^ 2) * Real.sqrt (∑ j, (x k j) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        exact hpt i k
    _ = (∑ i, Real.sqrt (∑ j, (x i j) ^ 2)) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum]

end Qatlib.Papers.NoisyLearn26.MainResults.ShadowNoise
