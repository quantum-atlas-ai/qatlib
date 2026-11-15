/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeHammingMoments

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Bounds the Hamming weight of a Boolean vector by its dimension. -/
theorem cube_hamming_le {n : ℕ} (x : Fin n → Bool) : cubeHamming x ≤ n := by
  unfold cubeHamming
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Expresses a product-measure point weight in terms of its Hamming weight. -/
theorem muWeight_eq_hamming (p : ℝ) (n : ℕ) (x : Fin n → Bool) :
    muWeight p n x = p^(cubeHamming x)*(1-p)^(n-cubeHamming x) := by
  unfold muWeight
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have he : Finset.univ.filter (fun i : Fin n => ¬x i=true) =
      Finset.univ.filter (fun i : Fin n => x i=false) := by ext i; cases x i <;> simp
  rw [he]
  have hc : (Finset.univ.filter (fun i : Fin n => x i=false)).card = n-cubeHamming x := by
    have hz := cube_zero_count x
    omega
  rw [hc]
  rfl

def cubeBinomialWeight (p : ℝ) (n k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ)*p^k*(1-p)^(n-k)

/-- Evaluates the slice expectation of a function of Hamming weight at the slice index. -/
theorem cube_slice_hamming_function (n k : ℕ) (hk : k ≤ n) (g : ℕ → ℝ) :
    cubeExpect n (sliceWeight n k) (fun x => g (cubeHamming x)) = g k := by
  have hw := sliceWeight_cubeWeight n k hk
  have he (x : Fin n → Bool) : sliceWeight n k x*g (cubeHamming x) = sliceWeight n k x*g k := by
    unfold sliceWeight
    split_ifs with hx
    · rw [hx]
    · simp
  unfold cubeExpect
  simp_rw [he]
  rw [← Finset.sum_mul,hw.2,one_mul]

/-- Decomposes a product-measure expectation into binomially weighted slice expectations. -/
theorem cube_product_slice_decomposition (p : ℝ) (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (muWeight p n) f =
      ∑ k : Fin (n+1), cubeBinomialWeight p n k*cubeExpect n (sliceWeight n k) f := by
  have hk (k : Fin (n+1)) : (k : ℕ) ≤ n := Nat.le_of_lt_succ k.isLt
  have hterm (k : Fin (n+1)) : cubeBinomialWeight p n k*cubeExpect n (sliceWeight n k) f =
      (p^(k : ℕ)*(1-p)^(n-(k : ℕ)))*∑ x : Fin n → Bool, if cubeHamming x=k then f x else 0 := by
    have hc : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ) ≠ 0 :=
      by exact_mod_cast (cube_slice_card_pos n k (hk k)).ne'
    rw [cube_slice_expect_uniform]
    unfold cubeBinomialWeight
    field_simp
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold cubeExpect
  apply Finset.sum_congr rfl
  intro x _
  let j : Fin (n+1) := ⟨cubeHamming x, Nat.lt_succ_of_le (cube_hamming_le x)⟩
  have he (k : Fin (n+1)) : cubeHamming x=(k : ℕ) ↔ k=j := by
    constructor
    · intro h; apply Fin.ext; simpa [j] using h.symm
    · intro h; subst k; rfl
  simp_rw [mul_ite, mul_zero, he]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ j), muWeight_eq_hamming]

/-- Shows that binomial weights are nonnegative for biases in the unit interval. -/
theorem cube_binomial_weights_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) :
    0 ≤ cubeBinomialWeight p n k := by unfold cubeBinomialWeight; positivity

/-- Shows that the binomial weights sum to one for biases in the unit interval. -/
theorem cube_binomial_weights_sum {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (∑ k : Fin (n+1), cubeBinomialWeight p n k) = 1 := by
  have he := cube_product_slice_decomposition p n (fun _ => (1 : ℝ))
  have hw := muWeight_cubeWeight hp0 hp1 n
  have hk (k : Fin (n+1)) : cubeExpect n (sliceWeight n k) (fun _ => (1 : ℝ)) = 1 := by
    have hn := (sliceWeight_cubeWeight n k (Nat.le_of_lt_succ k.isLt)).2
    simpa [cubeExpect] using hn
  simp only [hk,mul_one] at he
  rw [← he]
  simpa [cubeExpect] using hw.2

/-- Expresses the product expectation of a Hamming-weight function as a binomial weighted sum. -/
theorem cube_binomial_hamming_expectation (p : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    cubeExpect n (muWeight p n) (fun x => g (cubeHamming x)) =
      ∑ k : Fin (n+1), cubeBinomialWeight p n k*g k := by
  rw [cube_product_slice_decomposition]
  apply Finset.sum_congr rfl
  intro k _
  rw [cube_slice_hamming_function n k (Nat.le_of_lt_succ k.isLt)]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
