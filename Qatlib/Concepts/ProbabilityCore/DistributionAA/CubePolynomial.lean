/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.MarkovBrothers

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open Polynomial
open scoped Classical BigOperators

def cubeMonomial {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ S, if x i then (1 : ℝ) else 0

def cubeCoordinateWeight {n : ℕ} (q : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, if x i then q i else 1-q i

theorem cube_coordinate_weight_normalized {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc 0 1) : CubeWeight n (cubeCoordinateWeight q) := by
  constructor
  · intro x
    apply Finset.prod_nonneg
    intro i _
    split_ifs <;> linarith [(hq i).1,(hq i).2]
  · unfold cubeCoordinateWeight
    calc
      _ = ∏ i, ∑ b : Bool, (if b then q i else 1-q i) :=
        (Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b then q i else 1-q i)).symm
      _ = 1 := by simp

theorem cube_coordinate_monomial_expect {n : ℕ} (q : Fin n → ℝ) (S : Finset (Fin n)) :
    cubeExpect n (cubeCoordinateWeight q) (cubeMonomial S) = ∏ i ∈ S, q i := by
  let h := fun (i : Fin n) (b : Bool) =>
    (if b then q i else 1-q i)*(if i ∈ S then (if b then (1 : ℝ) else 0) else 1)
  have he (x : Fin n → Bool) : cubeCoordinateWeight q x*cubeMonomial S x = ∏ i, h i (x i) := by
    dsimp [h,cubeCoordinateWeight,cubeMonomial]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
  unfold cubeExpect
  simp_rw [he]
  rw [← Fintype.prod_sum h]
  have hi (i : Fin n) : (∑ b : Bool, h i b) = if i ∈ S then q i else 1 := by
    dsimp [h]
    by_cases his : i ∈ S <;> simp [his]
  simp only [hi, Finset.prod_ite_mem_eq]

def cubeExpectationPolynomial {n : ℕ} (c : Finset (Fin n) → ℝ)
    (q : Fin n → Polynomial ℝ) : Polynomial ℝ :=
  ∑ S : Finset (Fin n), Polynomial.C (c S)*∏ i ∈ S, q i

theorem cube_expectation_polynomial_eval {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (c : Finset (Fin n) → ℝ) (hf : ∀ x, f x = ∑ S, c S*cubeMonomial S x)
    (q : Fin n → Polynomial ℝ) (t : ℝ) :
    (cubeExpectationPolynomial c q).eval t =
      cubeExpect n (cubeCoordinateWeight (fun i => (q i).eval t)) f := by
  simp only [cubeExpectationPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod]
  unfold cubeExpect
  simp_rw [hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  have he := cube_coordinate_monomial_expect (fun i => (q i).eval t) S
  change c S*(∏ i ∈ S, (q i).eval t) = _
  calc
    _ = c S*∑ x, cubeCoordinateWeight (fun i => (q i).eval t) x*cubeMonomial S x := by rw [← he]; rfl
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem cube_expectation_polynomial_degree_le {n d : ℕ} (c : Finset (Fin n) → ℝ)
    (q : Fin n → Polynomial ℝ) (hc : ∀ S, d < S.card → c S = 0)
    (hq : ∀ i, (q i).natDegree ≤ 1) : (cubeExpectationPolynomial c q).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro S _
  by_cases hs : d < S.card
  · simp [hc S hs]
  · have hp : (∏ i ∈ S, q i).natDegree ≤ S.card := by
      apply (Polynomial.natDegree_prod_le _ _).trans
      calc
        (∑ i ∈ S, (q i).natDegree) ≤ ∑ _i ∈ S, 1 := Finset.sum_le_sum fun i _ => hq i
        _ = S.card := by simp
    have hm := Polynomial.natDegree_mul_le (p := Polynomial.C (c S)) (q := ∏ i ∈ S, q i)
    simp only [Polynomial.natDegree_C, zero_add] at hm
    exact hm.trans (hp.trans (Nat.le_of_not_gt hs))

theorem cube_expect_range {n : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 1) : cubeExpect n w f ∈ Set.Icc 0 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (hf x).1
  · calc
      _ ≤ ∑ x, w x*1 := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x).2 (hw.1 x)
      _ = 1 := by simp only [mul_one]; exact hw.2

def cubeNoisePolynomial {n : ℕ} (x : Fin n → Bool) (A : Finset (Fin n)) (i : Fin n) : Polynomial ℝ :=
  if i ∈ A then (if x i then 1-Polynomial.X else Polynomial.X)
  else Polynomial.C (if x i then (1 : ℝ) else 0)

theorem cube_noise_polynomial_degree {n : ℕ} (x : Fin n → Bool) (A : Finset (Fin n)) (i : Fin n) :
    (cubeNoisePolynomial x A i).natDegree ≤ 1 := by
  unfold cubeNoisePolynomial
  split_ifs
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp
  · simp
  · simp

theorem cube_noise_polynomial_eval_zero {n : ℕ} (x : Fin n → Bool) (A : Finset (Fin n)) (i : Fin n) :
    (cubeNoisePolynomial x A i).eval 0 = if x i then (1 : ℝ) else 0 := by
  unfold cubeNoisePolynomial
  split_ifs <;> simp_all

theorem cube_noise_polynomial_eval_range {n : ℕ} (x : Fin n → Bool) (A : Finset (Fin n))
    (i : Fin n) {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (cubeNoisePolynomial x A i).eval t ∈ Set.Icc 0 1 := by
  unfold cubeNoisePolynomial
  split_ifs <;> simp_all

theorem cube_noise_polynomial_derivative {n : ℕ} (x : Fin n → Bool) (A : Finset (Fin n)) (i : Fin n) :
    (cubeNoisePolynomial x A i).derivative.eval 0 =
      if i ∈ A then 1-2*(if x i then (1 : ℝ) else 0) else 0 := by
  unfold cubeNoisePolynomial
  split_ifs <;> norm_num [*]

theorem cube_monomial_flip_difference {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) :
    cubeMonomial S (cubeFlip x i)-cubeMonomial S x =
      if i ∈ S then (1-2*(if x i then (1 : ℝ) else 0))*cubeMonomial (S.erase i) x else 0 := by
  by_cases hi : i ∈ S
  · have hprod (y : Fin n → Bool) : cubeMonomial S y =
        (if y i then (1 : ℝ) else 0)*cubeMonomial (S.erase i) y :=
      (Finset.mul_prod_erase S (fun j => if y j then (1 : ℝ) else 0) hi).symm
    have herase : cubeMonomial (S.erase i) (cubeFlip x i) = cubeMonomial (S.erase i) x := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [cubeFlip, (Finset.mem_erase.1 hj).1]
    rw [if_pos hi, hprod, hprod, herase]
    cases hx : x i
    · simp [cubeFlip,hx]
    · simp [cubeFlip,hx]
      ring
  · rw [if_neg hi]
    have he : cubeMonomial S (cubeFlip x i) = cubeMonomial S x := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by intro he; subst j; exact hi hj
      simp [cubeFlip, hji]
    rw [he, sub_self]

theorem cube_noise_product_derivative {n : ℕ} (x : Fin n → Bool) (A S : Finset (Fin n)) :
    (∏ i ∈ S, cubeNoisePolynomial x A i).derivative.eval 0 =
      ∑ i ∈ A, (cubeMonomial S (cubeFlip x i)-cubeMonomial S x) := by
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, cube_noise_polynomial_eval_zero,
    cube_noise_polynomial_derivative]
  simp_rw [cube_monomial_flip_difference]
  change (∑ i ∈ S,
      cubeMonomial (S.erase i) x*(if i ∈ A then 1-2*(if x i then (1 : ℝ) else 0) else 0)) = _
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have he : S.filter (fun i => i ∈ A) = A.filter (fun i => i ∈ S) := by ext i; simp [and_comm]
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cube_noise_expectation_derivative {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (c : Finset (Fin n) → ℝ) (hf : ∀ x, f x = ∑ S, c S*cubeMonomial S x)
    (x : Fin n → Bool) (A : Finset (Fin n)) :
    (cubeExpectationPolynomial c (cubeNoisePolynomial x A)).derivative.eval 0 =
      ∑ i ∈ A, (f (cubeFlip x i)-f x) := by
  simp only [cubeExpectationPolynomial, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, cube_noise_product_derivative]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hf]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

end Qatlib.Concepts.ProbabilityCore.DistributionAA
