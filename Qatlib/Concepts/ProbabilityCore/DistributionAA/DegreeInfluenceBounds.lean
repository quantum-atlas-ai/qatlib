/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubePolynomial
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSymmetry
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSlicePoincare
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open Polynomial
open scoped Classical BigOperators

theorem cube_flip_sum_le_two {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (x : Fin n → Bool) (A : Finset (Fin n)) :
    |∑ i ∈ A, (f x-f (cubeFlip x i))| ≤ 2*(d : ℝ)^2 := by
  obtain ⟨c,hc,hf⟩ := hd
  let q := cubeNoisePolynomial x A
  let P := cubeExpectationPolynomial c q
  have hP : P.natDegree ≤ d := cube_expectation_polynomial_degree_le c q hc
    (cube_noise_polynomial_degree x A)
  have hG : (P-Polynomial.C (1/2 : ℝ)).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hP (by simp))
  have hbP (t : ℝ) (ht : t ∈ Set.Icc 0 1) : P.eval t ∈ Set.Icc 0 1 := by
    rw [cube_expectation_polynomial_eval c hf q t]
    exact cube_expect_range (cube_coordinate_weight_normalized _
      (fun i => cube_noise_polynomial_eval_range x A i ht)) hb
  have hM := markov_brothers_unit_deriv_le hG (by norm_num : (0 : ℝ) ≤ 1/2)
    (fun t ht => by
      simp only [Polynomial.eval_sub, Polynomial.eval_C]
      apply abs_le.2
      constructor <;> linarith [(hbP t ht).1,(hbP t ht).2]) 0 (by norm_num)
  simp only [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero] at hM
  have hder := cube_noise_expectation_derivative c hf x A
  have hneg : (∑ i ∈ A, (f x-f (cubeFlip x i))) = -(∑ i ∈ A, (f (cubeFlip x i)-f x)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg, abs_neg, ← hder]
  change |P.derivative.eval 0| ≤ _
  nlinarith only [hM]

theorem cube_flip_sum_le {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f)
    (x : Fin n → Bool) (A : Finset (Fin n)) :
    |∑ i ∈ A, (f x-f (cubeFlip x i))| ≤ 4*(d : ℝ)^2 :=
  (cube_flip_sum_le_two hb hd x A).trans (by nlinarith [sq_nonneg (d : ℝ)])

theorem cube_point_flip_square_sum_le {n d : ℕ} {f : (Fin n → Bool) → ℝ}
    (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) (x : Fin n → Bool) :
    (∑ i, (f x-f (cubeFlip x i))^2) ≤ 4*(d : ℝ)^2 := by
  let a := fun i : Fin n => f x-f (cubeFlip x i)
  let P := Finset.univ.filter (fun i => 0 ≤ a i)
  let N := Finset.univ.filter (fun i => a i < 0)
  have hA : (∑ i, |a i|) = (∑ i ∈ P, a i)-(∑ i ∈ N, a i) := by
    dsimp [P,N]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · simp [hi, not_lt_of_ge hi, abs_of_nonneg hi]
    · have hn : a i < 0 := lt_of_not_ge hi
      simp [hi, hn, abs_of_neg hn]
  have hp : (∑ i ∈ P, a i) ≤ 2*(d : ℝ)^2 :=
    (le_abs_self _).trans (cube_flip_sum_le_two hb hd x P)
  have hn : -(∑ i ∈ N, a i) ≤ 2*(d : ℝ)^2 :=
    (neg_le_abs _).trans (cube_flip_sum_le_two hb hd x N)
  have hsum : (∑ i, |a i|) ≤ 4*(d : ℝ)^2 := by rw [hA]; linarith
  calc
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      have habs : |a i| ≤ 1 := by
        apply abs_le.2
        dsimp [a]
        constructor <;> linarith [(hb x).1,(hb x).2,(hb (cubeFlip x i)).1,(hb (cubeFlip x i)).2]
      change (a i)^2 ≤ |a i|
      nlinarith [sq_abs (a i), abs_nonneg (a i)]
    _ ≤ _ := hsum

theorem cube_total_inf_le {n d : ℕ} {w : (Fin n → Bool) → ℝ} (hw : CubeWeight n w)
    {f : (Fin n → Bool) → ℝ} (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) :
    cubeTotalInf n w f ≤ 8*(d : ℝ)^2 := by
  unfold cubeTotalInf cubeInf cubeExpect
  rw [Finset.sum_comm]
  calc
    _ = ∑ x, w x*(∑ i, (f x-f (cubeFlip x i))^2) := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ x, w x*(4*(d : ℝ)^2) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (cube_point_flip_square_sum_le hb hd x) (hw.1 x)
    _ = 4*(d : ℝ)^2 := by rw [← Finset.sum_mul, hw.2, one_mul]
    _ ≤ _ := by nlinarith [sq_nonneg (d : ℝ)]

theorem swap_inf_le_two_add {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {f : (Fin n → Bool) → ℝ} (i j : Fin n) :
    cubeExpect n (nuWeight p n) (fun x => (f x-f (cubeSwap x i j))^2) ≤
      2*(cubeInf n (nuWeight p n) f i+cubeInf n (nuWeight p n) f j) := by
  have hw := nuWeight_cubeWeight hp0 hp1 n
  have hpoint (x : Fin n → Bool) : (f x-f (cubeSwap x i j))^2 ≤
      2*((f x-f (cubeFlip x i))^2+
        (f (cubeSwap x i j)-f (cubeFlip (cubeSwap x i j) j))^2) := by
    by_cases hx : x i=x j
    · rw [cube_swap_same_bits x i j hx]
      nlinarith [sq_nonneg (f x-f (cubeFlip x i)), sq_nonneg (f x-f (cubeFlip x j))]
    · rw [cube_swap_flip_path x i j hx]
      nlinarith only [sq_nonneg (f x+f (cubeSwap x i j)-2*f (cubeFlip x i))]
  calc
    _ ≤ cubeExpect n (nuWeight p n) (fun x => 2*((f x-f (cubeFlip x i))^2+
          (f (cubeSwap x i j)-f (cubeFlip (cubeSwap x i j) j))^2)) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw.1 x)
    _ = _ := by
      rw [cube_expect_const_mul, cube_expect_add,
        cube_expect_swap p (fun x => (f x-f (cubeFlip x j))^2) i j]
      rfl

theorem exists_inf_ge_var_div_two_n_sq {n : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 0 < n) {f : (Fin n → Bool) → ℝ} :
    (∃ i : Fin n, cubeVar n (muWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (muWeight p n) f i) ∧
    (∃ i : Fin n, cubeVar n (nuWeight p n) f ≤ 2*(n : ℝ)^2*cubeInf n (nuWeight p n) f i) :=
  cube_both_exists_large_influence hp0 hp1 hn f

end Qatlib.Concepts.ProbabilityCore.DistributionAA
