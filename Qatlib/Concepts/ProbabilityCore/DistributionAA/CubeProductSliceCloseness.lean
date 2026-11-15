/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeBinomial
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceContinuity
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Bounds the expected distance from Hamming weight to the floor of its mean by twice the
square root of the dimension. -/
theorem cube_mu_hamming_floor_deviation {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n : ℕ} (hn : 0 < n) :
    cubeExpect n (muWeight p n) (fun x => |(cubeHamming x : ℝ)-(Nat.floor (p*n) : ℝ)|) ≤
      2*Real.sqrt (n : ℝ) := by
  let w := muWeight p n
  let D := fun x : Fin n → Bool => |(cubeHamming x : ℝ)-p*n|
  have hw := muWeight_cubeWeight hp0 hp1 n
  have hD0 : 0 ≤ cubeExpect n w D := Finset.sum_nonneg fun x _ => mul_nonneg (hw.1 x) (abs_nonneg _)
  have hJ : (cubeExpect n w D)^2 ≤ cubeExpect n w (fun x => D x^2) := by
    have h := cubeVar_nonneg n hw D
    rw [cube_var_eq_second_moment_sub_sq n hw D] at h
    linarith
  have hM : cubeExpect n w (fun x => D x^2) = (n : ℝ)*p*(1-p) := by
    have he := cube_mu_hamming_variance hp0 hp1 n
    unfold cubeVar at he
    rw [cube_mu_hamming_mean] at he
    simpa only [D,w,sq_abs,mul_comm] using he
  rw [hM] at hJ
  have hVar : (n : ℝ)*p*(1-p) ≤ n := by
    have hp : p*(1-p) ≤ 1 := by nlinarith [sq_nonneg p]
    have he := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [he]
  have hE : cubeExpect n w D ≤ Real.sqrt (n : ℝ) := by
    nlinarith only [hJ,hVar,hD0,Real.sqrt_nonneg (n : ℝ),Real.sq_sqrt (Nat.cast_nonneg n)]
  have hfloor : |p*(n : ℝ)-(Nat.floor (p*n) : ℝ)| ≤ 1 := by
    have h0 := Nat.floor_le (show 0 ≤ p*(n : ℝ) by positivity)
    have h1 := Nat.lt_floor_add_one (p*(n : ℝ))
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hpnt (x : Fin n → Bool) : |(cubeHamming x : ℝ)-(Nat.floor (p*n) : ℝ)| ≤ D x+1 := by
    have he := abs_sub_le (cubeHamming x : ℝ) (p*n) (Nat.floor (p*n) : ℝ)
    exact he.trans (add_le_add le_rfl hfloor)
  have he : cubeExpect n w (fun x => |(cubeHamming x : ℝ)-(Nat.floor (p*n) : ℝ)|) ≤ cubeExpect n w D+1 := by
    calc
      _ ≤ cubeExpect n w (fun x => D x+1) := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpnt x) (hw.1 x)
      _ = _ := by rw [cube_expect_add]; simp [cubeExpect,w,hw.2]
  have hS : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [hnr,Real.sqrt_nonneg (n : ℝ),Real.sq_sqrt (Nat.cast_nonneg n)]
  linarith only [he,hE,hS]

/-- Bounds the product-slice expectation difference for a bounded degree-`d` function by eight
times the squared degree over the square root of the dimension. -/
theorem cube_product_slice_expectation_error {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n d : ℕ}
    {f : (Fin n → Bool) → ℝ} (hb : ∀ x, f x ∈ Set.Icc 0 1) (hd : CubeDegreeLE d f) :
    |cubeExpect n (muWeight p n) f-cubeExpect n (nuWeight p n) f| ≤ 8*(d : ℝ)^2/Real.sqrt (n : ℝ) := by
  by_cases hn : n=0
  · subst n
    have hw : muWeight p 0=nuWeight p 0 := by
      ext x; simp [muWeight,nuWeight,sliceWeight,cubeHamming]
    rw [hw,sub_self,abs_zero]
    simp
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    let k := Nat.floor (p*n)
    have hk : k ≤ n := by
      have h := Nat.floor_le (show 0 ≤ p*(n : ℝ) by positivity)
      have he := mul_le_mul_of_nonneg_right hp1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      simp only [one_mul] at he
      exact_mod_cast h.trans he
    let F := fun j => cubeExpect n (sliceWeight n j) f
    let C := 4*(d : ℝ)^2/(n : ℝ)
    have hC : 0 ≤ C := by positivity
    have hsum := cube_binomial_weights_sum hp0.le hp1.le n
    have hdiff : cubeExpect n (muWeight p n) f-cubeExpect n (nuWeight p n) f =
        ∑ j : Fin (n+1), cubeBinomialWeight p n j*(F j-F k) := by
      rw [cube_product_slice_decomposition]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
      rfl
    have hDev := cube_mu_hamming_floor_deviation hp0.le hp1.le hn0
    have hBin : (∑ j : Fin (n+1), cubeBinomialWeight p n j*|(j : ℝ)-(k : ℝ)|) ≤ 2*Real.sqrt (n : ℝ) := by
      have he := cube_binomial_hamming_expectation p n (fun j => |(j : ℝ)-(k : ℝ)|)
      simpa only [← he,k] using hDev
    rw [hdiff]
    calc
      _ ≤ ∑ j : Fin (n+1), |cubeBinomialWeight p n j*(F j-F k)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin (n+1), cubeBinomialWeight p n j*|F j-F k| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul,abs_of_nonneg (cube_binomial_weights_nonneg hp0.le hp1.le n j)]
      _ ≤ ∑ j : Fin (n+1), cubeBinomialWeight p n j*(C*|(j : ℝ)-(k : ℝ)|) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (cube_slice_expectation_lipschitz hb hd j k (Nat.le_of_lt_succ j.isLt) hk)
          (cube_binomial_weights_nonneg hp0.le hp1.le n j)
      _ = C*(∑ j : Fin (n+1), cubeBinomialWeight p n j*|(j : ℝ)-(k : ℝ)|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ C*(2*Real.sqrt (n : ℝ)) := mul_le_mul_of_nonneg_left hBin hC
      _ = 8*(d : ℝ)^2/Real.sqrt (n : ℝ) := by
        have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn0)).ne'
        have he := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        dsimp [C]
        field_simp
        nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (show 0 ≤ (n : ℝ) by positivity)]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
