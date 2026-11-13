/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WildcardSrch12.MainResults.Model.GramOverlap
import Qatlib.Papers.WildcardSrch12.MainResults.OneQueryCGT
import Mathlib.Data.Nat.Choose.Sum

set_option backward.isDefEq.respectTransparency false

/-!
# Constant Expected Hamming Error of Subset-State Pretty-Good Measurement

This module formalizes Lemma 3 of Ambainis and Montanaro showing that when
`k ≤ n` with `n - k ≤ √n`, the pretty-good measurement on the subset-query state
`|ψ_x^k⟩` outputs a bitstring whose expected Hamming distance from `x` is
bounded by an absolute constant `C`.

## Main statements

* `pgmProb_nonneg`, `pgmExpectedDistance_nonneg`: nonnegativity of PGM outcome
  probabilities and expected Hamming distance.
* `lemma3_pgm_expected_distance`: Lemma 3, proving `pgmExpectedDistance n k x ≤ C`
  whenever `1 ≤ n`, `k ≤ n`, and `n - k ≤ √n`.

## References

* [Ambainis and Montanaro, 2014][AmbainisMontanaro2014], Sections 2--3, Lemma 3,
  pp. 3 and 5--7.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults.StateDiscrimination

open Qatlib.Papers.WildcardSrch12.MainResults

private def FourierFlip {n : ℕ} (s : BitStr n) (i : Fin n) : BitStr n :=
  Function.update s i (!s i)

private def fourierSign (b : Bool) : ℝ := if b then -1 else 1

private theorem fourier_kernel_flip {n : ℕ} (s y : BitStr n) (i : Fin n) :
    OneQueryCGT.walshKernel (FourierFlip s i) y =
      fourierSign (y i) * OneQueryCGT.walshKernel s y := by
  classical
  have he : (∏ j ∈ Finset.univ.erase i,
      if FourierFlip s i j && y j then (-1 : ℝ) else 1) =
      ∏ j ∈ Finset.univ.erase i, if s j && y j then (-1 : ℝ) else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [FourierFlip, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  unfold OneQueryCGT.walshKernel
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if FourierFlip s i j && y j then (-1 : ℝ) else 1) (Finset.mem_univ i), he]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if s j && y j then (-1 : ℝ) else 1) (Finset.mem_univ i)]
  cases hs : s i <;> cases hy : y i <;> simp [FourierFlip, fourierSign, hs]

private theorem fourier_kernel_sq {n : ℕ} (s x : BitStr n) :
    OneQueryCGT.walshKernel s x ^ 2 = 1 := by
  unfold OneQueryCGT.walshKernel
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases hs : s i <;> cases hx : x i <;> norm_num [hs, hx]

private theorem fourier_hamming_sign {n : ℕ} (x y : BitStr n) :
    (hammingDist x y : ℝ) =
      ∑ i : Fin n, (1 - fourierSign (x i) * fourierSign (y i)) / 2 := by
  classical
  have hc : hammingDist x y = ∑ i : Fin n, if x i ≠ y i then 1 else 0 := by
    exact Finset.card_filter _ _
  rw [hc, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> cases hy : y i <;> norm_num [hx, hy, fourierSign]

private theorem fourier_weighted_bilinear {n : ℕ}
    (h a b : BitStr n → ℝ) :
    (∑ y : BitStr n, h y * (∑ s : BitStr n, a s * OneQueryCGT.walshKernel s y) *
      (∑ t : BitStr n, b t * OneQueryCGT.walshKernel t y)) =
    ∑ s : BitStr n, ∑ t : BitStr n, a s * b t *
      (∑ y : BitStr n, h y *
        (OneQueryCGT.walshKernel s y * OneQueryCGT.walshKernel t y)) := by
  classical
  calc
    _ = ∑ y : BitStr n, ∑ s : BitStr n, ∑ t : BitStr n,
        a s * b t * (h y *
          (OneQueryCGT.walshKernel s y * OneQueryCGT.walshKernel t y)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum Finset.univ
        (fun s => a s * OneQueryCGT.walshKernel s y) (h y), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]

private theorem fourier_parseval {n : ℕ} (a : BitStr n → ℝ) :
    (∑ y : BitStr n, (∑ s : BitStr n, a s * OneQueryCGT.walshKernel s y) ^ 2) =
      (2 : ℝ) ^ n * ∑ s : BitStr n, a s ^ 2 := by
  classical
  have h := fourier_weighted_bilinear (fun _ => 1) a a
  simp only [one_mul] at h
  simp only [pow_two]
  rw [h]
  simp only [OneQueryCGT.walsh_orthogonality, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem fourier_phase_parseval {n : ℕ} (a : BitStr n → ℝ) (x : BitStr n) :
    (∑ y : BitStr n,
      (∑ s : BitStr n, a s * OneQueryCGT.walshKernel s x *
        OneQueryCGT.walshKernel s y) ^ 2) =
      (2 : ℝ) ^ n * ∑ s : BitStr n, a s ^ 2 := by
  rw [fourier_parseval]
  simp only [mul_pow, fourier_kernel_sq, mul_one]

private theorem fourier_coordinate_correlation {n : ℕ}
    (a : BitStr n → ℝ) (x : BitStr n) (i : Fin n) :
    (∑ y : BitStr n, fourierSign (x i) * fourierSign (y i) *
      (∑ s : BitStr n, a s * OneQueryCGT.walshKernel s x *
        OneQueryCGT.walshKernel s y) ^ 2) =
      (2 : ℝ) ^ n * ∑ s : BitStr n, a s * a (FourierFlip s i) := by
  classical
  have ho (s t : BitStr n) :
      (∑ y : BitStr n, fourierSign (x i) * fourierSign (y i) *
        (OneQueryCGT.walshKernel s y * OneQueryCGT.walshKernel t y)) =
        fourierSign (x i) * (if FourierFlip s i = t then (2 : ℝ) ^ n else 0) := by
    calc
      _ = fourierSign (x i) *
          (∑ y : BitStr n, (fourierSign (y i) * OneQueryCGT.walshKernel s y) *
            OneQueryCGT.walshKernel t y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by
        simp only [← fourier_kernel_flip, OneQueryCGT.walsh_orthogonality]
  calc
    _ = ∑ y : BitStr n, (fourierSign (x i) * fourierSign (y i)) *
        (∑ s : BitStr n, (a s * OneQueryCGT.walshKernel s x) *
          OneQueryCGT.walshKernel s y) *
        (∑ s : BitStr n, (a s * OneQueryCGT.walshKernel s x) *
          OneQueryCGT.walshKernel s y) := by
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ s : BitStr n, ∑ t : BitStr n,
        (a s * OneQueryCGT.walshKernel s x) * (a t * OneQueryCGT.walshKernel t x) *
          (fourierSign (x i) * (if FourierFlip s i = t then (2 : ℝ) ^ n else 0)) := by
      rw [fourier_weighted_bilinear]
      simp only [ho]
    _ = _ := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [fourier_kernel_flip]
      have hx : fourierSign (x i) ^ 2 = 1 := by
        cases x i <;> norm_num [fourierSign]
      calc
        _ = (2 : ℝ) ^ n * (a s * a (FourierFlip s i)) *
            (fourierSign (x i) ^ 2 * OneQueryCGT.walshKernel s x ^ 2) := by ring
        _ = _ := by rw [hx, fourier_kernel_sq]; ring

private theorem fourier_hamming_parseval {n : ℕ}
    (a : BitStr n → ℝ) (x : BitStr n) :
    (∑ y : BitStr n, (hammingDist x y : ℝ) *
      ((1 / (2 : ℝ) ^ n) * ∑ s : BitStr n,
        a s * OneQueryCGT.walshKernel s x * OneQueryCGT.walshKernel s y) ^ 2) =
      (n : ℝ) / (2 * (2 : ℝ) ^ n) * (∑ s : BitStr n, a s ^ 2) -
        1 / (2 * (2 : ℝ) ^ n) *
          ∑ i : Fin n, ∑ s : BitStr n, a s * a (FourierFlip s i) := by
  classical
  let F (y : BitStr n) := ∑ s : BitStr n,
    a s * OneQueryCGT.walshKernel s x * OneQueryCGT.walshKernel s y
  have hu : (∑ y : BitStr n, (hammingDist x y : ℝ) * F y ^ 2) =
      (2 : ℝ) ^ n / 2 * ((n : ℝ) * (∑ s : BitStr n, a s ^ 2) -
        ∑ i : Fin n, ∑ s : BitStr n, a s * a (FourierFlip s i)) := by
    calc
      _ = ∑ i : Fin n, ∑ y : BitStr n,
          ((1 - fourierSign (x i) * fourierSign (y i)) / 2) * F y ^ 2 := by
        simp only [fourier_hamming_sign, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = ∑ i : Fin n, (2 : ℝ) ^ n / 2 *
          ((∑ s : BitStr n, a s ^ 2) -
            ∑ s : BitStr n, a s * a (FourierFlip s i)) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = (1 / 2 : ℝ) * (∑ y : BitStr n, F y ^ 2) -
              (1 / 2 : ℝ) * ∑ y : BitStr n,
                fourierSign (x i) * fourierSign (y i) * F y ^ 2 := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y _
            ring
          _ = _ := by
            dsimp only [F]
            rw [fourier_phase_parseval, fourier_coordinate_correlation]
            ring
      _ = _ := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hscale : (∑ y : BitStr n, (hammingDist x y : ℝ) *
      ((1 / (2 : ℝ) ^ n) * F y) ^ 2) =
      (1 / (2 : ℝ) ^ n) ^ 2 *
        (∑ y : BitStr n, (hammingDist x y : ℝ) * F y ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  change (∑ y : BitStr n, (hammingDist x y : ℝ) *
    ((1 / (2 : ℝ) ^ n) * F y) ^ 2) = _
  rw [hscale, hu]
  field_simp

/-- PGM outcome probabilities are nonnegative. -/
theorem pgmProb_nonneg {n k : ℕ} (x y : BitStr n) : 0 ≤ pgmProb n k x y :=
  Complex.normSq_nonneg _

/-- The expected Hamming distance of the PGM output is nonnegative. -/
theorem pgmExpectedDistance_nonneg {n k : ℕ} (x : BitStr n) :
    0 ≤ pgmExpectedDistance n k x :=
  Finset.sum_nonneg fun y _ =>
    mul_nonneg (Nat.cast_nonneg _) (pgmProb_nonneg x y)

private theorem binomial_sum_Icc (k : ℕ) :
    (∑ u ∈ Finset.Icc 1 k, (k.choose u : ℝ)) = (2 : ℝ) ^ k - 1 := by
  have hr : (∑ u ∈ Finset.range (k + 1), (k.choose u : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  have hs := Finset.sum_range_eq_add_Ico (fun u => (k.choose u : ℝ)) (Nat.succ_pos k)
  simp only [Nat.succ_eq_add_one] at hs
  rw [Finset.Ico_add_one_right_eq_Icc] at hs
  simp only [Nat.choose_zero_right, Nat.cast_one] at hs
  linarith

private theorem binomial_firstMoment_Icc (k : ℕ) :
    (∑ u ∈ Finset.Icc 1 k, (u : ℝ) * (k.choose u : ℝ)) =
      (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
  have hr : (∑ u ∈ Finset.range (k + 1), (u : ℝ) * (k.choose u : ℝ)) =
      (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
    exact_mod_cast Nat.sum_range_mul_choose k
  have hs := Finset.sum_range_eq_add_Ico
    (fun u => (u : ℝ) * (k.choose u : ℝ)) (Nat.succ_pos k)
  simp only [Nat.succ_eq_add_one] at hs
  rw [Finset.Ico_add_one_right_eq_Icc] at hs
  simp only [Nat.cast_zero, zero_mul, zero_add] at hs
  exact hs.symm.trans hr

private theorem binomial_reciprocal_Icc (k : ℕ) :
    (∑ u ∈ Finset.Icc 1 k, (k.choose u : ℝ) / ((u : ℝ) + 1)) ≤
      (2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
  have ht (u : ℕ) : (k.choose u : ℝ) / ((u : ℝ) + 1) =
      ((k + 1).choose (u + 1) : ℝ) / ((k : ℝ) + 1) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.add_one_mul_choose_eq k u)
    push_cast at h
    nlinarith only [h]
  calc
    (∑ u ∈ Finset.Icc 1 k, (k.choose u : ℝ) / ((u : ℝ) + 1)) ≤
        ∑ u ∈ Finset.range (k + 1), (k.choose u : ℝ) / ((u : ℝ) + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        have hu' := Finset.mem_Icc.mp hu
        exact Finset.mem_range.mpr (by omega)
      · intro u _ _
        positivity
    _ = (∑ u ∈ Finset.range (k + 1), ((k + 1).choose (u + 1) : ℝ)) /
        ((k : ℝ) + 1) := by simp_rw [ht]; rw [Finset.sum_div]
    _ ≤ (2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hr : (∑ u ∈ Finset.range (k + 1 + 1), ((k + 1).choose u : ℝ)) =
          (2 : ℝ) ^ (k + 1) := by
        exact_mod_cast Nat.sum_range_choose (k + 1)
      have hs := Finset.sum_range_succ'
        (fun u => ((k + 1).choose u : ℝ)) (k + 1)
      simp only [Nat.choose_zero_right, Nat.cast_one] at hs
      linarith

private theorem pgmProb_sum {n k : ℕ} (hk : k ≤ n) (x : BitStr n) :
    ∑ y : BitStr n, pgmProb n k x y = 1 := by
  have hs : (gramMat n k).sqrt.matᴴ * (gramMat n k).sqrt.mat =
      (gramMat n k).mat := by
    rw [HermitianMat.conjTranspose_mat]
    exact HermitianMat.sqrt_sq (ensembleGram_nonneg (psiEnsemble n k))
  have hc : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hd : (gramMat n k).mat x x = 1 := by
    rw [gramMat_mat, hammingDist_self]
    simp [gramEntry, hc]
  have he := congrArg (fun A : Matrix (BitStr n) (BitStr n) ℂ => A x x) hs
  rw [Matrix.mul_apply, hd] at he
  have ht : ∀ y : BitStr n,
      star ((gramMat n k).sqrt.mat y x) * (gramMat n k).sqrt.mat y x =
        (pgmProb n k x y : ℂ) := fun y => Complex.normSq_eq_conj_mul_self.symm
  simp only [Matrix.conjTranspose_apply, ht, ← Complex.ofReal_sum] at he
  exact_mod_cast he

private theorem pgmExpectedDistance_le_dimension {n k : ℕ} (hk : k ≤ n)
    (x : BitStr n) : pgmExpectedDistance n k x ≤ n := by
  calc
    pgmExpectedDistance n k x ≤ ∑ y : BitStr n, (n : ℝ) * pgmProb n k x y := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_right _ (pgmProb_nonneg x y)
      have hd : hammingDist x y ≤ n := by
        simpa [hammingDist] using
          (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i ≠ y i))
      exact_mod_cast hd
    _ = n := by rw [← Finset.mul_sum, pgmProb_sum hk, mul_one]

private theorem sqrt_product_lower (u g : ℝ) (hu : 1 ≤ u) (hg : 0 ≤ g) :
    u + g / 2 - g ^ 2 / (2 * (u + 1)) ≤ Real.sqrt (u * (u + g)) := by
  set t := g ^ 2 / (2 * (u + 1))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : 2 * (u + 1) * t = g ^ 2 := by
    dsimp [t]
    exact mul_div_cancel₀ _ (by linarith : 2 * (u + 1) ≠ 0)
  by_cases ha : 0 ≤ u + g / 2 - t
  · apply Real.le_sqrt_of_sq_le
    have hm : 0 ≤ t * (u - 1 + g + 2 * (u + g / 2 - t)) :=
      mul_nonneg ht (by linarith)
    nlinarith [he]
  · exact (le_of_lt (lt_of_not_ge ha)).trans (Real.sqrt_nonneg _)

private theorem binomial_sqrt_lower (k : ℕ) (g : ℝ) (hg : 0 ≤ g) :
    (k : ℝ) * (2 : ℝ) ^ (k - 1) +
        g / 2 * ((2 : ℝ) ^ k - 1) -
        g ^ 2 / 2 * ((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) ≤
      ∑ u ∈ Finset.Icc 1 k,
        (k.choose u : ℝ) * Real.sqrt ((u : ℝ) * ((u : ℝ) + g)) := by
  have hs : (∑ u ∈ Finset.Icc 1 k,
      (k.choose u : ℝ) *
        ((u : ℝ) + g / 2 - g ^ 2 / (2 * ((u : ℝ) + 1)))) =
      (k : ℝ) * (2 : ℝ) ^ (k - 1) + g / 2 * ((2 : ℝ) ^ k - 1) -
        g ^ 2 / 2 * ∑ u ∈ Finset.Icc 1 k,
          (k.choose u : ℝ) / ((u : ℝ) + 1) := by
    simp_rw [show ∀ u : ℕ, (k.choose u : ℝ) *
        ((u : ℝ) + g / 2 - g ^ 2 / (2 * ((u : ℝ) + 1))) =
        (u : ℝ) * (k.choose u : ℝ) +
          g / 2 * (k.choose u : ℝ) -
          g ^ 2 / 2 * ((k.choose u : ℝ) / ((u : ℝ) + 1)) by
      intro u
      field_simp]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, binomial_sum_Icc, binomial_firstMoment_Icc]
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 k,
        (k.choose u : ℝ) *
          ((u : ℝ) + g / 2 - g ^ 2 / (2 * ((u : ℝ) + 1))) := by
      rw [hs]
      have ht := mul_le_mul_of_nonneg_left (binomial_reciprocal_Icc k)
        (by positivity : 0 ≤ g ^ 2 / 2)
      linarith
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sqrt_product_lower u g (by exact_mod_cast (Finset.mem_Icc.mp hu).1) hg

private theorem binomial_distance_bound (n k : ℕ) (hk : k ≤ n) (hkpos : 1 ≤ k) :
    (n : ℝ) / 2 - 1 / (2 : ℝ) ^ k *
        ∑ z ∈ Finset.range k, (k.choose z : ℝ) *
          Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) ≤
      ((n - k : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) +
        ((n - k : ℕ) : ℝ) ^ 2 / ((k : ℝ) + 1) := by
  have he : (∑ z ∈ Finset.range k, (k.choose z : ℝ) *
      Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ))) =
      ∑ u ∈ Finset.Icc 1 k, (k.choose u : ℝ) *
        Real.sqrt ((u : ℝ) * ((u : ℝ) + ((n - k : ℕ) : ℝ))) := by
    refine Finset.sum_nbij' (fun z : ℕ => k - z) (fun u : ℕ => k - u)
      ?_ ?_ ?_ ?_ ?_
    · intro z hz
      have hz' := Finset.mem_range.mp hz
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro u hu
      have hu' := Finset.mem_Icc.mp hu
      exact Finset.mem_range.mpr (by omega)
    · intro z hz
      have hz' := Finset.mem_range.mp hz
      omega
    · intro u hu
      have hu' := Finset.mem_Icc.mp hu
      omega
    · intro z hz
      have hz' := Finset.mem_range.mp hz
      have hsub : n - z = (k - z) + (n - k) := by omega
      rw [Nat.choose_symm (by omega : z ≤ k), hsub, Nat.cast_add]
      congr 2
      ring
  have hs := binomial_sqrt_lower k ((n - k : ℕ) : ℝ) (Nat.cast_nonneg _)
  rw [← he] at hs
  have hp : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hkpos]
  have hp' : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ']
  have hkreal : (n : ℝ) = (k : ℝ) + ((n - k : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_sub_of_le hk).symm
  have hq : 0 < (2 : ℝ) ^ k := by positivity
  apply (mul_le_mul_iff_left₀ hq).mp
  calc
    ((n : ℝ) / 2 - 1 / (2 : ℝ) ^ k *
        ∑ z ∈ Finset.range k, (k.choose z : ℝ) *
          Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ))) * (2 : ℝ) ^ k =
        (n : ℝ) * (2 : ℝ) ^ k / 2 -
          ∑ z ∈ Finset.range k, (k.choose z : ℝ) *
            Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) := by
      field_simp
    _ ≤ (n : ℝ) * (2 : ℝ) ^ k / 2 -
        ((k : ℝ) * (2 : ℝ) ^ (k - 1) +
          ((n - k : ℕ) : ℝ) / 2 * ((2 : ℝ) ^ k - 1) -
          ((n - k : ℕ) : ℝ) ^ 2 / 2 *
            ((2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1))) := sub_le_sub_left hs _
    _ = _ := by
      rw [hkreal, hp', hp]
      field_simp
      ring

private theorem binomial_final_bound (n k : ℕ) (g : ℝ) (hn : 9 ≤ n)
    (hg : 0 ≤ g) (hgs : g ≤ Real.sqrt (n : ℝ))
    (hkg : (n : ℝ) - (k : ℝ) = g) :
    g / (2 : ℝ) ^ (k + 1) + g ^ 2 / ((k : ℝ) + 1) ≤ 8 := by
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  have hn9 : (9 : ℝ) ≤ n := by exact_mod_cast hn
  have hs3 : 3 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hs : 3 * Real.sqrt (n : ℝ) ≤ n := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs3)]
  have hg2 : g ^ 2 ≤ n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hgs) (add_nonneg hs0 hg)]
  have hd : 0 < (k : ℝ) + 1 := by positivity
  have hp : (k : ℝ) + 1 ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := k + 1)))
  calc
    g / (2 : ℝ) ^ (k + 1) + g ^ 2 / ((k : ℝ) + 1) ≤
        g / ((k : ℝ) + 1) + g ^ 2 / ((k : ℝ) + 1) :=
      add_le_add (div_le_div_of_nonneg_left hg hd hp) le_rfl
    _ = (g + g ^ 2) / ((k : ℝ) + 1) := by rw [add_div]
    _ ≤ 8 := (div_le_iff₀ hd).mpr (by nlinarith)

private theorem binomial_expected_distance_bound (n k : ℕ) (hn : 9 ≤ n)
    (hk : k ≤ n) (hclose : (n : ℝ) - (k : ℝ) ≤ Real.sqrt (n : ℝ)) :
    (n : ℝ) / 2 - 1 / (2 : ℝ) ^ k *
        ∑ z ∈ Finset.range k, (k.choose z : ℝ) *
          Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) ≤ 8 := by
  have hkpos : 1 ≤ k := by
    by_contra h
    have hkzero : k = 0 := by omega
    have hn9 : (9 : ℝ) ≤ n := by exact_mod_cast hn
    have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    simp only [hkzero, Nat.cast_zero, sub_zero] at hclose
    nlinarith
  refine (binomial_distance_bound n k hk hkpos).trans ?_
  apply binomial_final_bound n k ((n - k : ℕ) : ℝ) hn (Nat.cast_nonneg _)
  · simpa only [Nat.cast_sub hk] using hclose
  · exact (Nat.cast_sub hk).symm

private def weightEquiv (n : ℕ) : BitStr n ≃ Finset (Fin n) where
  toFun s := Finset.univ.filter (fun i => s i)
  invFun S i := decide (i ∈ S)
  left_inv s := by funext i; simp
  right_inv S := by ext i; simp

private theorem sum_bitWeight (n : ℕ) (f : ℕ → ℝ) :
    (∑ s : BitStr n, f (bitWeight s)) =
      ∑ z ∈ Finset.range (n + 1), (n.choose z : ℝ) * f z := by
  calc
    (∑ s : BitStr n, f (bitWeight s)) =
        ∑ S : Finset (Fin n), f S.card := by
      exact Equiv.sum_comp (weightEquiv n) (fun S => f S.card)
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, f S.card := by simp
    _ = _ := by
      rw [Finset.sum_powerset_apply_card]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem bitWeight_le {n : ℕ} (s : BitStr n) : bitWeight s ≤ n := by
  simpa [bitWeight] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => s i))

private theorem bitWeight_update_false {n : ℕ} (s : BitStr n) (i : Fin n)
    (hi : s i = false) : bitWeight (Function.update s i (!s i)) = bitWeight s + 1 := by
  have he : (Finset.univ.filter (fun j => Function.update s i (!s i) j)) =
      insert i (Finset.univ.filter (fun j => s j)) := by
    ext j
    by_cases hj : j = i
    · subst j; simp [hi]
    · simp [hj]
  simp only [bitWeight]
  rw [he, Finset.card_insert_of_notMem (by simp [hi])]

private theorem sum_false_coordinates {n : ℕ} (s : BitStr n) (c : ℝ) :
    (∑ i : Fin n, if s i = false then c else 0) = ((n - bitWeight s : ℕ) : ℝ) * c := by
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => s i = true)
  have hn : (Finset.univ.filter (fun i => s i = false)).card = n - bitWeight s := by
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at hc
    change bitWeight s + _ = n at hc
    omega
  rw [← Finset.sum_filter, Finset.sum_const, hn, nsmul_eq_mul]

private theorem sum_cube_edges (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, ∑ s : BitStr n,
      f (bitWeight s) * f (bitWeight (Function.update s i (!s i)))) =
      2 * ∑ z ∈ Finset.range (n + 1),
        (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) * f z * f (z + 1) := by
  classical
  have hinv (i : Fin n) :
      Function.Involutive (fun s : BitStr n => Function.update s i (!s i)) := by
    intro s
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  have hp (i : Fin n) :
      (∑ s : BitStr n, f (bitWeight s) *
        f (bitWeight (Function.update s i (!s i)))) =
      2 * ∑ s : BitStr n, if s i = false then
        f (bitWeight s) * f (bitWeight s + 1) else 0 := by
    let e : BitStr n ≃ BitStr n :=
      { toFun := fun s => Function.update s i (!s i)
        invFun := fun s => Function.update s i (!s i)
        left_inv := fun s => hinv i s
        right_inv := fun s => hinv i s }
    have hr := e.sum_comp
      (fun s : BitStr n => if s i = true then
        f (bitWeight s) * f (bitWeight (Function.update s i (!s i))) else 0)
    have hsplit : (∑ s : BitStr n, f (bitWeight s) *
        f (bitWeight (Function.update s i (!s i)))) =
        (∑ s : BitStr n, if s i = false then
          f (bitWeight s) * f (bitWeight s + 1) else 0) +
        (∑ s : BitStr n, if s i = true then
          f (bitWeight s) * f (bitWeight (Function.update s i (!s i))) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      cases hs : s i with
      | false =>
        have hw := bitWeight_update_false s i hs
        simp only [hs] at hw
        simp only [Bool.false_eq_true, ite_true, ite_false, add_zero]
        rw [hw]
      | true => simp
    have hr' : (∑ s : BitStr n, if s i = true then
        f (bitWeight s) * f (bitWeight (Function.update s i (!s i))) else 0) =
        ∑ s : BitStr n, if s i = false then
          f (bitWeight s) * f (bitWeight s + 1) else 0 := by
      rw [← hr]
      apply Finset.sum_congr rfl
      intro s _
      change (if (Function.update s i (!s i)) i = true then
        f (bitWeight (Function.update s i (!s i))) *
          f (bitWeight (Function.update (Function.update s i (!s i)) i
            (!(Function.update s i (!s i)) i))) else 0) = _
      have hflip := hinv i s
      dsimp only at hflip
      rw [hflip, Function.update_self]
      cases hs : s i with
      | false =>
        have hw := bitWeight_update_false s i hs
        simp only [hs] at hw
        rw [hw]
        simp [mul_comm]
      | true => simp
    rw [hsplit, hr']
    ring
  simp_rw [hp, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [sum_false_coordinates]
  rw [sum_bitWeight n (fun z => ((n - z : ℕ) : ℝ) * (f z * f (z + 1)))]
  apply Finset.sum_congr rfl
  intro z _
  ring

private def eigenWeight (n k z : ℕ) : ℝ :=
  if z ≤ k then (2 : ℝ) ^ n / ((2 : ℝ) ^ k * (n.choose k : ℝ)) *
    ((n - z).choose (k - z) : ℝ) else 0

private theorem eigenWeight_nonneg (n k z : ℕ) : 0 ≤ eigenWeight n k z := by
  unfold eigenWeight
  split_ifs <;> positivity

private theorem eigenWeight_mass {n k z : ℕ} (hk : k ≤ n) :
    (n.choose z : ℝ) * eigenWeight n k z =
      ((2 : ℝ) ^ n / (2 : ℝ) ^ k) * (k.choose z : ℝ) := by
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  by_cases hz : z ≤ k
  · simp only [eigenWeight, hz, ite_true]
    have hm : (n.choose k : ℝ) * (k.choose z : ℝ) =
        (n.choose z : ℝ) * ((n - z).choose (k - z) : ℝ) := by
      exact_mod_cast (Nat.choose_mul (n := n) hz)
    field_simp
    nlinarith only [hm]
  · simp [eigenWeight, hz, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hz)]

private theorem eigenWeight_step {n k z : ℕ} (hk : k ≤ n) (hz : z < k) :
    ((n - z : ℕ) : ℝ) * eigenWeight n k (z + 1) =
      ((k - z : ℕ) : ℝ) * eigenWeight n k z := by
  have hz' : z + 1 ≤ k := by omega
  have hn : n - z = (n - (z + 1)) + 1 := by omega
  have hku : k - z = (k - (z + 1)) + 1 := by omega
  have hm := Nat.add_one_mul_choose_eq (n - (z + 1)) (k - (z + 1))
  rw [← hn, ← hku] at hm
  have hm' : ((n - z : ℕ) : ℝ) * ((n - (z + 1)).choose (k - (z + 1)) : ℝ) =
      ((n - z).choose (k - z) : ℝ) * ((k - z : ℕ) : ℝ) := by exact_mod_cast hm
  simp only [eigenWeight, hz', Nat.le_of_lt hz, ite_true]
  nlinarith only [congrArg
    (fun t : ℝ => (2 : ℝ) ^ n / ((2 : ℝ) ^ k * (n.choose k : ℝ)) * t) hm']

private theorem eigenWeight_edge {n k z : ℕ} (hk : k ≤ n) (hz : z < k) :
    (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) *
        Real.sqrt (eigenWeight n k z) * Real.sqrt (eigenWeight n k (z + 1)) =
      ((2 : ℝ) ^ n / (2 : ℝ) ^ k) * (k.choose z : ℝ) *
        Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) := by
  have hmass := eigenWeight_mass (z := z) hk
  have hstep := eigenWeight_step hk hz
  have ha := eigenWeight_nonneg n k z
  have hb := eigenWeight_nonneg n k (z + 1)
  have hs : ((n.choose z : ℝ) * ((n - z : ℕ) : ℝ) *
        Real.sqrt (eigenWeight n k z) * Real.sqrt (eigenWeight n k (z + 1))) ^ 2 =
      (((2 : ℝ) ^ n / (2 : ℝ) ^ k) * (k.choose z : ℝ) *
        Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ))) ^ 2 := by
    calc
      _ = (n.choose z : ℝ) ^ 2 * ((n - z : ℕ) : ℝ) * eigenWeight n k z *
          (((n - z : ℕ) : ℝ) * eigenWeight n k (z + 1)) := by
        simp only [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
        ring
      _ = ((n.choose z : ℝ) * eigenWeight n k z) ^ 2 *
          (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) := by rw [hstep]; ring
      _ = _ := by
        rw [hmass]
        simp only [mul_pow, Real.sq_sqrt (by positivity :
          0 ≤ ((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ))]
  have hl : 0 ≤ (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) *
      Real.sqrt (eigenWeight n k z) * Real.sqrt (eigenWeight n k (z + 1)) := by positivity
  have hr : 0 ≤ ((2 : ℝ) ^ n / (2 : ℝ) ^ k) * (k.choose z : ℝ) *
      Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) := by positivity
  nlinarith

private theorem eigenWeight_sum {n k : ℕ} (hk : k ≤ n) :
    (∑ s : BitStr n, eigenWeight n k (bitWeight s)) = (2 : ℝ) ^ n := by
  rw [sum_bitWeight]
  simp_rw [eigenWeight_mass hk]
  rw [← Finset.mul_sum]
  have he : (∑ z ∈ Finset.range (n + 1), (k.choose z : ℝ)) = (2 : ℝ) ^ k := by
    have hs : (∑ z ∈ Finset.range (k + 1), (k.choose z : ℝ)) =
        ∑ z ∈ Finset.range (n + 1), (k.choose z : ℝ) := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro z _ hz
      rw [Finset.mem_range] at hz
      simp [Nat.choose_eq_zero_of_lt (by omega : k < z)]
    rw [← hs]
    exact_mod_cast Nat.sum_range_choose k
  rw [he, div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ k ≠ 0)]

private theorem eigenWeight_edge_sum {n k : ℕ} (hk : k ≤ n) :
    (∑ z ∈ Finset.range (n + 1), (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) *
        Real.sqrt (eigenWeight n k z) * Real.sqrt (eigenWeight n k (z + 1))) =
      ((2 : ℝ) ^ n / (2 : ℝ) ^ k) *
        ∑ z ∈ Finset.range k, (k.choose z : ℝ) *
          Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) := by
  have hs : (∑ z ∈ Finset.range k, (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) *
      Real.sqrt (eigenWeight n k z) * Real.sqrt (eigenWeight n k (z + 1))) =
      ∑ z ∈ Finset.range (n + 1), (n.choose z : ℝ) * ((n - z : ℕ) : ℝ) *
        Real.sqrt (eigenWeight n k z) * Real.sqrt (eigenWeight n k (z + 1)) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro z _ hz
    have hz' : ¬ z + 1 ≤ k := by simp only [Finset.mem_range] at hz; omega
    simp [eigenWeight, hz']
  rw [← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [eigenWeight_edge hk (Finset.mem_range.mp hz)]
  ring

private def spectralSupport {n : ℕ} (s : BitStr n) : Finset (Fin n) :=
  Finset.univ.filter fun i => s i

private def spectralCount (n k : ℕ) (s : BitStr n) : ℕ :=
  ((Finset.univ.powersetCard k).filter (spectralSupport s ⊆ ·)).card

private def spectralEigen (n k : ℕ) (s : BitStr n) : ℝ :=
  (2 : ℝ) ^ n / ((2 : ℝ) ^ k * (Nat.choose n k : ℝ)) * spectralCount n k s

private theorem spectralCount_eq {n k : ℕ} (s : BitStr n) :
    spectralCount n k s =
      if bitWeight s ≤ k then Nat.choose (n - bitWeight s) (k - bitWeight s) else 0 := by
  classical
  by_cases hs : bitWeight s ≤ k
  · simp only [hs, ite_true, spectralCount]
    have hc := Finset.card_filter_powersetCard_subset
      (spectralSupport s) (Finset.univ : Finset (Fin n)) k (Finset.subset_univ _)
      (show (spectralSupport s).card ≤ k from hs)
    simpa only [Finset.card_univ, Fintype.card_fin, spectralSupport, bitWeight] using hc
  · simp only [hs, ite_false, spectralCount]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro S hS hsub
    have hc := Finset.card_le_card hsub
    rw [(Finset.mem_powersetCard.mp hS).2] at hc
    exact hs hc

private theorem spectral_restricted_sum {n : ℕ} (x y : BitStr n)
    (S : Finset (Fin n)) :
    (∑ s : BitStr n, if spectralSupport s ⊆ S then
      OneQueryCGT.walshKernel x s * OneQueryCGT.walshKernel y s else 0) =
      if S ⊆ agreeSet x y then (2 : ℝ) ^ S.card else 0 := by
  classical
  let f : Fin n → Bool → ℝ := fun i b =>
    if b then
      if i ∈ S then (if x i then -1 else 1) * (if y i then -1 else 1) else 0
    else 1
  have hterm (s : BitStr n) :
      (if spectralSupport s ⊆ S then
        OneQueryCGT.walshKernel x s * OneQueryCGT.walshKernel y s else 0) =
        ∏ i, f i (s i) := by
    by_cases hs : spectralSupport s ⊆ S
    · simp only [hs, ite_true, OneQueryCGT.walshKernel, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      cases hsi : s i
      · simp [f]
      · have hi : i ∈ S := hs (by simp [spectralSupport, hsi])
        cases hxi : x i <;> cases hyi : y i <;> simp [f, hi, hxi, hyi]
    · simp only [hs, ite_false]
      obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp hs
      have hsi : s i = true := (Finset.mem_filter.mp hi).2
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hsi, hiS])
  rw [Finset.sum_congr rfl (fun s _ => hterm s), ← Fintype.prod_sum]
  have hc (i : Fin n) : (∑ b : Bool, f i b) =
      if i ∈ S then (if x i = y i then 2 else 0) else 1 := by
    by_cases hi : i ∈ S <;> cases hxi : x i <;> cases hyi : y i <;>
      norm_num [f, hi, hxi, hyi]
  simp_rw [hc]
  rw [Fintype.prod_ite_mem, Finset.prod_ite_zero]
  have he : (∀ i ∈ S, x i = y i) ↔ S ⊆ agreeSet x y := by
    simp [Finset.subset_iff, agreeSet]
  simp only [he, Finset.prod_const]

private theorem spectralEigen_eq_weight {n k : ℕ} (s : BitStr n) :
    spectralEigen n k s = eigenWeight n k (bitWeight s) := by
  rw [spectralEigen, spectralCount_eq]
  by_cases hs : bitWeight s ≤ k <;> simp [eigenWeight, hs]

private theorem spectral_count_expansion {n k : ℕ} (x y : BitStr n) :
    (∑ s : BitStr n, (spectralCount n k s : ℝ) *
      OneQueryCGT.walshKernel x s * OneQueryCGT.walshKernel y s) =
      (Nat.choose (n - hammingDist x y) k : ℝ) * (2 : ℝ) ^ k := by
  classical
  have hc (s : BitStr n) : (spectralCount n k s : ℝ) =
      ∑ S ∈ Finset.univ.powersetCard k,
        if spectralSupport s ⊆ S then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [spectralCount]
  simp_rw [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  have ht (S : Finset (Fin n)) :
      (∑ s : BitStr n, (if spectralSupport s ⊆ S then (1 : ℝ) else 0) *
        OneQueryCGT.walshKernel x s * OneQueryCGT.walshKernel y s) =
        if S ⊆ agreeSet x y then (2 : ℝ) ^ S.card else 0 := by
    convert spectral_restricted_sum x y S using 1
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp
  simp_rw [ht]
  have hr : (∑ S ∈ Finset.univ.powersetCard k,
      if S ⊆ agreeSet x y then (2 : ℝ) ^ S.card else 0) =
      ∑ S ∈ Finset.univ.powersetCard k,
        if S ⊆ agreeSet x y then (2 : ℝ) ^ k else 0 := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [hr, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Qatlib.Papers.WildcardSrch12.MainResults.card_filter_powersetCard_subset,
    card_agreeSet]

private theorem spectral_gram_entry {n k : ℕ} (hk : k ≤ n) (x y : BitStr n) :
    (gramMat n k).mat y x = ((2 : ℝ) ^ n)⁻¹ *
      ((∑ s : BitStr n, spectralEigen n k s *
        OneQueryCGT.walshKernel y s * OneQueryCGT.walshKernel x s : ℝ) : ℂ) := by
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hk2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hc : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have he : (∑ s : BitStr n, spectralEigen n k s *
      OneQueryCGT.walshKernel y s * OneQueryCGT.walshKernel x s) =
      (2 : ℝ) ^ n / ((2 : ℝ) ^ k * (Nat.choose n k : ℝ)) *
        ∑ s : BitStr n, (spectralCount n k s : ℝ) *
          OneQueryCGT.walshKernel y s * OneQueryCGT.walshKernel x s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [spectralEigen]
    ring
  rw [he, spectral_count_expansion, hammingDist_comm y x, gramMat_mat]
  rw [← Complex.ofReal_mul]
  congr 1
  unfold gramEntry
  field_simp

private def spectralWalsh (n : ℕ) : Matrix (BitStr n) (BitStr n) ℂ := fun x s =>
  (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * OneQueryCGT.walshKernel x s : ℝ) : ℂ)

private theorem spectralWalsh_star (n : ℕ) :
    (spectralWalsh n)ᴴ = spectralWalsh n := by
  ext x y
  change starRingEnd ℂ ((spectralWalsh n) y x) = (spectralWalsh n) x y
  simp only [spectralWalsh, Complex.conj_ofReal]
  rw [OneQueryCGT.walshKernel_comm y x]

private theorem spectralWalsh_sq (n : ℕ) : spectralWalsh n * spectralWalsh n = 1 := by
  classical
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hnorm : ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 2 * (2 : ℝ) ^ n = 1 := by
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ hn]
  ext x y
  rw [Matrix.mul_apply]
  simp only [spectralWalsh, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have he : (∑ s : BitStr n,
      ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * OneQueryCGT.walshKernel x s) *
        ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * OneQueryCGT.walshKernel s y)) =
      ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 2 *
        ∑ s : BitStr n, OneQueryCGT.walshKernel x s * OneQueryCGT.walshKernel y s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [OneQueryCGT.walshKernel_comm s y]
    ring
  rw [he, OneQueryCGT.walsh_orthogonality]
  by_cases hxy : x = y
  · simp [hxy, Matrix.one_apply]
  · simp [hxy]

private def spectralUnitary (n : ℕ) : Matrix.unitaryGroup (BitStr n) ℂ :=
  ⟨spectralWalsh n, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, spectralWalsh_star, spectralWalsh_sq])⟩

private theorem spectral_conj_diagonal_entry {n : ℕ} (f : BitStr n → ℝ)
    (x y : BitStr n) :
    ((HermitianMat.diagonal ℂ f).conj (spectralUnitary n).val).mat y x =
      (((2 : ℝ) ^ n)⁻¹ * ∑ s : BitStr n, f s *
        OneQueryCGT.walshKernel y s * OneQueryCGT.walshKernel x s : ℝ) := by
  have hnorm : ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [HermitianMat.conj_apply_mat, HermitianMat.diagonal_mat]
  change (spectralWalsh n * Matrix.diagonal (fun s => (f s : ℂ)) *
    (spectralWalsh n)ᴴ) y x = _
  rw [spectralWalsh_star, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, spectralWalsh, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [OneQueryCGT.walshKernel_comm s x, ← hnorm]
  ring

private theorem spectral_gram_diagonal {n k : ℕ} (hk : k ≤ n) :
    gramMat n k = (HermitianMat.diagonal ℂ (spectralEigen n k)).conj
      (spectralUnitary n).val := by
  apply HermitianMat.ext
  ext y x
  rw [spectral_conj_diagonal_entry, spectral_gram_entry hk x y, Complex.ofReal_mul]

private theorem spectral_sqrt_entry {n k : ℕ} (hk : k ≤ n) (x y : BitStr n) :
    (gramMat n k).sqrt.mat y x =
      (((2 : ℝ) ^ n)⁻¹ * ∑ s : BitStr n, Real.sqrt (spectralEigen n k s) *
        OneQueryCGT.walshKernel y s * OneQueryCGT.walshKernel x s : ℝ) := by
  rw [spectral_gram_diagonal hk, HermitianMat.sqrt,
    HermitianMat.cfc_conj_unitary, HermitianMat.cfc_diagonal]
  exact spectral_conj_diagonal_entry _ x y

private theorem spectral_sqrt_entry_weight {n k : ℕ} (hk : k ≤ n) (x y : BitStr n) :
    (gramMat n k).sqrt.mat y x =
      (((2 : ℝ) ^ n)⁻¹ * ∑ s : BitStr n, Real.sqrt (eigenWeight n k (bitWeight s)) *
        OneQueryCGT.walshKernel y s * OneQueryCGT.walshKernel x s : ℝ) := by
  rw [spectral_sqrt_entry hk]
  simp only [spectralEigen_eq_weight]

private theorem pgmExpectedDistance_eq_binomial {n k : ℕ} (hk : k ≤ n)
    (x : BitStr n) :
    pgmExpectedDistance n k x =
      (n : ℝ) / 2 - 1 / (2 : ℝ) ^ k *
        ∑ z ∈ Finset.range k, (k.choose z : ℝ) *
          Real.sqrt (((n - z : ℕ) : ℝ) * ((k - z : ℕ) : ℝ)) := by
  classical
  have hp (y : BitStr n) : pgmProb n k x y =
      ((1 / (2 : ℝ) ^ n) * ∑ s : BitStr n,
        Real.sqrt (eigenWeight n k (bitWeight s)) *
          OneQueryCGT.walshKernel s x * OneQueryCGT.walshKernel s y) ^ 2 := by
    rw [pgmProb, spectral_sqrt_entry_weight hk]
    simp only [Complex.normSq_ofReal, one_div, ← pow_two]
    apply congrArg (fun t : ℝ => t ^ 2)
    apply congrArg (fun t : ℝ => ((2 : ℝ) ^ n)⁻¹ * t)
    apply Finset.sum_congr rfl
    intro s _
    rw [OneQueryCGT.walshKernel_comm y s, OneQueryCGT.walshKernel_comm x s]
    ring
  unfold pgmExpectedDistance
  simp_rw [hp]
  rw [fourier_hamming_parseval]
  simp_rw [Real.sq_sqrt (eigenWeight_nonneg n k _)]
  rw [eigenWeight_sum hk]
  change (n : ℝ) / (2 * (2 : ℝ) ^ n) * (2 : ℝ) ^ n -
    1 / (2 * (2 : ℝ) ^ n) *
      (∑ i : Fin n, ∑ s : BitStr n,
        Real.sqrt (eigenWeight n k (bitWeight s)) *
          Real.sqrt (eigenWeight n k (bitWeight (Function.update s i (!s i))))) = _
  rw [sum_cube_edges n (fun z => Real.sqrt (eigenWeight n k z)), eigenWeight_edge_sum hk]
  field_simp

/-- Lemma 3: when `1 ≤ n`, `k ≤ n`, and `n - k ≤ √n`, the expected Hamming
distance `pgmExpectedDistance n k x` of the pretty-good measurement is bounded
above by a universal constant `C > 0`. -/
theorem lemma3_pgm_expected_distance :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (x : BitStr n),
        1 ≤ n → k ≤ n → (n : ℝ) - (k : ℝ) ≤ Real.sqrt (n : ℝ) →
        pgmExpectedDistance n k x ≤ C := by
  refine ⟨8, by norm_num, ?_⟩
  intro n k x hn hk hclose
  cases n with
  | zero => omega
  | succ n =>
    by_cases hsmall : n + 1 ≤ 8
    · exact (pgmExpectedDistance_le_dimension hk x).trans (by exact_mod_cast hsmall)
    · rw [pgmExpectedDistance_eq_binomial hk]
      exact binomial_expected_distance_bound (n + 1) k (by omega) hk hclose

end Qatlib.Papers.WildcardSrch12.MainResults.StateDiscrimination
