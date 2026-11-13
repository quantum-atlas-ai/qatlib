/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WildcardSrch12.MainResults.Model.GramOverlap
import Qatlib.Papers.WildcardSrch12.MainResults.OneQueryCGT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option backward.isDefEq.respectTransparency false

/-!
# Exponential Upper Bound on the Pretty-Good Measurement Diagonal

This module formalizes Lemma 9 of Ambainis and Montanaro showing that when
`k = n - a √n` with `a ≥ 0`, the diagonal success probability `pgmProb n k x x`
of the pretty-good measurement on the subset-query state ensemble is at most
`4 exp(-a^2 / 32)`.

## Main statements

* `lemma9_gram_diagonal_upper`: Lemma 9, `pgmProb n k x x ≤ 4 * Real.exp (-(a ^ 2) / 32)`.
* `lemma9_bound_le_four`: monotonicity bound `4 * Real.exp (-(a ^ 2) / 32) ≤ 4`.

## References

* [Ambainis and Montanaro, 2014][AmbainisMontanaro2014], Appendix A, Lemma 9, p. 12.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators
open scoped Classical

open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults.GramDiagonalUpper

open Qatlib.Papers.WildcardSrch12.MainResults
open OneQueryCGT

/-- The support of the character indexed by `s` is contained in `T`. -/
private def supported {n : ℕ} (T : Finset (Fin n)) (s : BitStr n) : Prop :=
  ∀ i, s i = true → i ∈ T

private theorem supported_sum_prod {n : ℕ} (T : Finset (Fin n))
    (f : Fin n → Bool → ℝ) :
    (∑ s : BitStr n, if supported T s then ∏ i, f i (s i) else 0) =
      ∏ i, (f i false + if i ∈ T then f i true else 0) := by
  classical
  have hterm (s : BitStr n) :
      (if supported T s then ∏ i, f i (s i) else 0) =
        ∏ i, if s i = true → i ∈ T then f i (s i) else 0 := by
    by_cases hs : supported T s
    · simp only [hs, ite_true]
      exact Finset.prod_congr rfl fun i _ => by
        split
        · rfl
        · rename_i h
          exact False.elim (h (hs i))
    · simp only [hs, ite_false]
      obtain ⟨i, hi, hiT⟩ : ∃ i, s i = true ∧ i ∉ T := by
        simpa [supported] using hs
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hiT])).symm
  simp_rw [hterm]
  rw [← Fintype.prod_sum (κ := fun _ : Fin n => Bool)
    (f := fun i b => if b = true → i ∈ T then f i b else 0)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

/-- The exponential weight `exp (r * |s|)`, factored over the coordinates. -/
private def tilt {n : ℕ} (r : ℝ) (s : BitStr n) : ℝ :=
  ∏ i, if s i then Real.exp r else 1

private theorem tilt_add {n : ℕ} (r t : ℝ) (s : BitStr n) :
    tilt (r + t) s = tilt r s * tilt t s := by
  unfold tilt
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [Real.exp_add]

private theorem tilt_zero {n : ℕ} (s : BitStr n) : tilt 0 s = 1 := by
  simp [tilt]

private theorem supported_tilt_sum {n : ℕ} (T : Finset (Fin n)) (r : ℝ) :
    (∑ s : BitStr n, if supported T s then tilt r s else 0) =
      (1 + Real.exp r) ^ T.card := by
  classical
  unfold tilt
  rw [supported_sum_prod T (fun _ b => if b then Real.exp r else 1)]
  have hprod : (∏ i : Fin n, (1 + if i ∈ T then Real.exp r else 0)) =
      ∏ i : Fin n, if i ∈ T then (1 + Real.exp r) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    split <;> simp_all
  simp only [Bool.false_eq_true, ite_false, ite_true,
    hprod, Fintype.prod_ite_mem, Finset.prod_const]

private theorem tilt_sum (n : ℕ) (r : ℝ) :
    (∑ s : BitStr n, tilt r s) = (1 + Real.exp r) ^ n := by
  have h := supported_tilt_sum (Finset.univ : Finset (Fin n)) r
  simpa [supported] using h

/-- The eigenvalue indexed by `s`, divided by `2^n`. Keeping the count of containing
`k`-subsets as a sum lets us compute its generating function without regrouping by weight. -/
private def spectralMass (n k : ℕ) (s : BitStr n) : ℝ :=
  (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    if supported T s then 1 else 0) / ((Nat.choose n k : ℝ) * 2 ^ k)

private theorem spectralMass_nonneg (n k : ℕ) (s : BitStr n) :
    0 ≤ spectralMass n k s := by
  unfold spectralMass
  positivity

/-- The tilted spectral sum is the binomial generating function on a `k`-subset. -/
private theorem spectralMass_tilt_sum (n k : ℕ) (hk : k ≤ n) (r : ℝ) :
    (∑ s : BitStr n, spectralMass n k s * tilt r s) =
      ((1 + Real.exp r) / 2) ^ k := by
  classical
  have hc : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  simp only [spectralMass, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hinner (T : Finset (Fin n)) :
      (∑ s : BitStr n, (if supported T s then (1 : ℝ) else 0) * tilt r s) =
        (1 + Real.exp r) ^ T.card := by
    simpa only [ite_mul, one_mul, zero_mul] using supported_tilt_sum T r
  simp_rw [hinner]
  have heq : (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (1 + Real.exp r) ^ T.card) = (Nat.choose n k : ℝ) * (1 + Real.exp r) ^ k := by
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2])]
    simp [Finset.card_powersetCard, nsmul_eq_mul]
  rw [heq, div_pow]
  field_simp

private theorem restricted_kernel_sum {n : ℕ} (T : Finset (Fin n))
    (x y : BitStr n) :
    (∑ s : BitStr n, if supported T s then walshKernel x s * walshKernel y s else 0) =
      if T ⊆ agreeSet x y then (2 : ℝ) ^ T.card else 0 := by
  have h := supported_sum_prod T (fun i b =>
    (if x i && b then (-1 : ℝ) else 1) * (if y i && b then (-1 : ℝ) else 1))
  simp only [Finset.prod_mul_distrib] at h
  change (∑ s : BitStr n, if supported T s then walshKernel x s * walshKernel y s
    else 0) = _ at h
  rw [h]
  have hprod : (∏ i : Fin n,
      ((if x i && false then (-1 : ℝ) else 1) *
        (if y i && false then (-1 : ℝ) else 1) +
        if i ∈ T then (if x i && true then (-1 : ℝ) else 1) *
          (if y i && true then (-1 : ℝ) else 1) else 0)) =
      ∏ i : Fin n, if i ∈ T then (if x i = y i then (2 : ℝ) else 0) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ T <;> cases hx : x i <;> cases hy : y i <;> norm_num [hi, hx, hy]
  rw [hprod, Fintype.prod_ite_mem]
  by_cases hT : T ⊆ agreeSet x y
  · simp only [hT, ite_true]
    rw [Finset.prod_eq_pow_card]
    intro i hi
    simp [(Finset.mem_filter.mp (hT hi)).2]
  · simp only [hT, ite_false]
    obtain ⟨i, hi, hxy⟩ : ∃ i ∈ T, x i ≠ y i := by
      simpa [Finset.subset_iff, agreeSet] using hT
    exact Finset.prod_eq_zero hi (by simp [hxy])

private theorem gram_character_sum {n k : ℕ} (hk : k ≤ n) (x y : BitStr n) :
    (∑ s : BitStr n, walshKernel x s * spectralMass n k s * walshKernel y s) =
      gramEntry n k (hammingDist x y) := by
  have hc : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have htwo : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hterm (s : BitStr n) :
      walshKernel x s * spectralMass n k s * walshKernel y s =
        (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if supported T s then walshKernel x s * walshKernel y s else 0) /
            ((Nat.choose n k : ℝ) * 2 ^ k) := by
    unfold spectralMass
    rw [← mul_div_assoc, div_mul_eq_mul_div, Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro T _
    split <;> simp_all
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [restricted_kernel_sum]
  have hsum : (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      if T ⊆ agreeSet x y then (2 : ℝ) ^ T.card else 0) =
      (Nat.choose (agreeSet x y).card k : ℝ) * 2 ^ k := by
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.mp hT).2]),
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact_mod_cast card_filter_powersetCard_subset (agreeSet x y)
  rw [hsum, card_agreeSet, gramEntry]
  field_simp

private def walsh (n : ℕ) : Matrix (BitStr n) (BitStr n) ℂ :=
  fun x s => ((walshKernel x s / Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ)

private theorem walsh_star (n : ℕ) : (walsh n)ᴴ = walsh n := by
  ext x y
  simp [Matrix.conjTranspose_apply, walsh, walshKernel_comm]

private theorem walsh_square (n : ℕ) : walsh n * walsh n = 1 := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  ext x y
  rw [Matrix.mul_apply]
  have hterm (s : BitStr n) :
      walsh n x s * walsh n s y =
        ((walshKernel x s * walshKernel y s / (2 : ℝ) ^ n : ℝ) : ℂ) := by
    simp only [walsh, ← Complex.ofReal_mul, div_mul_div_comm, walshKernel_comm s y,
      Real.mul_self_sqrt hN.le]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, walsh_orthogonality]
  by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy, hN.ne']

private def walshUnitary (n : ℕ) : Matrix.unitaryGroup (BitStr n) ℂ :=
  ⟨walsh n, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, walsh_star]
    exact walsh_square n⟩

/-- Walsh diagonalization of the actual ensemble Gram matrix. -/
private theorem gram_diagonalization {n k : ℕ} (hk : k ≤ n) :
    gramMat n k = (HermitianMat.diagonal ℂ
      (fun s => (2 : ℝ) ^ n * spectralMass n k s)).conj (walshUnitary n).val := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  apply HermitianMat.ext
  ext x y
  rw [HermitianMat.conj_apply_mat, HermitianMat.diagonal, HermitianMat.mat_mk]
  change (gramMat n k).mat x y =
    (walsh n * Matrix.diagonal (fun s => (((2 : ℝ) ^ n * spectralMass n k s : ℝ) : ℂ)) *
      (walsh n)ᴴ) x y
  rw [walsh_star, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have hterm (s : BitStr n) :
      (walsh n x s * (((2 : ℝ) ^ n * spectralMass n k s : ℝ) : ℂ)) * walsh n s y =
        ((walshKernel x s * spectralMass n k s * walshKernel y s : ℝ) : ℂ) := by
    simp only [walsh, ← Complex.ofReal_mul, walshKernel_comm s y]
    congr 1
    have hn := (Real.sqrt_pos.mpr hN).ne'
    field_simp [hn]
    rw [Real.sq_sqrt hN.le]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, gram_character_sum hk, gramMat_mat, hammingDist_comm]

private theorem kernel_square {n : ℕ} (x s : BitStr n) :
    walshKernel x s * walshKernel s x = 1 := by
  rw [walshKernel_comm s x]
  unfold walshKernel
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> cases s i <;> norm_num

/-- Functional calculus gives the PSD square root in the Walsh basis. -/
private theorem sqrt_gram_diagonal {n k : ℕ} (hk : k ≤ n) (x : BitStr n) :
    (gramMat n k).sqrt.mat x x =
      (((∑ s : BitStr n, Real.sqrt (spectralMass n k s)) /
        Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hn := (Real.sqrt_pos.mpr hN).ne'
  rw [gram_diagonalization hk, HermitianMat.sqrt, HermitianMat.cfc_conj_unitary,
    HermitianMat.cfc_diagonal, HermitianMat.conj_apply_mat]
  change (walsh n * Matrix.diagonal
    (fun s => ((Real.sqrt ((2 : ℝ) ^ n * spectralMass n k s) : ℝ) : ℂ)) *
      (walsh n)ᴴ) x x = _
  rw [walsh_star, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have hterm (s : BitStr n) :
      (walsh n x s * ((Real.sqrt ((2 : ℝ) ^ n * spectralMass n k s) : ℝ) : ℂ)) *
        walsh n s x = ((Real.sqrt (spectralMass n k s) /
          Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ) := by
    simp only [walsh, ← Complex.ofReal_mul, Real.sqrt_mul hN.le]
    congr 1
    calc
      (walshKernel x s / Real.sqrt ((2 : ℝ) ^ n) *
        (Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt (spectralMass n k s))) *
          (walshKernel s x / Real.sqrt ((2 : ℝ) ^ n)) =
        (walshKernel x s * walshKernel s x) *
          (Real.sqrt (spectralMass n k s) / Real.sqrt ((2 : ℝ) ^ n)) := by
            field_simp [hn]
      _ = _ := by rw [kernel_square, one_mul]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, ← Finset.sum_div]

private theorem pgm_diagonal_formula {n k : ℕ} (hk : k ≤ n) (x : BitStr n) :
    pgmProb n k x x =
      (∑ s : BitStr n, Real.sqrt (spectralMass n k s)) ^ 2 / (2 : ℝ) ^ n := by
  rw [pgmProb, sqrt_gram_diagonal hk]
  simp [Complex.normSq_apply, ← pow_two,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 ^ n by positivity)]

private theorem tilt_sq {n : ℕ} (r : ℝ) (s : BitStr n) :
    tilt r s ^ 2 = tilt (2 * r) s := by
  rw [two_mul, tilt_add, pow_two]

private theorem pgm_tilt_bound {n k : ℕ} (hk : k ≤ n) (x : BitStr n) (t : ℝ) :
    pgmProb n k x x ≤
      (1 + Real.exp (-2 * t)) ^ n * ((1 + Real.exp (2 * t)) / 2) ^ k /
        (2 : ℝ) ^ n := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun s : BitStr n => Real.sqrt (spectralMass n k s) * tilt t s)
    (g := fun s : BitStr n => tilt (-t) s)
  have hcancel (s : BitStr n) :
      (Real.sqrt (spectralMass n k s) * tilt t s) * tilt (-t) s =
        Real.sqrt (spectralMass n k s) := by
    rw [mul_assoc, ← tilt_add, add_neg_cancel, tilt_zero, mul_one]
  have hsquare (s : BitStr n) :
      (Real.sqrt (spectralMass n k s) * tilt t s) ^ 2 =
        spectralMass n k s * tilt (2 * t) s := by
    rw [mul_pow, Real.sq_sqrt (spectralMass_nonneg n k s), tilt_sq]
  simp_rw [hcancel, hsquare, tilt_sq] at hcs
  rw [spectralMass_tilt_sum n k hk, tilt_sum] at hcs
  rw [pgm_diagonal_formula hk]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [mul_neg, neg_mul, mul_comm] using hcs

private theorem tilted_binomial_eq (n k : ℕ) (t : ℝ) :
    (1 + Real.exp (-2 * t)) ^ n * ((1 + Real.exp (2 * t)) / 2) ^ k /
        (2 : ℝ) ^ n =
      Real.exp (-((n : ℝ) - k) * t) * Real.cosh t ^ (n + k) := by
  have hm : (1 + Real.exp (-2 * t)) / 2 = Real.exp (-t) * Real.cosh t := by
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, show -t + -t = -2 * t by ring]
  have hp : (1 + Real.exp (2 * t)) / 2 = Real.exp t * Real.cosh t := by
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, show t + t = 2 * t by ring, add_comm]
  rw [mul_div_right_comm, ← div_pow, hm, hp, mul_pow, mul_pow]
  calc
    (Real.exp (-t) ^ n * Real.cosh t ^ n) *
        (Real.exp t ^ k * Real.cosh t ^ k) =
      (Real.exp (-t) ^ n * Real.exp t ^ k) * Real.cosh t ^ (n + k) := by
        rw [pow_add]
        ring
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      ring

private theorem pgm_exponential_bound {n k : ℕ} (hk : k ≤ n)
    (x : BitStr n) (t : ℝ) :
    pgmProb n k x x ≤
      Real.exp (-((n : ℝ) - k) * t + ((n : ℝ) + k) * (t ^ 2 / 2)) := by
  calc
    pgmProb n k x x ≤
      Real.exp (-((n : ℝ) - k) * t) * Real.cosh t ^ (n + k) := by
        simpa only [tilted_binomial_eq] using pgm_tilt_bound hk x t
    _ ≤ Real.exp (-((n : ℝ) - k) * t) * Real.exp (t ^ 2 / 2) ^ (n + k) := by
      gcongr
      exact Real.cosh_le_exp_half_sq t
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_add]

/-- Lemma 9: for `1 ≤ n`, `0 ≤ a`, `k ≤ n`, and `n - k = a √n`, the PGM diagonal
probability `pgmProb n k x x` is at most `4 exp(-a^2 / 32)`. -/
theorem lemma9_gram_diagonal_upper :
    ∀ (n k : ℕ) (a : ℝ) (x : BitStr n),
      1 ≤ n → 0 ≤ a → k ≤ n →
      (n : ℝ) - (k : ℝ) = a * Real.sqrt (n : ℝ) →
      pgmProb n k x x ≤ 4 * Real.exp (-(a ^ 2) / 32) := by
  intro n k a x hn ha hk hgap
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hnpos.le
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hbound := pgm_exponential_bound hk x (a / (2 * Real.sqrt (n : ℝ)))
  have he : -((n : ℝ) - k) * (a / (2 * Real.sqrt (n : ℝ))) +
      ((n : ℝ) + k) * ((a / (2 * Real.sqrt (n : ℝ))) ^ 2 / 2) ≤ -(a ^ 2) / 4 := by
    rw [hgap]
    have heq : -(a * Real.sqrt (n : ℝ)) * (a / (2 * Real.sqrt (n : ℝ))) =
        -(a ^ 2) / 2 := by field_simp
    rw [heq]
    have hle : ((n : ℝ) + k) * ((a / (2 * Real.sqrt (n : ℝ))) ^ 2 / 2) ≤
        (2 * n) * ((a / (2 * Real.sqrt (n : ℝ))) ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hval : (2 * (n : ℝ)) * ((a / (2 * Real.sqrt (n : ℝ))) ^ 2 / 2) =
        a ^ 2 / 4 := by
      field_simp
      nlinarith [hs]
    rw [hval] at hle
    linarith
  calc
    pgmProb n k x x ≤ Real.exp (-(a ^ 2) / 4) :=
      hbound.trans (Real.exp_le_exp.mpr he)
    _ ≤ Real.exp (-(a ^ 2) / 32) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg a]
    _ ≤ 4 * Real.exp (-(a ^ 2) / 32) := by
      nlinarith [Real.exp_pos (-(a ^ 2) / 32), ha]

/-- The upper bound `4 exp(-a^2 / 32)` of Lemma 9 never exceeds `4`. -/
theorem lemma9_bound_le_four (a : ℝ) (_ha : 0 ≤ a) :
    4 * Real.exp (-(a ^ 2) / 32) ≤ 4 := by
  have hsq : 0 ≤ a ^ 2 := sq_nonneg a
  have hle : Real.exp (-(a ^ 2) / 32) ≤ Real.exp 0 := by
    apply Real.exp_le_exp.mpr
    linarith
  simpa using mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 4)

end Qatlib.Papers.WildcardSrch12.MainResults.GramDiagonalUpper
