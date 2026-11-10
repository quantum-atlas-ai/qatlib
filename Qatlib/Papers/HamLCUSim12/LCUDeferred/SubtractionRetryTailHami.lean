/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.SubtractionRetryTailStat
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.HamLCUSim12.LCUDeferred

open scoped BigOperators

private theorem retry_born (m : ℕ) (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hhalf : ∀ i, p i ≤ 1 / 2) (z : Fin m → Bool) :
    BornProb (retryState m p) z = ∏ i, if z i then p i else 1 - p i := by
  simp only [BornProb, retryState, norm_prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt]
  cases z i <;> simp <;> linarith [hp i, hhalf i]

private theorem retry_weighted_sum (m : ℕ) (p : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hhalf : ∀ i, p i ≤ 1 / 2) :
    (∑ z : Fin m → Bool,
      (2 : ℝ) ^ (Finset.univ.filter fun i : Fin m => z i).card *
        BornProb (retryState m p) z) = ∏ i, (1 + p i) := by
  have hweight (z : Fin m → Bool) :
      (2 : ℝ) ^ (Finset.univ.filter fun i : Fin m => z i).card *
        BornProb (retryState m p) z =
          ∏ i, if z i then 2 * p i else 1 - p i := by
    have hc : (∏ i : Fin m, if z i then (2 : ℝ) else 1) =
        2 ^ (Finset.univ.filter fun i : Fin m => z i).card := by
      rw [← Finset.prod_filter]
      simp
    rw [retry_born m p hp hhalf z, ← hc, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    cases z i <;> simp
  simp_rw [hweight]
  rw [← Fintype.prod_sum (fun (i : Fin m) (b : Bool) => if b then 2 * p i else 1 - p i)]
  apply Finset.prod_congr rfl
  intro i _hi
  simp
  ring

private theorem retry_rational_tail (r : ℕ) (p : Fin (3 * r) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hhalf : ∀ i, p i ≤ 1 / 2) :
    MeasureProb (retryState (3 * r) p) (retryExhausted r) ≤
      (1 / 2 : ℝ) * (27 / 32 : ℝ)^r := by
  let S := retryExhausted r
  have hborn (z : Fin (3 * r) → Bool) : 0 ≤ BornProb (retryState (3 * r) p) z := by
    unfold BornProb
    positivity
  have hm : (2 : ℝ)^(2 * r + 1) * MeasureProb (retryState (3 * r) p) S ≤
      ∏ i : Fin (3 * r), (1 + p i) := by
    calc
      _ = ∑ z ∈ S, (2 : ℝ)^(2 * r + 1) * BornProb (retryState (3 * r) p) z := by
        simp [MeasureProb, Finset.mul_sum]
      _ ≤ ∑ z ∈ S,
          (2 : ℝ)^(Finset.univ.filter fun i : Fin (3 * r) => z i).card *
            BornProb (retryState (3 * r) p) z := by
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_right _ (hborn z)
        apply pow_le_pow_right₀ (by norm_num)
        exact (Finset.mem_filter.mp hz).2
      _ ≤ ∑ z : Fin (3 * r) → Bool,
          (2 : ℝ)^(Finset.univ.filter fun i : Fin (3 * r) => z i).card *
            BornProb (retryState (3 * r) p) z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro z _hz _hnz
        exact mul_nonneg (by positivity) (hborn z)
      _ = _ := retry_weighted_sum (3 * r) p hp hhalf
  have hprod : (∏ i : Fin (3 * r), (1 + p i)) ≤ (3 / 2 : ℝ)^(3 * r) := by
    calc
      _ ≤ ∏ _i : Fin (3 * r), (3 / 2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i _hi
          linarith [hp i]
        · intro i _hi
          linarith [hhalf i]
      _ = _ := by simp [div_pow]
  have hscale : (2 : ℝ)^(2 * r + 1) * ((1 / 2 : ℝ) * (27 / 32 : ℝ)^r) =
      (3 / 2 : ℝ)^(3 * r) := by
    simp only [pow_add, pow_mul, pow_one]
    calc
      _ = ((2 : ℝ)^2 * (27 / 32))^r := by rw [mul_pow]; ring
      _ = ((3 / 2 : ℝ)^3)^r := by congr 1; norm_num
  have hcompare : (2 : ℝ)^(2 * r + 1) * MeasureProb (retryState (3 * r) p) S ≤
      (2 : ℝ)^(2 * r + 1) * ((1 / 2 : ℝ) * (27 / 32 : ℝ)^r) := by
    rw [hscale]
    exact hm.trans hprod
  exact le_of_mul_le_mul_left hcompare (by positivity)

theorem subtractionRetryTail : SubtractionRetryTail := by
  intro r _hr p hp hhalf
  have he : Real.exp (1 / 14) ≤ (14 / 13 : ℝ) := by
    convert Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 14) (by norm_num : (1 / 14 : ℝ) < 1) using 1
    norm_num
  have hb : (27 / 32 : ℝ) ≤ Real.exp (-(1 : ℝ) / 14) := by
    rw [show -(1 : ℝ) / 14 = -(1 / 14) by ring, Real.exp_neg]
    rw [← one_div]
    apply (le_div_iff₀ (Real.exp_pos (1 / 14))).2
    calc
      (27 / 32 : ℝ) * Real.exp (1 / 14) ≤ (27 / 32) * (14 / 13) := by gcongr
      _ ≤ 1 := by norm_num
  calc
    _ ≤ (1 / 2 : ℝ) * (27 / 32 : ℝ)^r := retry_rational_tail r p hp hhalf
    _ ≤ (27 / 32 : ℝ)^r := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 32) r]
    _ ≤ (Real.exp (-(1 : ℝ) / 14))^r := pow_le_pow_left₀ (by norm_num) hb r
    _ = Real.exp (-(r : ℝ) / 14) := by rw [← Real.exp_nat_mul]; congr 1; ring

end Qatlib.Papers.HamLCUSim12.LCUDeferred
