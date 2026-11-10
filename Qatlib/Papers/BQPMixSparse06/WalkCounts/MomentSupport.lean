/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Lemma1FunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.WalkCounts

open Finset

def spectralMoment {ι : Type*} [Fintype ι] (p lam : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ l, p l * lam l ^ n

theorem spectralMoment_even_nonneg {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (n : ℕ) : 0 ≤ spectralMoment p lam (2 * n) := by
  unfold spectralMoment
  have h : ∀ l : ι, p l * lam l ^ (2 * n) = p l * (lam l ^ 2) ^ n := by
    intro l
    rw [pow_mul]
  simp only [h]
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (pow_nonneg (sq_nonneg (lam l)) n)

theorem spectralMoment_even_ge {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (j : ι) (k : ℕ) :
    p j * (lam j ^ 2) ^ k ≤ spectralMoment p lam (2 * k) := by
  unfold spectralMoment
  have h : ∀ l : ι, p l * lam l ^ (2 * k) = p l * (lam l ^ 2) ^ k := by
    intro l
    rw [pow_mul]
  simp only [h]
  exact Finset.single_le_sum
    (fun l _ => mul_nonneg (hp l) (pow_nonneg (sq_nonneg (lam l)) k))
    (Finset.mem_univ j)

theorem moment_le_of_supp {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (hmass : ∑ l, p l = 1) (b : ℝ)
    (hb : ∀ l, 0 < p l → |lam l| ≤ b) (n : ℕ) :
    |spectralMoment p lam n| ≤ b ^ n := by
  unfold spectralMoment
  calc |∑ l, p l * lam l ^ n| ≤ ∑ l, |p l * lam l ^ n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, p l * |lam l| ^ n := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hp l), abs_pow]
    _ ≤ ∑ l, p l * b ^ n := by
        refine Finset.sum_le_sum fun l _ => ?_
        rcases lt_or_eq_of_le (hp l) with hl | hl
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg (lam l)) (hb l hl) n) (le_of_lt hl)
        · rw [← hl]
          simp
    _ = (∑ l, p l) * b ^ n := by rw [Finset.sum_mul]
    _ = b ^ n := by rw [hmass, one_mul]

theorem moment_growth_supp {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (b : ℝ) (hb : 0 ≤ b)
    (hΔ : ∀ n, |spectralMoment p lam n| ≤ b ^ n) :
    ∀ j, 0 < p j → |lam j| ≤ b := by
  intro j hj
  rcases lt_or_eq_of_le hb with hbpos | hbzero
  · by_contra hcon
    rw [not_le] at hcon
    have hsq : b ^ 2 < lam j ^ 2 := by
      have hbb : b ^ 2 < |lam j| ^ 2 := by
        have h0 : 0 < b := hbpos
        nlinarith [abs_nonneg (lam j), sq_abs (lam j), hcon]
      rwa [sq_abs] at hbb
    have hb2 : 0 < b ^ 2 := by positivity
    have hr : 1 < lam j ^ 2 / b ^ 2 :=
      (one_lt_div hb2).mpr hsq
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (p j)⁻¹ hr
    have hge := spectralMoment_even_ge p lam hp j k
    have hbnd := hΔ (2 * k)
    have hbpow : b ^ (2 * k) = (b ^ 2) ^ k := by rw [pow_mul]
    rw [hbpow] at hbnd
    have hle : p j * (lam j ^ 2) ^ k ≤ (b ^ 2) ^ k :=
      le_trans hge (le_trans (le_abs_self _) hbnd)
    have hb2k : 0 < (b ^ 2) ^ k := pow_pos hb2 k
    have hdiv : (lam j ^ 2) ^ k / (b ^ 2) ^ k ≤ (p j)⁻¹ := by
      have hle' : (lam j ^ 2) ^ k * p j ≤ (b ^ 2) ^ k := by
        simpa [mul_comm] using hle
      have h1 : (lam j ^ 2) ^ k ≤ (b ^ 2) ^ k / p j :=
        (le_div_iff₀ hj).mpr hle'
      have h2 : (lam j ^ 2) ^ k ≤ (p j)⁻¹ * (b ^ 2) ^ k := by
        simpa [div_eq_inv_mul] using h1
      rw [div_le_iff₀ hb2k]
      simpa [mul_comm] using h2
    have hratio : (lam j ^ 2 / b ^ 2) ^ k = (lam j ^ 2) ^ k / (b ^ 2) ^ k :=
      div_pow _ _ _
    rw [hratio] at hk
    linarith
  · subst hbzero
    have hzero : spectralMoment p lam (2 * 1) = 0 := by
      have h1 := hΔ (2 * 1)
      have h2 : (0 : ℝ) ^ (2 * 1) = 0 := by norm_num
      rw [h2] at h1
      have habs : |spectralMoment p lam (2 * 1)| = 0 :=
        le_antisymm h1 (abs_nonneg _)
      exact abs_eq_zero.mp habs
    have hge := spectralMoment_even_ge p lam hp j 1
    rw [hzero] at hge
    have hsq : lam j ^ 2 = 0 := by
      have h1 : p j * (lam j ^ 2) ≤ 0 := by simpa [pow_one] using hge
      have hprod : p j * (lam j ^ 2) = 0 := by
        simpa using le_antisymm h1 (mul_nonneg (le_of_lt hj) (sq_nonneg (lam j)))
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hj)
    have hlam : lam j = 0 := by
      have := sq_nonneg (lam j)
      nlinarith
    rw [hlam, abs_zero]

theorem moment_growth_iff_supp {ι : Type*} [Fintype ι] (p lam : ι → ℝ)
    (hp : ∀ l, 0 ≤ p l) (hmass : ∑ l, p l = 1) (b : ℝ) (hb : 0 ≤ b) :
    (∀ n, |spectralMoment p lam n| ≤ b ^ n) ↔
      ∀ j, 0 < p j → |lam j| ≤ b :=
  ⟨moment_growth_supp p lam hp b hb, fun hsupp n => moment_le_of_supp p lam hp hmass b hsupp n⟩

theorem pow_abs_le_of_abs_le {x c : ℝ} (_hc : 0 ≤ c) (hx : |x| ≤ c) (m : ℕ) :
    |x ^ m| ≤ c ^ m := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) hx m

theorem pow_abs_sub_pow_le {x y c : ℝ} (_hc : 0 ≤ c) (hx : |x| ≤ c)
    (hy : |y| ≤ c) (m : ℕ) :
    |x ^ m - y ^ m| ≤ (m : ℝ) * c ^ (m - 1) * |x - y| := by
  have hmain := abs_pow_sub_pow_le x y m
  have hmax : max |x| |y| ≤ c := max_le hx hy
  have hmaxnn : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
  have hpow : max |x| |y| ^ (m - 1) ≤ c ^ (m - 1) :=
    pow_le_pow_left₀ hmaxnn hmax (m - 1)
  have hstep : |x - y| * (m : ℝ) * max |x| |y| ^ (m - 1) ≤
      |x - y| * (m : ℝ) * c ^ (m - 1) := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    calc |x - y| * (m : ℝ) * max |x| |y| ^ (m - 1)
        = (|x - y| * (m : ℝ)) * max |x| |y| ^ (m - 1) := by ring
      _ ≤ (|x - y| * (m : ℝ)) * c ^ (m - 1) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) hm)
      _ = |x - y| * (m : ℝ) * c ^ (m - 1) := by ring
  calc |x ^ m - y ^ m|
      ≤ |x - y| * (m : ℝ) * max |x| |y| ^ (m - 1) := hmain
    _ ≤ |x - y| * (m : ℝ) * c ^ (m - 1) := hstep
    _ = (m : ℝ) * c ^ (m - 1) * |x - y| := by ring

theorem abs_min_sub_min_le_abs (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  have h : LipschitzWith 1 (fun x : ℝ => min x c) := LipschitzWith.id.min_const c
  have hd := h.dist_le_mul a b
  simpa [Real.dist_eq] using hd

theorem abs_clamp_sub_clamp_le {lo hi : ℝ} (x y : ℝ) :
    |Qatlib.Papers.BQPMixSparse06.MainResults.clamp lo hi x -
        Qatlib.Papers.BQPMixSparse06.MainResults.clamp lo hi y| ≤
      |x - y| := by
  have h : LipschitzWith 1
      (fun x : ℝ => max lo (min hi x)) :=
    (LipschitzWith.id.const_min hi).const_max lo
  have hd := h.dist_le_mul x y
  simpa [Real.dist_eq, Qatlib.Papers.BQPMixSparse06.MainResults.clamp]
    using hd

end Qatlib.Papers.BQPMixSparse06.WalkCounts
