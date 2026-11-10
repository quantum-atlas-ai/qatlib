/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth

open Polynomial Finset
open scoped BigOperators

theorem factorial_mul_factorial_le (d k : ℕ) (hk : k < d) :
    (k + 1).factorial * (d - k).factorial ≤ d.factorial := by
  induction d generalizing k with
  | zero => omega
  | succ n ih =>
    have hkn : k ≤ n := by omega
    rcases Nat.lt_or_eq_of_le hkn with h | h
    · have hrec := ih k h
      have he : n + 1 - k = (n - k) + 1 := by omega
      rw [he, Nat.factorial_succ, Nat.factorial_succ n]
      have hle : n - k + 1 ≤ n + 1 := by omega
      calc (k + 1).factorial * ((n - k + 1) * (n - k).factorial)
          = (n - k + 1) * ((k + 1).factorial * (n - k).factorial) := by ring
        _ ≤ (n + 1) * n.factorial := Nat.mul_le_mul hle hrec
    · rw [h, show n + 1 - n = 1 by omega]
      simp

theorem prod_node_sub (d i : ℕ) (hi : i ≤ d) :
    ∏ j ∈ (Finset.range (d + 1)).erase i, ((i : ℝ) - (j : ℝ))
      = (i.factorial : ℝ) * (-1 : ℝ) ^ (d - i) * ((d - i).factorial : ℝ) := by
  have hset : (Finset.range (d + 1)).erase i
      = Finset.range i ∪ Finset.Ico (i + 1) (d + 1) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range i) (Finset.Ico (i + 1) (d + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2
    omega
  rw [hset, Finset.prod_union hdisj]
  have hleft : ∏ j ∈ Finset.range i, ((i : ℝ) - (j : ℝ)) = (i.factorial : ℝ) := by
    have h1 : ((i.descFactorial i : ℕ) : ℝ) = ∏ j ∈ Finset.range i, ((i - j : ℕ) : ℝ) := by
      rw [Nat.descFactorial_eq_prod_range]
      push_cast
      rfl
    have h2 : (∏ j ∈ Finset.range i, ((i : ℝ) - (j : ℝ)))
        = ∏ j ∈ Finset.range i, ((i - j : ℕ) : ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.cast_sub (by omega : j ≤ i)]
    rw [h2, ← h1, Nat.descFactorial_self]
  have hright : ∏ j ∈ Finset.Ico (i + 1) (d + 1), ((i : ℝ) - (j : ℝ))
      = (-1 : ℝ) ^ (d - i) * ((d - i).factorial : ℝ) := by
    rw [Finset.prod_Ico_eq_prod_range (fun j => ((i : ℝ) - (j : ℝ))) (i + 1) (d + 1)]
    have hsub : d + 1 - (i + 1) = d - i := by omega
    rw [hsub]
    have hterm : ∀ k ∈ Finset.range (d - i),
        ((i : ℝ) - (((i + 1 + k : ℕ)) : ℝ)) = -((k + 1 : ℕ) : ℝ) := by
      intro k _
      push_cast
      ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_neg]
    congr 1
    · rw [Finset.card_range]
    · rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  rw [mul_assoc, hleft, hright]

def lagrangeCardinal (m d i : ℕ) : Polynomial ℝ :=
  Polynomial.C ((((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ * (-1 : ℝ) ^ (d - i)) *
    ∏ j ∈ (Finset.range (d + 1)).erase i,
      (Polynomial.X - Polynomial.C (((m + j : ℕ) : ℝ)))

theorem lagrangeCardinal_eval_node (m d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) :
    (lagrangeCardinal m d i).eval (((m + k : ℕ) : ℝ))
      = if i = k then 1 else 0 := by
  simp only [lagrangeCardinal, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  have hprod : ∏ j ∈ (Finset.range (d + 1)).erase i,
      (((m + k : ℕ) : ℝ) - ((m + j : ℕ) : ℝ))
      = ∏ j ∈ (Finset.range (d + 1)).erase i, ((k : ℝ) - (j : ℝ)) := by
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [hprod]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, prod_node_sub d i hi]
    set B : ℝ := (-1 : ℝ) ^ (d - i) with hB
    have hB2 : B * B = 1 := by
      rw [hB, ← pow_add]
      rw [show (d - i) + (d - i) = 2 * (d - i) by ring, pow_mul]
      norm_num
    have hCpos : (0 : ℝ) < (i.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos i
    have hDpos : (0 : ℝ) < ((d - i).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (d - i)
    have hCD : ((i.factorial : ℝ) * ((d - i).factorial : ℝ)) ≠ 0 :=
      (mul_pos hCpos hDpos).ne'
    have hc : (((i.factorial * (d - i).factorial : ℕ) : ℝ))
        = (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by push_cast; ring
    rw [hc]
    calc (((i.factorial : ℝ) * ((d - i).factorial : ℝ))⁻¹ * B) *
          ((i.factorial : ℝ) * B * ((d - i).factorial : ℝ))
        = (((i.factorial : ℝ) * ((d - i).factorial : ℝ))⁻¹ *
            ((i.factorial : ℝ) * ((d - i).factorial : ℝ))) * (B * B) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hCD, hB2, mul_one]
  · rw [if_neg hik]
    have hkmem : k ∈ (Finset.range (d + 1)).erase i := by
      rw [Finset.mem_erase, Finset.mem_range]
      exact ⟨Ne.symm hik, by omega⟩
    have hz : ∏ j ∈ (Finset.range (d + 1)).erase i, ((k : ℝ) - (j : ℝ)) = 0 := by
      apply Finset.prod_eq_zero hkmem
      simp
    rw [hz, mul_zero]

theorem natDegree_lagrangeCardinal (m d i : ℕ) (hi : i ≤ d) :
    (lagrangeCardinal m d i).natDegree ≤ d := by
  have hprod : (∏ j ∈ (Finset.range (d + 1)).erase i,
      (Polynomial.X - Polynomial.C (((m + j : ℕ) : ℝ)))).natDegree ≤ d := by
    refine le_trans (Polynomial.natDegree_prod_le (s := (Finset.range (d + 1)).erase i)
      (f := fun j => (Polynomial.X - Polynomial.C (((m + j : ℕ) : ℝ))))) ?_
    have h1 : ∀ j ∈ (Finset.range (d + 1)).erase i,
        (Polynomial.X - Polynomial.C (((m + j : ℕ) : ℝ))).natDegree ≤ 1 := by
      intro j _; rw [Polynomial.natDegree_X_sub_C]
    have hsum : (∑ j ∈ (Finset.range (d + 1)).erase i,
        (Polynomial.X - Polynomial.C (((m + j : ℕ) : ℝ))).natDegree)
        ≤ ∑ _j ∈ (Finset.range (d + 1)).erase i, 1 := Finset.sum_le_sum h1
    have hcard : ((Finset.range (d + 1)).erase i).card ≤ d := by
      rw [Finset.card_erase_of_mem]
      · simp
      · rw [Finset.mem_range]; omega
    calc (∑ j ∈ (Finset.range (d + 1)).erase i,
          (Polynomial.X - Polynomial.C (((m + j : ℕ) : ℝ))).natDegree)
        ≤ ∑ _j ∈ (Finset.range (d + 1)).erase i, 1 := hsum
      _ = ((Finset.range (d + 1)).erase i).card := by simp
      _ ≤ d := hcard
  unfold lagrangeCardinal
  refine Polynomial.natDegree_mul_le.trans ?_
  have hc : (Polynomial.C
      ((((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ * (-1 : ℝ) ^ (d - i))).natDegree = 0 :=
    Polynomial.natDegree_C _
  omega

theorem prod_abs_sub_le_factorial (d i : ℕ) (hi : i ≤ d) {y : ℝ}
    (hy0 : 0 ≤ y) (hyd : y ≤ (d : ℝ)) :
    ∏ j ∈ (Finset.range (d + 1)).erase i, |y - (j : ℝ)| ≤ (d.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    have hi0 : i = 0 := by omega
    subst hi0
    simp
  set k : ℕ := min ⌊y⌋₊ (d - 1) with hk
  have hk_le : k ≤ d - 1 := by rw [hk]; exact Nat.min_le_right _ _
  have hk_y : (k : ℝ) ≤ y := by
    rw [hk]
    rcases le_or_gt (⌊y⌋₊) (d - 1) with h | h
    · rw [min_eq_left h]; exact Nat.floor_le hy0
    · have hd' : d ≤ ⌊y⌋₊ := by omega
      have hdR : ((d : ℕ) : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hd'
      have hyle : ((d : ℕ) : ℝ) ≤ y := hdR.trans (Nat.floor_le hy0)
      rw [min_eq_right (le_of_lt h)]
      have h1 : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast Nat.sub_le d 1
      exact le_trans h1 hyle
  have hk_y1 : y ≤ (k : ℝ) + 1 := by
    rw [hk]
    rcases le_or_gt (⌊y⌋₊) (d - 1) with h | h
    · rw [min_eq_left h]; exact le_of_lt (Nat.lt_floor_add_one y)
    · have hd' : d ≤ ⌊y⌋₊ := by omega
      have hdR : ((d : ℕ) : ℝ) ≤ ((⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hd'
      have hyle : ((d : ℕ) : ℝ) ≤ y := hdR.trans (Nat.floor_le hy0)
      have hyeq : y = (d : ℝ) := le_antisymm hyd hyle
      rw [min_eq_right (le_of_lt h), hyeq]
      have h1 : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring
      rw [h1]

  set b : ℕ → ℝ := fun j => if j ≤ k then ((k + 1 - j : ℕ) : ℝ) else ((j - k : ℕ) : ℝ) with hb
  have hb_one : ∀ j, 1 ≤ b j := by
    intro j
    simp only [hb]
    by_cases hj : j ≤ k
    · rw [if_pos hj]
      have : 1 ≤ k + 1 - j := by omega
      exact_mod_cast this
    · rw [if_neg hj]
      push Not at hj
      have : 1 ≤ j - k := by omega
      exact_mod_cast this
  have hterm : ∀ j ∈ (Finset.range (d + 1)).erase i, |y - (j : ℝ)| ≤ b j := by
    intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    simp only [hb]
    by_cases hj' : j ≤ k
    · rw [if_pos hj']
      have h1 : (j : ℝ) ≤ y := le_trans (by exact_mod_cast hj') hk_y
      rw [abs_of_nonneg (by linarith)]
      have h2 : y - (j : ℝ) ≤ (k : ℝ) + 1 - (j : ℝ) := by linarith
      have h3 : ((k + 1 - j : ℕ) : ℝ) = (k : ℝ) + 1 - (j : ℝ) := by
        rw [Nat.cast_sub (by omega : j ≤ k + 1)]; push_cast; ring
      rw [h3]; exact h2
    · rw [if_neg hj']
      push Not at hj'
      have h1 : y ≤ (j : ℝ) := le_trans hk_y1 (by exact_mod_cast hj')
      rw [abs_of_nonpos (by linarith), neg_sub]
      have h2 : (j : ℝ) - y ≤ (j : ℝ) - (k : ℝ) := by linarith
      have h3 : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := by
        rw [Nat.cast_sub (by omega : k ≤ j)]

      rw [h3]; exact h2
  have hsplit : d + 1 = (k + 1) + (d - k) := by omega
  have hbprod : ∏ j ∈ Finset.range (d + 1), b j
      = ((k + 1).factorial : ℝ) * ((d - k).factorial : ℝ) := by
    conv_lhs => rw [hsplit]
    rw [Finset.prod_range_add]
    have h1 : ∏ j ∈ Finset.range (k + 1), b j = ((k + 1).factorial : ℝ) := by
      have hstep : ∀ j ∈ Finset.range (k + 1), b j = ((k + 1 - j : ℕ) : ℝ) := by
        intro j hj
        rw [Finset.mem_range] at hj
        simp only [hb]; exact if_pos (by omega)
      rw [Finset.prod_congr rfl hstep]
      have key : (∏ j ∈ Finset.range (k + 1), (k + 1 - j : ℕ)) = (k + 1).factorial := by
        rw [← Nat.descFactorial_eq_prod_range (k + 1) (k + 1), Nat.descFactorial_self]
      calc (∏ j ∈ Finset.range (k + 1), ((k + 1 - j : ℕ) : ℝ))
          = ((∏ j ∈ Finset.range (k + 1), (k + 1 - j : ℕ) : ℕ) : ℝ) := by push_cast; rfl
        _ = ((k + 1).factorial : ℝ) := by rw [key]
    have h2 : ∏ j ∈ Finset.range (d - k), b (k + 1 + j) = ((d - k).factorial : ℝ) := by
      have hstep : ∀ j ∈ Finset.range (d - k), b (k + 1 + j) = ((j + 1 : ℕ) : ℝ) := by
        intro j hj
        rw [Finset.mem_range] at hj
        simp only [hb]
        rw [if_neg (by omega)]
        congr 1
        omega
      rw [Finset.prod_congr rfl hstep]
      have key : (∏ j ∈ Finset.range (d - k), (j + 1 : ℕ)) = (d - k).factorial :=
        Finset.prod_range_add_one_eq_factorial (d - k)
      calc (∏ j ∈ Finset.range (d - k), ((j + 1 : ℕ) : ℝ))
          = ((∏ j ∈ Finset.range (d - k), (j + 1 : ℕ) : ℕ) : ℝ) := by push_cast; rfl
        _ = ((d - k).factorial : ℝ) := by rw [key]
    rw [h1, h2]
  have hbi : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  calc ∏ j ∈ (Finset.range (d + 1)).erase i, |y - (j : ℝ)|
      ≤ ∏ j ∈ (Finset.range (d + 1)).erase i, b j :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) hterm
    _ ≤ ∏ j ∈ (Finset.range (d + 1)), b j := by
        rw [← Finset.prod_erase_mul (Finset.range (d + 1)) b hbi]
        have hnonneg : 0 ≤ ∏ j ∈ (Finset.range (d + 1)).erase i, b j :=
          Finset.prod_nonneg (fun j _ => le_trans zero_le_one (hb_one j))
        have hb1 : 1 ≤ b i := hb_one i
        calc ∏ j ∈ (Finset.range (d + 1)).erase i, b j
            = (∏ j ∈ (Finset.range (d + 1)).erase i, b j) * 1 := by rw [mul_one]
          _ ≤ (∏ j ∈ (Finset.range (d + 1)).erase i, b j) * b i :=
              mul_le_mul_of_nonneg_left hb1 hnonneg
    _ = ((k + 1).factorial : ℝ) * ((d - k).factorial : ℝ) := hbprod
    _ ≤ (d.factorial : ℝ) := by
        exact_mod_cast factorial_mul_factorial_le d k (by omega)

theorem interpolation_eq (m d : ℕ) {p : Polynomial ℝ} (hdeg : p.natDegree ≤ d) :
    p = ∑ i ∈ Finset.range (d + 1),
        Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i := by
  set I : Polynomial ℝ := ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i with hI
  have hIdeg : I.natDegree ≤ d := by
    rw [hI]
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.range (d + 1))
      (n := d) _ (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    refine Polynomial.natDegree_mul_le.trans ?_
    have hc : (Polynomial.C (p.eval (((m + i : ℕ) : ℝ)))).natDegree = 0 :=
      Polynomial.natDegree_C _
    have hl := natDegree_lagrangeCardinal m d i (by omega)
    omega
  have heval : ∀ y ∈ Finset.image (fun i => (((m + i : ℕ) : ℝ))) (Finset.range (d + 1)),
      Polynomial.eval y p = Polynomial.eval y I := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Finset.mem_range] at hk
    rw [hI, Polynomial.eval_finsetSum]
    have hterm : ∀ i ∈ Finset.range (d + 1),
        (Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i).eval
            (((m + k : ℕ) : ℝ))
          = if i = k then p.eval (((m + i : ℕ) : ℝ)) else 0 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Polynomial.eval_mul, Polynomial.eval_C, lagrangeCardinal_eval_node m d i k
        (by omega) (by omega)]
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik, mul_one]
      · rw [if_neg hik, if_neg hik, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl]
    · intro b _ hbk
      rw [if_neg hbk]
    · intro hknot
      exact absurd (Finset.mem_range.mpr hk) hknot
  have hcard : max p.natDegree I.natDegree <
      (Finset.image (fun i => (((m + i : ℕ) : ℝ))) (Finset.range (d + 1))).card := by
    have hinj : Function.Injective (fun i : ℕ => (((m + i : ℕ) : ℝ))) := by
      intro a b hab
      have : ((m + a : ℕ)) = ((m + b : ℕ)) := Nat.cast_injective hab
      omega
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    omega
  exact Polynomial.eq_of_natDegree_lt_card_of_eval_eq' p I _ heval hcard

theorem block_bound (m d : ℕ) {p : Polynomial ℝ} {c x : ℝ}
    (hdeg : p.natDegree ≤ d) (hc : 0 ≤ c)
    (hgrid : ∀ i : ℕ, i ≤ d → |p.eval (((m + i : ℕ) : ℝ))| ≤ c)
    (hx0 : 0 ≤ x - (m : ℝ)) (hxd : x - (m : ℝ) ≤ (d : ℝ)) :
    |p.eval x| ≤ (2 : ℝ) ^ d * c := by
  conv_lhs => rw [interpolation_eq m d hdeg]
  rw [Polynomial.eval_finsetSum]
  have hterm : ∀ i ∈ Finset.range (d + 1),
      |(Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i).eval x|
        ≤ c * (d.choose i : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
    have hgi : |p.eval (((m + i : ℕ) : ℝ))| ≤ c := hgrid i (by omega)
    have hlag : |(lagrangeCardinal m d i).eval x| ≤ (d.choose i : ℝ) := by
      have hevalx : (lagrangeCardinal m d i).eval x
          = ((((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ * (-1 : ℝ) ^ (d - i)) *
            ∏ j ∈ (Finset.range (d + 1)).erase i, ((x - (m : ℝ)) - (j : ℝ)) := by
        simp only [lagrangeCardinal, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        push_cast
        ring
      rw [hevalx, abs_mul]
      have hCin' : (0 : ℝ) < (((i.factorial * (d - i).factorial : ℕ) : ℝ)) := by
        have hpos : (0 : ℕ) < i.factorial * (d - i).factorial :=
          Nat.mul_pos (Nat.factorial_pos i) (Nat.factorial_pos (d - i))
        exact_mod_cast hpos
      have hcoef : |((((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ *
          (-1 : ℝ) ^ (d - i))| = (((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ := by
        rw [abs_mul, abs_inv, abs_of_pos hCin', abs_pow]
        simp
      rw [hcoef]
      have hprod : |∏ j ∈ (Finset.range (d + 1)).erase i,
          ((x - (m : ℝ)) - (j : ℝ))| ≤ (d.factorial : ℝ) := by
        rw [Finset.abs_prod]
        exact prod_abs_sub_le_factorial d i (by omega) hx0 hxd
      calc (((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ *
            |∏ j ∈ (Finset.range (d + 1)).erase i, ((x - (m : ℝ)) - (j : ℝ))|
          ≤ (((i.factorial * (d - i).factorial : ℕ) : ℝ))⁻¹ * (d.factorial : ℝ) := by
            exact mul_le_mul_of_nonneg_left hprod (le_of_lt (inv_pos.mpr hCin'))
        _ = (d.choose i : ℝ) := by
            rw [Nat.cast_choose ℝ (by omega : i ≤ d)]
            have hc2 : (((i.factorial * (d - i).factorial : ℕ) : ℝ))
                = (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by push_cast; ring
            rw [hc2, inv_mul_eq_div]
    exact mul_le_mul hgi hlag (abs_nonneg _) hc
  have h1 : |∑ i ∈ Finset.range (d + 1),
        (Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i).eval x|
      ≤ ∑ i ∈ Finset.range (d + 1),
          |(Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i).eval x| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ i ∈ Finset.range (d + 1),
          |(Polynomial.C (p.eval (((m + i : ℕ) : ℝ))) * lagrangeCardinal m d i).eval x|)
      ≤ ∑ i ∈ Finset.range (d + 1), c * (d.choose i : ℝ) := Finset.sum_le_sum hterm
  have h3 : (∑ i ∈ Finset.range (d + 1), c * (d.choose i : ℝ)) = c * (2 : ℝ) ^ d := by
    rw [← Finset.mul_sum]
    congr 1
    have h := Nat.sum_range_choose d
    have hcast : (∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ)) = (2 : ℝ) ^ d := by
      rw [← Nat.cast_sum, h]
      push_cast
      norm_num
    rw [hcast]
  refine le_trans h1 (le_trans h2 ?_)
  rw [h3]
  exact le_of_eq (mul_comm _ _)

theorem source_fact_A2 {d n : ℕ} (hdn : d ≤ n)
    {p : Polynomial ℝ} {c x : ℝ} (hdeg : p.natDegree ≤ d) (hc : 0 ≤ c)
    (hgrid : ∀ i : ℕ, i ≤ n → |p.eval ((i : ℕ) : ℝ)| ≤ c)
    (hx : x ∈ Set.Icc (0 : ℝ) (n : ℝ)) :
    |p.eval x| ≤ (2 : ℝ) ^ d * c := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    have hp : p.natDegree = 0 := le_antisymm hdeg (Nat.zero_le _)
    have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hp
    rw [hpc, Polynomial.eval_C]
    have h0 : |p.coeff 0| ≤ c := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa using hgrid 0 (Nat.zero_le n)
    simpa using h0
  · set k : ℕ := ⌊x⌋₊ with hkdef
    set m : ℕ := min k (n - d) with hmdef
    have hm_le : m ≤ n - d := by rw [hmdef]; exact Nat.min_le_right _ _
    have hm_le_k : m ≤ k := by rw [hmdef]; exact Nat.min_le_left _ _
    have hxm0 : 0 ≤ x - (m : ℝ) := by
      have h1 : ((m : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm_le_k
      have h2 : ((k : ℕ) : ℝ) ≤ x := by rw [hkdef]; exact Nat.floor_le hx.1
      linarith
    have hxm1 : x - (m : ℝ) ≤ (d : ℝ) := by
      rcases le_or_gt k (n - d) with h | h
      · have hm : m = k := by rw [hmdef]; exact min_eq_left h
        have hlt : x < (k : ℝ) + 1 := by
          rw [hkdef]; exact Nat.lt_floor_add_one x
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        rw [hm]; linarith
      · have hm : m = n - d := by rw [hmdef]; exact min_eq_right (le_of_lt h)
        have hxn : x ≤ (n : ℝ) := hx.2
        have hmd : ((m : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) := by
          rw [hm, Nat.cast_sub hdn]
        rw [hmd]; linarith
    have hgrid' : ∀ i : ℕ, i ≤ d → |p.eval (((m + i : ℕ) : ℝ))| ≤ c := by
      intro i hi
      apply hgrid (m + i)
      have hle : m + i ≤ n - d + d := Nat.add_le_add hm_le hi
      rwa [Nat.sub_add_cancel hdn] at hle
    exact block_bound m d hdeg hc hgrid' hxm0 hxm1

theorem source_fact_A2_exact {d n : ℕ} (hdn : d ≤ n) {p : Polynomial ℝ} {c x : ℝ}
    (hdeg : p.natDegree ≤ d)
    (hgrid : ∀ i : ℕ, i ≤ n → |p.eval ((i : ℕ) : ℝ)| ≤ c)
    (hx : x ∈ Set.Icc (0 : ℝ) (n : ℝ)) :
    |p.eval x| ≤ (2 : ℝ) ^ d * c :=
  source_fact_A2 hdn hdeg (le_trans (abs_nonneg _) (hgrid 0 (Nat.zero_le n))) hgrid hx

end Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth
