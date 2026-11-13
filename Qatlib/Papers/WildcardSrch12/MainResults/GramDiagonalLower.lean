/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WildcardSrch12.MainResults.Model.GramOverlap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option backward.isDefEq.respectTransparency false

/-!
# Reciprocal-Overlap and Asymptotic Lower Bounds on the PGM Diagonal

This module formalizes Equation (2) and Lemma 7 of Ambainis and Montanaro on the
diagonal success probability `pgmProb n k x x` of the pretty-good measurement
for subset-query states: `pgmProb n k x x` is bounded below by the reciprocal of
the total Gram overlap and satisfies `1 - 2 a^2 - C / √n ≤ pgmProb n k x x`
whenever `n - k ≤ a √n + 1` with `0 ≤ a ≤ 1`.

## Main statements

* `gramEntry_zero`, `gramEntry_nonneg`, `gramEntry_le_one`: basic normalization
  and interval properties of `gramEntry`.
* `gram_diagonal_reciprocal_overlap_bound`: Equation (2), lower-bounding
  `pgmProb n k x x` by `1 / ∑ y, gramEntry n k (hammingDist x y)`.
* `lemma7_gram_diagonal_lower`: Lemma 7, establishing the `1 - 2 a^2 - O(1/√n)`
  lower bound on `pgmProb n k x x`.

## References

* [Ambainis and Montanaro, 2014][AmbainisMontanaro2014], Appendix A, Lemma 7, p. 11.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults.GramDiagonalLower

open Qatlib.Papers.WildcardSrch12.MainResults

private def character {n : ℕ} (x s : BitStr n) : ℝ :=
  ∏ i, if x i && s i then (-1 : ℝ) else 1

private theorem character_comm {n : ℕ} (x s : BitStr n) :
    character x s = character s x := by
  unfold character
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> cases s i <;> rfl

private theorem character_sq {n : ℕ} (x s : BitStr n) : character x s ^ 2 = 1 := by
  rw [character, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> cases s i <;> norm_num

private theorem character_orthogonality {n : ℕ} (x y : BitStr n) :
    (∑ s : BitStr n, character x s * character y s) =
      if x = y then (2 : ℝ) ^ n else 0 := by
  classical
  have hf : (∑ s : BitStr n, character x s * character y s) =
      ∏ i, if x i = y i then (2 : ℝ) else 0 := by
    simp only [character, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (κ := fun _ : Fin n => Bool)
      (f := fun i b => (if x i && b then (-1 : ℝ) else 1) *
        (if y i && b then (-1 : ℝ) else 1))]
    apply Finset.prod_congr rfl
    intro i _
    cases hx : x i <;> cases hy : y i <;> norm_num [hx, hy]
  rw [hf]
  by_cases hxy : x = y
  · simp [hxy]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    simpa [hxy] using Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [hi] : (if x i = y i then (2 : ℝ) else 0) = 0)

private def spectralValue (n k : ℕ) (s : BitStr n) : ℝ :=
  (2 : ℝ) ^ (n - k) / (Nat.choose n k : ℝ) *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0

private theorem spectralValue_nonneg (n k : ℕ) (s : BitStr n) :
    0 ≤ spectralValue n k s := by
  unfold spectralValue
  positivity

private theorem restricted_character_sum {n : ℕ} (x y : BitStr n)
    (S : Finset (Fin n)) :
    (∑ s : BitStr n,
      (if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0) *
        character x s * character y s) =
      if S ⊆ agreeSet x y then (2 : ℝ) ^ S.card else 0 := by
  classical
  have hf (s : BitStr n) :
      (if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0) *
          character x s * character y s =
        ∏ i, if s i then
          (if i ∈ S then
            (if x i then (-1 : ℝ) else 1) * (if y i then (-1 : ℝ) else 1)
           else 0) else 1 := by
    by_cases hs : (Finset.univ.filter fun i => s i) ⊆ S
    · simp only [hs, ite_true, one_mul, character, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      cases hsi : s i
      · simp
      · have hi : i ∈ S := hs (by simp [hsi])
        simp [hi]
    · have hex : ∃ i, s i = true ∧ i ∉ S := by
        simpa only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ,
          true_and, not_forall, not_imp, exists_prop] using hs
      obtain ⟨i, hi, hni⟩ := hex
      simp only [hs, ite_false, zero_mul]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hni])).symm
  rw [Finset.sum_congr rfl (fun s _ => hf s),
    ← Fintype.prod_sum (κ := fun _ : Fin n => Bool)
      (f := fun i b => if b then
        (if i ∈ S then
          (if x i then (-1 : ℝ) else 1) * (if y i then (-1 : ℝ) else 1)
         else 0) else 1)]
  have hcoord (i : Fin n) :
      (∑ b : Bool, if b then
        (if i ∈ S then
          (if x i then (-1 : ℝ) else 1) * (if y i then (-1 : ℝ) else 1)
         else 0) else 1) =
        if i ∈ S then (if x i = y i then (2 : ℝ) else 0) else 1 := by
    by_cases hi : i ∈ S <;> cases hx : x i <;> cases hy : y i <;>
      norm_num [hi, hx, hy]
  rw [Finset.prod_congr rfl (fun i _ => hcoord i), Finset.prod_ite_mem_eq]
  by_cases hs : S ⊆ agreeSet x y
  · simp only [hs, ite_true]
    have he : ∀ i ∈ S, x i = y i := fun i hi => (Finset.mem_filter.mp (hs hi)).2
    calc
      (∏ i ∈ S, if x i = y i then (2 : ℝ) else 0) = ∏ _i ∈ S, (2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [he i hi]
      _ = (2 : ℝ) ^ S.card := by simp
  · have hex : ∃ i ∈ S, x i ≠ y i := by
      simpa [Finset.subset_iff, agreeSet] using hs
    obtain ⟨i, hi, hne⟩ := hex
    simpa [hs] using Finset.prod_eq_zero hi
      (by simp [hne] : (if x i = y i then (2 : ℝ) else 0) = 0)

private theorem gramEntry_fourier {n k : ℕ} (hk : k ≤ n) (x y : BitStr n) :
    gramEntry n k (hammingDist x y) = ((2 : ℝ) ^ n)⁻¹ *
      ∑ s : BitStr n, spectralValue n k s * character x s * character y s := by
  classical
  have hsum : (∑ s : BitStr n,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0) *
          character x s * character y s) =
      (2 : ℝ) ^ k * (Nat.choose (n - hammingDist x y) k : ℝ) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [restricted_character_sum]
    have hc : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (if S ⊆ agreeSet x y then (2 : ℝ) ^ S.card else 0) =
          (2 : ℝ) ^ k * (if S ⊆ agreeSet x y then (1 : ℝ) else 0) := by
      intro S hS
      rw [(Finset.mem_powersetCard.mp hS).2]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
    congr 1
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      card_filter_powersetCard_subset, card_agreeSet]
  simp only [spectralValue, mul_assoc, ← Finset.mul_sum]
  rw [show (∑ s : BitStr n,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0) *
          (character x s * character y s)) =
      (2 : ℝ) ^ k * (Nat.choose (n - hammingDist x y) k : ℝ) by
        simpa only [mul_assoc] using hsum]
  have hp : (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k = (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  unfold gramEntry
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp [hchoose]
  linear_combination -(Nat.choose (n - hammingDist x y) k : ℝ) * hp

private def supportEquiv (n : ℕ) : BitStr n ≃ Finset (Fin n) where
  toFun s := Finset.univ.filter fun i => s i
  invFun S i := decide (i ∈ S)
  left_inv s := by
    funext i
    cases h : s i <;> simp [h]
  right_inv S := by
    ext i
    simp

private theorem bitWeight_le {n : ℕ} (s : BitStr n) : bitWeight s ≤ n := by
  simpa only [bitWeight, Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun i => s i) Finset.univ)

private theorem sum_by_weight (n : ℕ) (f : ℕ → ℝ) :
    (∑ s : BitStr n, f (bitWeight s)) =
      ∑ z ∈ Finset.range (n + 1), (Nat.choose n z : ℝ) * f z := by
  classical
  have hc (z : ℕ) :
      (Finset.univ.filter fun S : Finset (Fin n) => S.card = z) =
        (Finset.univ : Finset (Fin n)).powersetCard z := by
    ext S
    simp
  have hf := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Finset (Fin n))))
    (t := Finset.range (n + 1)) (g := fun S : Finset (Fin n) => S.card)
    (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (by
      simpa using Finset.card_le_card (Finset.subset_univ S)))) f
  rw [← (supportEquiv n).symm.sum_comp]
  change (∑ S : Finset (Fin n), f (bitWeight ((supportEquiv n).symm S))) = _
  have hw (S : Finset (Fin n)) : bitWeight ((supportEquiv n).symm S) = S.card := by
    simp [bitWeight, supportEquiv]
  simp_rw [hw]
  rw [← hf]
  apply Finset.sum_congr rfl
  intro z _
  simp [hc z, nsmul_eq_mul]

private def weightValue (n k z : ℕ) : ℝ :=
  (2 : ℝ) ^ (n - k) * (Nat.choose k z : ℝ) / (Nat.choose n z : ℝ)

private theorem spectralValue_weight {n k : ℕ} (hk : k ≤ n) (s : BitStr n) :
    spectralValue n k s = weightValue n k (bitWeight s) := by
  classical
  by_cases hs : bitWeight s ≤ k
  · have hc :
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0) =
          (Nat.choose (n - bitWeight s) (k - bitWeight s) : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_filter_powersetCard_subset _ _ k (Finset.subset_univ _) hs]
      simp [bitWeight]
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hwchoose : (Nat.choose n (bitWeight s) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (bitWeight_le s)).ne'
    have hm : (Nat.choose n k : ℝ) * (Nat.choose k (bitWeight s) : ℝ) =
        (Nat.choose n (bitWeight s) : ℝ) *
          (Nat.choose (n - bitWeight s) (k - bitWeight s) : ℝ) := by
      exact_mod_cast Nat.choose_mul (n := n) hs
    unfold spectralValue weightValue
    rw [hc]
    field_simp
    nlinarith only [hm]
  · have hc :
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          if (Finset.univ.filter fun i => s i) ⊆ S then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      have hnot : ¬ (Finset.univ.filter fun i => s i) ⊆ S := by
        intro hsub
        have hcard := Finset.card_le_card hsub
        rw [(Finset.mem_powersetCard.mp hS).2] at hcard
        exact hs hcard
      simp [hnot]
    simp [spectralValue, weightValue, hc, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hs)]

private theorem spectral_sqrt_sum {n k : ℕ} (hk : k ≤ n) :
    ((2 : ℝ) ^ n)⁻¹ * (∑ s : BitStr n, Real.sqrt (spectralValue n k s)) =
      ∑ z ∈ Finset.range (k + 1),
        Real.sqrt (((Nat.choose n z : ℝ) / 2 ^ n) * ((Nat.choose k z : ℝ) / 2 ^ k)) := by
  classical
  simp_rw [spectralValue_weight hk]
  rw [sum_by_weight n (fun z => Real.sqrt (weightValue n k z)), Finset.mul_sum]
  have hz0 : ∀ z ∈ Finset.range (n + 1), z ∉ Finset.range (k + 1) →
      ((2 : ℝ) ^ n)⁻¹ * ((Nat.choose n z : ℝ) * Real.sqrt (weightValue n k z)) = 0 := by
    intro z _ hz
    have hkz : k < z := by simpa using hz
    simp [weightValue, Nat.choose_eq_zero_of_lt hkz]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hk 1)) hz0]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : z ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hz)
  have hchoose : (Nat.choose n z : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hz'.trans hk)).ne'
  have hv : 0 ≤ weightValue n k z := by unfold weightValue; positivity
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  have htwok : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k = (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  rw [mul_pow, mul_pow, Real.sq_sqrt hv]
  unfold weightValue
  field_simp
  linear_combination -(Nat.choose k z : ℝ) * hp

private def binomialMass (m z : ℕ) : ℝ := (Nat.choose m z : ℝ) / 2 ^ m

private lemma binomialMass_pos {m z : ℕ} (hz : z ≤ m) : 0 < binomialMass m z := by
  unfold binomialMass
  exact div_pos (by exact_mod_cast Nat.choose_pos hz) (by positivity)

private lemma binomialMass_sum (m : ℕ) :
    ∑ z ∈ Finset.range (m + 1), binomialMass m z = 1 := by
  unfold binomialMass
  rw [← Finset.sum_div]
  have hs : (∑ z ∈ Finset.range (m + 1), (Nat.choose m z : ℝ)) = 2 ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  rw [hs, div_self (by positivity : (2 : ℝ) ^ m ≠ 0)]

private lemma binomialMass_mean {m : ℕ} (hm : 1 ≤ m) :
    ∑ z ∈ Finset.range (m + 1), binomialMass m z * (z : ℝ) = (m : ℝ) / 2 := by
  have hs : (∑ z ∈ Finset.range (m + 1), (z : ℝ) * (Nat.choose m z : ℝ)) =
      (m : ℝ) * 2 ^ (m - 1) := by
    exact_mod_cast Nat.sum_range_mul_choose m
  have hp : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  calc
    ∑ z ∈ Finset.range (m + 1), binomialMass m z * (z : ℝ) =
        (∑ z ∈ Finset.range (m + 1), (z : ℝ) * (Nat.choose m z : ℝ)) / 2 ^ m := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      unfold binomialMass
      ring
    _ = (m : ℝ) / 2 := by rw [hs, hp]; field_simp

private lemma binomialMass_succ_ratio {m z : ℕ} (hz : z ≤ m) :
    binomialMass m z / binomialMass (m + 1) z =
      2 * (1 - (z : ℝ) / ((m : ℝ) + 1)) := by
  have hc : (Nat.choose m z : ℝ) * ((m : ℝ) + 1) =
      (Nat.choose (m + 1) z : ℝ) * ((m : ℝ) + 1 - z) := by
    have h := Nat.choose_mul_succ_eq m z
    have hz' : z ≤ m + 1 := by omega
    exact_mod_cast h
  have hne : (Nat.choose (m + 1) z : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show z ≤ m + 1 by omega)).ne'
  unfold binomialMass
  rw [pow_succ]
  field_simp
  nlinarith

private lemma sqrt_log_lower {r : ℝ} (hr : 0 < r) :
    1 - (1 / 2) * Real.log (1 / r) ≤ Real.sqrt r := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hr)
  rw [Real.log_sqrt hr.le] at h
  rw [one_div r, Real.log_inv]
  linarith

private lemma binomialMass_log_ratio {k z : ℕ} (hz : z ≤ k) (g : ℕ) :
    Real.log (binomialMass k z / binomialMass (k + g) z) ≤
      ∑ j ∈ Finset.range g, (1 - 2 * (z : ℝ) / ((k : ℝ) + 1 + j)) := by
  have hq := binomialMass_pos hz
  induction g with
  | zero => simp [div_self hq.ne']
  | succ g ih =>
    have hm := binomialMass_pos (show z ≤ k + g by omega)
    have hn := binomialMass_pos (show z ≤ k + (g + 1) by omega)
    have he : Real.log (binomialMass k z / binomialMass (k + (g + 1)) z) =
        Real.log (binomialMass k z / binomialMass (k + g) z) +
          Real.log (binomialMass (k + g) z / binomialMass (k + g + 1) z) := by
      rw [Real.log_div hq.ne' hn.ne', Real.log_div hq.ne' hm.ne',
        Real.log_div hm.ne' (by simpa [Nat.add_assoc] using hn.ne')]
      ring
    have hstep : Real.log (binomialMass (k + g) z / binomialMass (k + g + 1) z) ≤
        1 - 2 * (z : ℝ) / ((k : ℝ) + 1 + g) := by
      have hr := Real.log_le_sub_one_of_pos
        (div_pos hm (by simpa [Nat.add_assoc] using hn))
      rw [← Nat.add_assoc k g 1,
        binomialMass_succ_ratio (show z ≤ k + g by omega)] at hr
      rw [binomialMass_succ_ratio (show z ≤ k + g by omega)]
      push_cast at hr ⊢
      have hd : (k : ℝ) + ↑g + 1 = ↑k + 1 + ↑g := by ring
      rw [hd] at hr ⊢
      convert hr using 1
      ring
    rw [he, Finset.sum_range_succ]
    exact add_le_add ih hstep

private lemma sum_range_successors (g : ℕ) :
    (∑ j ∈ Finset.range g, ((j : ℝ) + 1)) = (g : ℝ) * (g + 1) / 2 := by
  induction g with
  | zero => simp
  | succ g ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private lemma binomialMass_entropy_bound {k : ℕ} (hk : 1 ≤ k) (g : ℕ) :
    (∑ z ∈ Finset.range (k + 1), binomialMass k z *
      Real.log (binomialMass k z / binomialMass (k + g) z)) ≤
        (g : ℝ) * (g + 1) / (2 * ((k : ℝ) + 1)) := by
  calc
    _ ≤ ∑ z ∈ Finset.range (k + 1), binomialMass k z *
        ∑ j ∈ Finset.range g, (1 - 2 * (z : ℝ) / ((k : ℝ) + 1 + j)) := by
      apply Finset.sum_le_sum
      intro z hz
      have hz' : z ≤ k := by simpa using hz
      exact mul_le_mul_of_nonneg_left (binomialMass_log_ratio hz' g)
        (binomialMass_pos hz').le
    _ = ∑ j ∈ Finset.range g, ((j : ℝ) + 1) / ((k : ℝ) + 1 + j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have hd : (k : ℝ) + 1 + j ≠ 0 := by positivity
      calc
        _ = (∑ z ∈ Finset.range (k + 1), binomialMass k z) -
            2 * (∑ z ∈ Finset.range (k + 1), binomialMass k z * z) /
              ((k : ℝ) + 1 + j) := by
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib]
          congr 1
          rw [Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = ((j : ℝ) + 1) / ((k : ℝ) + 1 + j) := by
          rw [binomialMass_sum, binomialMass_mean hk]
          field_simp
          ring
    _ ≤ ∑ j ∈ Finset.range g, ((j : ℝ) + 1) / ((k : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (le_add_of_nonneg_right (Nat.cast_nonneg j))
    _ = (g : ℝ) * (g + 1) / (2 * ((k : ℝ) + 1)) := by
      rw [← Finset.sum_div, sum_range_successors]
      field_simp

private lemma binomial_fidelity_lower {n k : ℕ} (hk : k ≤ n) (hkpos : 1 ≤ k) :
    1 - ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) /
      (4 * ((k : ℝ) + 1)) ≤
        ∑ z ∈ Finset.range (k + 1), Real.sqrt
          (((Nat.choose n z : ℝ) / 2 ^ n) * ((Nat.choose k z : ℝ) / 2 ^ k)) := by
  have he := binomialMass_entropy_bound hkpos (n - k)
  rw [Nat.add_sub_of_le hk] at he
  have hl : (∑ z ∈ Finset.range (k + 1), binomialMass k z *
      (1 - (1 / 2) * Real.log (binomialMass k z / binomialMass n z))) ≤
        ∑ z ∈ Finset.range (k + 1), Real.sqrt (binomialMass n z * binomialMass k z) := by
    apply Finset.sum_le_sum
    intro z hz
    have hz' : z ≤ k := by simpa using hz
    have hq := binomialMass_pos hz'
    have hp := binomialMass_pos (hz'.trans hk)
    have hr := sqrt_log_lower (div_pos hp hq)
    have hd : 1 / (binomialMass n z / binomialMass k z) =
        binomialMass k z / binomialMass n z := by field_simp
    rw [hd] at hr
    have hs : binomialMass k z * Real.sqrt (binomialMass n z / binomialMass k z) =
        Real.sqrt (binomialMass n z * binomialMass k z) := by
      calc
        _ = Real.sqrt (binomialMass k z ^ 2) *
            Real.sqrt (binomialMass n z / binomialMass k z) := by rw [Real.sqrt_sq hq.le]
        _ = _ := by
          rw [← Real.sqrt_mul (sq_nonneg _)]
          congr 1
          field_simp
    simpa only [hs] using mul_le_mul_of_nonneg_left hr hq.le
  have hlhs : (∑ z ∈ Finset.range (k + 1), binomialMass k z *
      (1 - (1 / 2) * Real.log (binomialMass k z / binomialMass n z))) =
        1 - (1 / 2) * (∑ z ∈ Finset.range (k + 1), binomialMass k z *
          Real.log (binomialMass k z / binomialMass n z)) := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, binomialMass_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hlhs] at hl
  change _ ≤ ∑ z ∈ Finset.range (k + 1), Real.sqrt (binomialMass n z * binomialMass k z)
  have hd : (1 / 2 : ℝ) *
      (((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) / (2 * ((k : ℝ) + 1))) =
        ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) / (4 * ((k : ℝ) + 1)) := by
    field_simp
    ring
  linarith

/-- Diagonal normalization of the subset-query Gram entry when `k ≤ n`. -/
theorem gramEntry_zero {n k : ℕ} (hk : k ≤ n) : gramEntry n k 0 = 1 := by
  unfold gramEntry
  rw [Nat.sub_zero]
  have h : (Nat.choose n k : ℝ) ≠ 0 := by
    have := Nat.choose_pos hk
    exact_mod_cast this.ne'
  field_simp

/-- Subset-query Gram entries are nonnegative. -/
theorem gramEntry_nonneg (n k d : ℕ) : 0 ≤ gramEntry n k d := by
  unfold gramEntry
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Subset-query Gram entries are bounded above by `1` when `k ≤ n`. -/
theorem gramEntry_le_one {n k d : ℕ} (hk : k ≤ n) : gramEntry n k d ≤ 1 := by
  have hmono : Nat.choose (n - d) k ≤ Nat.choose n k :=
    Nat.choose_le_choose k (Nat.sub_le n d)
  have hpos : (0 : ℝ) < (Nat.choose n k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  unfold gramEntry
  rw [div_le_one hpos]
  exact_mod_cast hmono

private def walshMat (n : ℕ) : Matrix (BitStr n) (BitStr n) ℂ :=
  fun x s => (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character x s : ℝ) : ℂ)

private theorem walshMat_conjTranspose (n : ℕ) : (walshMat n)ᴴ = walshMat n := by
  ext x y
  simp only [Matrix.conjTranspose_apply, walshMat, Complex.star_def,
    Complex.conj_ofReal, character_comm y x]

private theorem walshMat_mul_self (n : ℕ) : walshMat n * walshMat n = 1 := by
  classical
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  ext x y
  rw [Matrix.mul_apply]
  have ht : ∀ s : BitStr n, walshMat n x s * walshMat n s y =
      (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ ^ 2 *
        (character x s * character y s) : ℝ) : ℂ) := by
    intro s
    simp only [walshMat, character_comm s y, ← Complex.ofReal_mul]
    congr 1
    ring
  simp_rw [ht]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum, character_orthogonality]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true, Matrix.one_apply_eq]
    rw [inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne', Complex.ofReal_one]
  · simp [hxy]

private def walshUnitary (n : ℕ) : Matrix.unitaryGroup (BitStr n) ℂ :=
  ⟨walshMat n, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      walshMat_conjTranspose, walshMat_mul_self]⟩

private theorem walsh_diagonal_entry (n : ℕ) (d : BitStr n → ℝ) (x : BitStr n) :
    (walshMat n * Matrix.diagonal (fun s => (d s : ℂ)) * walshMat n) x x =
      (((2 : ℝ) ^ n)⁻¹ * ∑ s, d s : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [walshMat, character_comm s x, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  calc
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character x s * d s *
        ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character x s) =
        ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 2 * character x s ^ 2 * d s := by ring
    _ = ((2 : ℝ) ^ n)⁻¹ * d s := by rw [inv_pow, Real.sq_sqrt hp, character_sq, mul_one]

private theorem walsh_sandwich_entry (n : ℕ) (d : BitStr n → ℝ) (x y : BitStr n) :
    (walshMat n * Matrix.diagonal (fun s => (d s : ℂ)) * walshMat n) x y =
      (((2 : ℝ) ^ n)⁻¹ * ∑ s, d s * character x s * character y s : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [walshMat, character_comm s y, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  calc
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character x s * d s *
        ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character y s) =
        ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 2 * (d s * character x s * character y s) := by
      ring
    _ = ((2 : ℝ) ^ n)⁻¹ * (d s * character x s * character y s) := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]

private theorem walsh_sqrt (n : ℕ) (H : HermitianMat (BitStr n) ℂ)
    (d : BitStr n → ℝ)
    (hd : H.mat = walshMat n * Matrix.diagonal (fun s => (d s : ℂ)) * walshMat n) :
    H.sqrt.mat = walshMat n * Matrix.diagonal (fun s => (Real.sqrt (d s) : ℂ)) *
      walshMat n := by
  classical
  have hd' : H.mat = (walshUnitary n).val *
      Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d) * star (walshUnitary n).val := by
    rw [hd]
    simp only [walshUnitary, Matrix.star_eq_conjTranspose, walshMat_conjTranspose]
    rfl
  rw [HermitianMat.sqrt, HermitianMat.mat_cfc, H.H.cfc_eq]
  rw [H.H.cfc_eq_any_unitary hd' Real.sqrt]
  simp only [walshUnitary, Matrix.star_eq_conjTranspose, walshMat_conjTranspose]
  rfl

private theorem walsh_eigenvalue (n : ℕ) (d : BitStr n → ℝ)
    (A : Matrix (BitStr n) (BitStr n) ℝ)
    (hd : A.map Complex.ofReal =
      walshMat n * Matrix.diagonal (fun s => (d s : ℂ)) * walshMat n)
    (x s : BitStr n) :
    d s = ∑ y, A x y * character x s * character y s := by
  classical
  have he : A.map Complex.ofReal * walshMat n =
      walshMat n * Matrix.diagonal (fun s => (d s : ℂ)) := by
    rw [hd, Matrix.mul_assoc, walshMat_mul_self, Matrix.mul_one]
  have he' := congrArg (fun M => (M x s).re) he
  rw [Matrix.mul_diagonal] at he'
  simp only [Matrix.mul_apply, Matrix.map_apply, walshMat,
    ← Complex.ofReal_mul,
    Complex.re_sum, Complex.ofReal_re] at he'
  have hs : Real.sqrt ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have hc : character x s * character x s = 1 := by
    simpa only [pow_two] using character_sq x s
  have ht : (∑ y, A x y * ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character y s)) *
      (Real.sqrt ((2 : ℝ) ^ n) * character x s) =
      ∑ y, A x y * character x s * character y s := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    field_simp
  rw [he'] at ht
  have ht' : (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * character x s * d s *
      (Real.sqrt ((2 : ℝ) ^ n) * character x s) = d s := by
    calc
      _ = ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ * Real.sqrt ((2 : ℝ) ^ n)) *
          (character x s * character x s) * d s := by ring
      _ = d s := by rw [inv_mul_cancel₀ hs, hc, one_mul, one_mul]
  rwa [ht'] at ht

private theorem gramMat_spectral {n k : ℕ} (hk : k ≤ n) :
    (gramMat n k).mat = walshMat n *
      Matrix.diagonal (fun s => (spectralValue n k s : ℂ)) * walshMat n := by
  ext x y
  rw [gramMat_mat, walsh_sandwich_entry, hammingDist_comm,
    gramEntry_fourier hk]

private theorem gram_sqrt_diagonal {n k : ℕ} (hk : k ≤ n) (x : BitStr n) :
    (gramMat n k).sqrt.mat x x =
      (((2 : ℝ) ^ n)⁻¹ * ∑ s, Real.sqrt (spectralValue n k s) : ℝ) := by
  rw [walsh_sqrt n (gramMat n k) (spectralValue n k) (gramMat_spectral hk),
    walsh_diagonal_entry]

private theorem spectralValue_le_row {n k : ℕ} (hk : k ≤ n) (x s : BitStr n) :
    spectralValue n k s ≤ ∑ y, gramEntry n k (hammingDist x y) := by
  have hd : (Matrix.of (fun x y => gramEntry n k (hammingDist x y))).map Complex.ofReal =
      walshMat n * Matrix.diagonal (fun s => (spectralValue n k s : ℂ)) *
        walshMat n := by
    rw [← gramMat_spectral hk]
    ext u v
    simp only [Matrix.map_apply, Matrix.of_apply, hammingDist_comm u v]
    exact (gramMat_mat v u).symm
  rw [walsh_eigenvalue n (spectralValue n k)
    (Matrix.of (fun u v => gramEntry n k (hammingDist u v))) hd x s]
  apply Finset.sum_le_sum
  intro y _
  have hc : character x s * character y s ≤ 1 := by
    nlinarith [character_sq x s, character_sq y s,
      sq_nonneg (character x s - character y s)]
  have hn := gramEntry_nonneg n k (hammingDist x y)
  rw [Matrix.of_apply]
  nlinarith

private theorem spectralValue_sum {n k : ℕ} (hk : k ≤ n) (x : BitStr n) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ s, spectralValue n k s = 1 := by
  have h := congrArg (fun M => (M x x).re) (gramMat_spectral hk)
  simpa only [gramMat_mat, hammingDist_self, gramEntry_zero hk, Complex.ofReal_one,
    Complex.one_re, walsh_diagonal_entry, Complex.ofReal_re] using h.symm

/-- Equation (2): the PGM diagonal probability is at least the reciprocal of the
sum of Gram overlaps across all bitstrings. -/
theorem gram_diagonal_reciprocal_overlap_bound {n k : ℕ} (x : BitStr n) :
    1 / (∑ y : BitStr n, gramEntry n k (hammingDist x y)) ≤ pgmProb n k x x := by
  by_cases hk : k ≤ n
  · let M : ℝ := ∑ y : BitStr n, gramEntry n k (hammingDist x y)
    have hM : 1 ≤ M := by
      have h := Finset.single_le_sum
        (fun y (_ : y ∈ (Finset.univ : Finset (BitStr n))) =>
          gramEntry_nonneg n k (hammingDist x y)) (Finset.mem_univ x)
      simpa only [hammingDist_self, gramEntry_zero hk] using h
    have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hkey : 1 ≤ Real.sqrt M * ((gramMat n k).sqrt.mat x x).re := by
      rw [gram_sqrt_diagonal hk, Complex.ofReal_re]
      calc
        1 = ((2 : ℝ) ^ n)⁻¹ * ∑ s, spectralValue n k s :=
          (spectralValue_sum hk x).symm
        _ ≤ ((2 : ℝ) ^ n)⁻¹ *
            ∑ s, Real.sqrt M * Real.sqrt (spectralValue n k s) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro s _
          calc
            spectralValue n k s = Real.sqrt (spectralValue n k s) *
                Real.sqrt (spectralValue n k s) :=
              (Real.mul_self_sqrt (spectralValue_nonneg n k s)).symm
            _ ≤ Real.sqrt M * Real.sqrt (spectralValue n k s) :=
              mul_le_mul_of_nonneg_right
                (Real.sqrt_le_sqrt (spectralValue_le_row hk x s)) (Real.sqrt_nonneg _)
        _ = Real.sqrt M * (((2 : ℝ) ^ n)⁻¹ *
            ∑ s, Real.sqrt (spectralValue n k s)) := by rw [← Finset.mul_sum]; ring
    have hsq : 1 ≤ M * ((gramMat n k).sqrt.mat x x).re ^ 2 := by
      have h : 1 ≤ (Real.sqrt M * ((gramMat n k).sqrt.mat x x).re) ^ 2 := by
        nlinarith
      rwa [mul_pow, Real.sq_sqrt hMp.le] at h
    have hp : pgmProb n k x x = ((gramMat n k).sqrt.mat x x).re ^ 2 := by
      have him : ((gramMat n k).sqrt.mat x x).im = 0 :=
        (gramMat n k).sqrt.complex_im_eq_zero x
      simp only [pgmProb, Complex.normSq_apply, him, mul_zero, add_zero, pow_two]
    change 1 / M ≤ pgmProb n k x x
    rw [div_le_iff₀ hMp, hp]
    simpa only [mul_comm] using hsq
  · have hz : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [gramEntry, hz, Nat.cast_zero, div_zero, Finset.sum_const_zero]
    exact Complex.normSq_nonneg _

private lemma large_dimension_arithmetic {n k : ℕ} {a : ℝ}
    (hn : 101 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hk : k ≤ n)
    (hgap : (n : ℝ) - (k : ℝ) ≤ a * Real.sqrt (n : ℝ) + 1) :
    1 ≤ k ∧
      0 < 1 - ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) /
        (4 * ((k : ℝ) + 1)) ∧
      1 - 2 * a ^ 2 - 10 / Real.sqrt (n : ℝ) ≤
        1 - ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) /
          (2 * ((k : ℝ) + 1)) := by
  set t := Real.sqrt (n : ℝ) with ht
  set g : ℝ := ((n - k : ℕ) : ℝ) with hg
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have htsq : t ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht10 : 10 < t := by nlinarith
  have htpos : 0 < t := by linarith
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  have hgeq : g = (n : ℝ) - k := by rw [hg, Nat.cast_sub hk]
  have hgat : g ≤ a * t + 1 := by simpa [hgeq, ht] using hgap
  have hgt : g ≤ t + 1 := by nlinarith
  have hkpos : 1 ≤ k := by
    by_contra h
    have hkzero : k = 0 := by omega
    simp only [hkzero, Nat.cast_zero, sub_zero] at hgeq
    nlinarith [sq_nonneg (t - 2)]
  have hden : (n : ℝ) ≤ 2 * ((k : ℝ) + 1) := by
    nlinarith [sq_nonneg (t - 1)]
  have hprod : g * (g + 1) ≤ (a * t + 1) * (a * t + 2) := by
    exact mul_le_mul hgat (by linarith) (by positivity) (by positivity)
  have hprod2 : g * (g + 1) ≤ 2 * a ^ 2 * (n : ℝ) + 5 := by
    nlinarith [sq_nonneg (a * t - 3 / 2)]
  have hcoarse : g * (g + 1) < 4 * ((k : ℝ) + 1) := by
    have hmul := mul_le_mul hgt (show g + 1 ≤ t + 2 by linarith)
      (show 0 ≤ g + 1 by linarith) (show 0 ≤ t + 1 by linarith)
    nlinarith [sq_nonneg (t - 2)]
  have hpositive : 0 < 1 - g * (g + 1) / (4 * ((k : ℝ) + 1)) := by
    have hd4 : 0 < 4 * ((k : ℝ) + 1) := by positivity
    have := (div_lt_one hd4).2 hcoarse
    linarith
  have hnpos : (0 : ℝ) < n := by positivity
  have hratio : g * (g + 1) / (2 * ((k : ℝ) + 1)) ≤ 2 * a ^ 2 + 10 / t := by
    calc
      g * (g + 1) / (2 * ((k : ℝ) + 1)) ≤ g * (g + 1) / (n : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hnpos hden
      _ ≤ (2 * a ^ 2 * (n : ℝ) + 5) / (n : ℝ) :=
        div_le_div_of_nonneg_right hprod2 hnpos.le
      _ = 2 * a ^ 2 + 5 / (n : ℝ) := by field_simp
      _ ≤ 2 * a ^ 2 + 10 / t := by
        have hlast : 5 / (n : ℝ) ≤ 10 / t := by
          apply (div_le_div_iff₀ hnpos htpos).2
          nlinarith [sq_nonneg (t - 1)]
        linarith
  exact ⟨hkpos, hpositive, by dsimp [g, t] at hratio ⊢; linarith⟩

private lemma small_dimension_arithmetic {n : ℕ} {a : ℝ}
    (hn : 1 ≤ n) (hn100 : n ≤ 100) :
    1 - 2 * a ^ 2 - 10 / Real.sqrt (n : ℝ) ≤ 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos := Real.sqrt_pos.2 hnpos
  have hsle : Real.sqrt (n : ℝ) ≤ 10 := by
    have hnR : (n : ℝ) ≤ 100 := by exact_mod_cast hn100
    nlinarith [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg (n : ℝ)]
  have hdiv : (1 : ℝ) ≤ 10 / Real.sqrt (n : ℝ) := (le_div_iff₀ hspos).2 (by simpa)
  nlinarith [sq_nonneg a]

/-- Lemma 7: for `0 ≤ a ≤ 1`, `k ≤ n`, and `n - k ≤ a √n + 1`, the PGM diagonal
probability satisfies `1 - 2 a^2 - C / √n ≤ pgmProb n k x x` for an absolute
constant `C > 0`. -/
theorem lemma7_gram_diagonal_lower :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (a : ℝ) (x : BitStr n),
        1 ≤ n → 0 ≤ a → a ≤ 1 → k ≤ n →
        (n : ℝ) - (k : ℝ) ≤ a * Real.sqrt (n : ℝ) + 1 →
        1 - 2 * a ^ 2 - C / Real.sqrt (n : ℝ) ≤ pgmProb n k x x := by
  refine ⟨10, by norm_num, ?_⟩
  intro n k a x hn ha ha1 hk hgap
  by_cases hn100 : n ≤ 100
  · exact (small_dimension_arithmetic hn hn100).trans (Complex.normSq_nonneg _)
  · obtain ⟨hkpos, hpositive, hcomparison⟩ :=
      large_dimension_arithmetic (by omega : 101 ≤ n) ha ha1 hk hgap
    let e : ℝ := ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) /
      (4 * ((k : ℝ) + 1))
    have hdiag : 1 - e ≤ ((gramMat n k).sqrt.mat x x).re := by
      rw [gram_sqrt_diagonal hk, Complex.ofReal_re, spectral_sqrt_sum hk]
      exact binomial_fidelity_lower hk hkpos
    have hpos : 0 ≤ 1 - e := hpositive.le
    have hsquared : (1 - e) ^ 2 ≤ ((gramMat n k).sqrt.mat x x).re ^ 2 := by
      have h := mul_le_mul hdiag hdiag hpos (hpos.trans hdiag)
      simpa only [pow_two] using h
    have him : ((gramMat n k).sqrt.mat x x).im = 0 :=
      (gramMat n k).sqrt.complex_im_eq_zero x
    have hp : pgmProb n k x x = ((gramMat n k).sqrt.mat x x).re ^ 2 := by
      simp only [pgmProb, Complex.normSq_apply, him, mul_zero, add_zero, pow_two]
    have hlower : 1 - 2 * e ≤ pgmProb n k x x := by
      rw [hp]
      nlinarith [sq_nonneg e]
    have he : 2 * e = ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) + 1) /
        (2 * ((k : ℝ) + 1)) := by dsimp [e]; field_simp; ring
    rw [he] at hlower
    exact hcomparison.trans hlower

end Qatlib.Papers.WildcardSrch12.MainResults.GramDiagonalLower
