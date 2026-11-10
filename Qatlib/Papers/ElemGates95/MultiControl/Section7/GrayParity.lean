/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.MultibitNetworks
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open scoped BigOperators

namespace Qatlib.Papers.ElemGates95.MultiControl.Section7

def bitSign (b : Bool) : ℚ := if b then -1 else 1

def subsetSign {m : ℕ} (x : Fin m → Bool) (S : Finset (Fin m)) : ℚ :=
  ∏ i ∈ S, bitSign (x i)

def xorVal {m : ℕ} (x : Fin m → Bool) (S : Finset (Fin m)) : ℚ :=
  (1 - subsetSign x S) / 2

theorem prod_bitSign_eq_pow {m : ℕ} (x : Fin m → Bool) (S : Finset (Fin m)) :
    ∏ i ∈ S, bitSign (x i) = (-1 : ℚ) ^ (S.filter (fun i => x i)).card := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.filter_insert]
    by_cases hxa : x a = true
    · rw [if_pos hxa]
      have hmem : a ∉ S.filter (fun i => x i) := by
        simp only [Finset.mem_filter]
        exact fun h => ha h.1
      rw [Finset.card_insert_of_notMem hmem, pow_succ]
      simp [bitSign, hxa]
    · rw [if_neg hxa]
      simp [bitSign, hxa]

theorem subsetSign_eq_pow {m : ℕ} (x : Fin m → Bool) (S : Finset (Fin m)) :
    subsetSign x S = (-1 : ℚ) ^ (S.filter (fun i => x i)).card :=
  prod_bitSign_eq_pow x S

theorem xorVal_eq_parity {m : ℕ} (x : Fin m → Bool) (S : Finset (Fin m)) :
    xorVal x S = if Even (S.filter (fun i => x i)).card then 0 else 1 := by
  rw [xorVal, subsetSign_eq_pow, neg_one_pow_eq_ite]
  by_cases hE : Even (S.filter (fun i => x i)).card <;> simp [hE]

theorem xorVal_zero_or_one {m : ℕ} (x : Fin m → Bool) (S : Finset (Fin m)) :
    xorVal x S = 0 ∨ xorVal x S = 1 := by
  rw [xorVal_eq_parity]; split_ifs <;> simp

theorem prod_one_sub_bitSign {m : ℕ} (x : Fin m → Bool) :
    ∏ i, (1 - bitSign (x i)) =
      if (∀ i, x i = true) then (2 : ℚ) ^ m else 0 := by
  classical
  by_cases h : ∀ i, x i = true
  · rw [if_pos h]
    have h2 : ∀ i, bitSign (x i) = -1 := fun i => by simp [bitSign, h i]
    simp only [h2, show (1 : ℚ) - (-1) = 2 by norm_num]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [bitSign, show x i = false from by simpa using! hi]

theorem sum_neg_one_pow_card_mul_sign {m : ℕ} (x : Fin m → Bool) :
    ∑ S : Finset (Fin m), ((-1 : ℚ) ^ S.card) * subsetSign x S
      = ∏ i, (1 - bitSign (x i)) := by
  classical
  simp only [sub_eq_add_neg]
  have h := Finset.prod_one_add (f := fun i => -bitSign (x i))
    (Finset.univ : Finset (Fin m))
  rw [Finset.powerset_univ] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro S _
  rw [subsetSign]
  have hstep : (∏ i ∈ S, -bitSign (x i))
      = ∏ i ∈ S, ((-1 : ℚ) * bitSign (x i)) := by
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_const]

theorem sum_neg_one_pow_card {m : ℕ} (hm : 1 ≤ m) :
    ∑ S : Finset (Fin m), (-1 : ℚ) ^ S.card = 0 := by
  classical
  have h := Finset.prod_one_add (f := fun _ => (-1 : ℚ)) (Finset.univ : Finset (Fin m))
  rw [Finset.powerset_univ] at h
  have hz : (∏ i : Fin m, (1 + (-1 : ℚ))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩)
    norm_num
  rw [show (∏ i ∈ (Finset.univ : Finset (Fin m)), (1 + (-1 : ℚ))) = 0 by
    simpa using! hz] at h
  simpa [Finset.prod_const] using! h.symm

theorem sum_shift {m : ℕ} (_hm : 1 ≤ m) (g : Finset (Fin m) → ℚ) :
    ∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1) * g S
      = 2 * g ∅ - ∑ S : Finset (Fin m), (-1 : ℚ) ^ S.card * g S := by
  classical
  have hmem : (∅ : Finset (Fin m)) ∈ (Finset.univ : Finset (Finset (Fin m))) :=
    Finset.mem_univ _
  have hsplit : (∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1) * g S)
      = (∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin m))),
            (-1 : ℚ) ^ (S.card - 1) * g S)
        + (-1 : ℚ) ^ ((∅ : Finset (Fin m)).card - 1) * g ∅ := by
    rw [Finset.sum_erase_add _ _ hmem]
  have hneg : (∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin m))),
        (-1 : ℚ) ^ (S.card - 1) * g S)
      = - ∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin m))),
            (-1 : ℚ) ^ S.card * g S := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hSne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    have hcard : 1 ≤ S.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
    have h1 : (-1 : ℚ) ^ S.card = (-1) ^ (S.card - 1) * (-1) := by
      rw [← pow_succ, Nat.sub_add_cancel hcard]
    rw [h1]; ring
  have hsplit2 : (∑ S : Finset (Fin m), (-1 : ℚ) ^ S.card * g S)
      = (∑ S ∈ (Finset.univ.erase (∅ : Finset (Fin m))),
            (-1 : ℚ) ^ S.card * g S)
        + (-1 : ℚ) ^ ((∅ : Finset (Fin m)).card) * g ∅ := by
    rw [Finset.sum_erase_add _ _ hmem]
  have hzero : (-1 : ℚ) ^ ((∅ : Finset (Fin m)).card - 1) * g ∅ = g ∅ := by norm_num
  have hzero2 : (-1 : ℚ) ^ ((∅ : Finset (Fin m)).card) * g ∅ = g ∅ := by norm_num
  rw [hsplit, hneg, hzero]
  rw [hzero2] at hsplit2
  linarith

theorem altSum_identity {m : ℕ} (hm : 1 ≤ m) (x : Fin m → Bool) :
    ∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1) * xorVal x S
      = (2 : ℚ) ^ (m - 1) * (if (∀ i, x i = true) then 1 else 0) := by
  classical
  have hdist : (∑ S : Finset (Fin m),
        (-1 : ℚ) ^ (S.card - 1) * xorVal x S)
      = (1 / 2) * ((∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1))
          - ∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1) * subsetSign x S) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    rw [xorVal]
    ring
  rw [hdist]
  have hA : (∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1)) = 2 := by
    have h := sum_shift hm (fun _ : Finset (Fin m) => (1 : ℚ))
    have h1 : (∑ S : Finset (Fin m), (-1 : ℚ) ^ S.card * (1 : ℚ)) = 0 := by
      simpa using! sum_neg_one_pow_card hm
    rw [h1] at h
    simpa using! h
  have hB : (∑ S : Finset (Fin m), (-1 : ℚ) ^ (S.card - 1) * subsetSign x S)
      = 2 - ∏ i, (1 - bitSign (x i)) := by
    rw [sum_shift hm (subsetSign x), sum_neg_one_pow_card_mul_sign x]
    simp [subsetSign]
  rw [hA, hB]
  have hprod := prod_one_sub_bitSign x
  rw [hprod]
  by_cases hall : ∀ i, x i = true
  · rw [if_pos hall, if_pos hall]
    have hp : (2 : ℚ) ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [hp]; ring
  · rw [if_neg hall, if_neg hall]; ring

theorem card_nonempty_subsets (m : ℕ) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.Nonempty)).card
      = 2 ^ m - 1 := by
  classical
  have hmem : (∅ : Finset (Fin m)) ∈ (Finset.univ : Finset (Finset (Fin m))) :=
    Finset.mem_univ _
  have hfilter : (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.Nonempty)
      = (Finset.univ : Finset (Finset (Fin m))).erase ∅ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · intro h; exact Finset.nonempty_iff_ne_empty.mp h
    · intro h; exact Finset.nonempty_iff_ne_empty.mpr h
  rw [hfilter, Finset.card_erase_of_mem hmem, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

theorem twoPow_root_exists (k : ℕ) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ V : Matrix Bool Bool ℂ, V ∈ Matrix.unitaryGroup Bool ℂ ∧ V ^ (2 ^ k) = U := by
  induction k generalizing U with
  | zero => exact ⟨U, hU, by simp⟩
  | succ k ih =>
    obtain ⟨W, hW, hWW⟩ := ih U hU
    obtain ⟨V, hV, hVV⟩ := noWork_unitary_square_root W hW
    refine ⟨V, hV, ?_⟩
    rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ]; ring]
    rw [pow_mul, pow_two, hVV, hWW]

end Qatlib.Papers.ElemGates95.MultiControl.Section7
