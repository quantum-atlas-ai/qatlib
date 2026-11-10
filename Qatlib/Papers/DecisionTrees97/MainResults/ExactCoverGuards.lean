/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.DecisionTrees97.MainResults.ExactCoverGuards

variable {m n : ℕ}

def rowOnes (A : Fin m → Fin n → Bool) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun k => A j k = true)

def prefixSum (A : Fin m → Fin n → Bool) (i : ℕ) (x : Fin n → Bool)
    (j : Fin m) : ℕ :=
  ∑ k : Fin n, if k.val < i ∧ A j k = true ∧ x k = true then 1 else 0

def prefixZeros (A : Fin m → Fin n → Bool) (i : ℕ) (x : Fin n → Bool)
    (j : Fin m) : ℕ :=
  ∑ k : Fin n, if k.val < i ∧ A j k = true ∧ x k = false then 1 else 0

def rowSum (A : Fin m → Fin n → Bool) (x : Fin n → Bool) (j : Fin m) : ℕ :=
  ∑ k : Fin n, if A j k = true ∧ x k = true then 1 else 0

def allowedOne (A : Fin m → Fin n → Bool) (i : Fin n) (x : Fin n → Bool) : Prop :=
  ∀ j : Fin m, A j i = true → prefixSum A i.val x j = 0

def allowedZero (A : Fin m → Fin n → Bool) (i : Fin n) (x : Fin n → Bool) : Prop :=
  ∀ j : Fin m, A j i = true → prefixZeros A i.val x j ≠ 2

def allowedAt (A : Fin m → Fin n → Bool) (i : Fin n) (x : Fin n → Bool) : Prop :=
  if x i then allowedOne A i x else allowedZero A i x

def legalAt (A : Fin m → Fin n → Bool) (i : ℕ) (x : Fin n → Bool) : Prop :=
  ∀ k : Fin n, k.val < i → allowedAt A k x

def guardSupport (A : Fin m → Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin m => A j i = true)).biUnion
    (fun j => (rowOnes A j).erase i)

theorem psum_card (A : Fin m → Fin n → Bool) (i : ℕ) (x : Fin n → Bool)
    (j : Fin m) :
    prefixSum A i x j =
      (Finset.univ.filter
        (fun k : Fin n => k.val < i ∧ A j k = true ∧ x k = true)).card := by
  rw [prefixSum]
  simpa using (Finset.card_filter
    (fun k : Fin n => k.val < i ∧ A j k = true ∧ x k = true) Finset.univ).symm

theorem pzero_card (A : Fin m → Fin n → Bool) (i : ℕ) (x : Fin n → Bool)
    (j : Fin m) :
    prefixZeros A i x j =
      (Finset.univ.filter
        (fun k : Fin n => k.val < i ∧ A j k = true ∧ x k = false)).card := by
  rw [prefixZeros]
  simpa using (Finset.card_filter
    (fun k : Fin n => k.val < i ∧ A j k = true ∧ x k = false) Finset.univ).symm

theorem rowSum_eq_psum (A : Fin m → Fin n → Bool) (x : Fin n → Bool)
    (j : Fin m) : rowSum A x j = prefixSum A n x j := by
  rw [rowSum, prefixSum]
  apply Finset.sum_congr rfl
  intro k _
  simp [k.isLt]

theorem psum_succ (A : Fin m → Fin n → Bool) (i : ℕ) (hi : i < n)
    (x : Fin n → Bool) (j : Fin m) :
    prefixSum A (i + 1) x j =
      prefixSum A i x j +
        (if A j ⟨i, hi⟩ = true ∧ x ⟨i, hi⟩ = true then 1 else 0) := by
  rw [prefixSum, prefixSum]
  have hpt : ∀ k : Fin n,
      (if k.val < i + 1 ∧ A j k = true ∧ x k = true then (1 : ℕ) else 0) =
        (if k.val < i ∧ A j k = true ∧ x k = true then 1 else 0) +
          (if k = ⟨i, hi⟩ then
            (if A j ⟨i, hi⟩ = true ∧ x ⟨i, hi⟩ = true then 1 else 0) else 0) := by
    intro k
    by_cases hk : k = ⟨i, hi⟩
    · subst hk
      simp
    · have hne : k.val ≠ i := fun h => hk (Fin.ext h)
      have hiff : k.val < i + 1 ↔ k.val < i := by omega
      simp [hk, hne, hiff]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib]
  have hsingle : (∑ k : Fin n,
      if k = ⟨i, hi⟩ then (if A j ⟨i, hi⟩ = true ∧ x ⟨i, hi⟩ = true then 1 else 0)
        else 0) =
      (if A j ⟨i, hi⟩ = true ∧ x ⟨i, hi⟩ = true then (1 : ℕ) else 0) := by
    simp
  rw [hsingle]

theorem psum_mono (A : Fin m → Fin n → Bool) (x : Fin n → Bool) {i i' : ℕ}
    (h : i ≤ i') (j : Fin m) : prefixSum A i x j ≤ prefixSum A i' x j := by
  rw [prefixSum, prefixSum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < i
  · have hk' : k.val < i' := lt_of_lt_of_le hk h
    simp [hk, hk']
  · have hk' : ¬ (k.val < i' ∧ A j k = true ∧ x k = true) ∨
        ¬ (k.val < i ∧ A j k = true ∧ x k = true) := Or.inr (by tauto)
    have h0 : (if k.val < i ∧ A j k = true ∧ x k = true then (1 : ℕ) else 0) = 0 := by
      simp [hk]
    rw [h0]
    exact Nat.zero_le _

theorem rowSum_le_three (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3) (x : Fin n → Bool) (j : Fin m) :
    rowSum A x j ≤ 3 := by
  rw [rowSum_eq_psum, psum_card]
  have hsub : (Finset.univ.filter
      (fun k : Fin n => k.val < n ∧ A j k = true ∧ x k = true)) ⊆ rowOnes A j := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp [rowOnes, hk.2.1]
  calc (Finset.univ.filter
        (fun k : Fin n => k.val < n ∧ A j k = true ∧ x k = true)).card
      ≤ (rowOnes A j).card := Finset.card_le_card hsub
    _ = 3 := hrow j

theorem psum_le_one (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3) (x : Fin n → Bool) :
    ∀ i, legalAt A i x → ∀ j, prefixSum A i x j ≤ 1 := by
  intro i
  induction i with
  | zero =>
    intro _ j
    simp [prefixSum]
  | succ i ih =>
    intro hleg j
    by_cases hi : i < n
    · rw [psum_succ A i hi x j]
      have hleg' : legalAt A i x :=
        fun k hk => hleg k (Nat.lt_trans hk (Nat.lt_succ_self i))
      have h1 := ih hleg' j
      by_cases hbit : A j ⟨i, hi⟩ = true ∧ x ⟨i, hi⟩ = true
      · rw [if_pos hbit]
        have hall := hleg ⟨i, hi⟩ (Nat.lt_succ_self i)
        simp only [allowedAt, hbit.2, if_true] at hall
        have hz : prefixSum A i x j = 0 := hall j hbit.1
        rw [hz]
      · rw [if_neg hbit]
        simpa using h1
    · have hEq : prefixSum A (i + 1) x j = prefixSum A i x j := by
        rw [prefixSum, prefixSum]
        apply Finset.sum_congr rfl
        intro k _
        have hki : k.val < i := Nat.lt_of_lt_of_le k.isLt (Nat.le_of_not_lt hi)
        have hk : k.val < i + 1 ↔ k.val < i :=
          ⟨fun _ => hki, fun h => Nat.lt_succ_of_lt h⟩
        simp [hk]
      rw [hEq]
      exact ih (fun k hk => hleg k (Nat.lt_trans hk (Nat.lt_succ_self i))) j

theorem rowSum_one (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3) (x : Fin n → Bool)
    (hleg : legalAt A n x) (j : Fin m) : rowSum A x j = 1 := by
  have hle : rowSum A x j ≤ 1 := by
    rw [rowSum_eq_psum]
    exact psum_le_one A hrow x n hleg j
  have hne : (rowOnes A j).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have := hrow j
    rw [hemp] at this
    simp at this
  obtain ⟨r, hr_mem, hr_max⟩ :=
    Finset.exists_max_image (rowOnes A j) (fun k : Fin n => k.val) hne
  have hrA : A j r = true := by simpa [rowOnes] using hr_mem
  by_contra hne1
  have hzero : rowSum A x j = 0 := by omega
  have hfalse : ∀ k ∈ rowOnes A j, x k = false := by
    intro k hk
    have hkA : A j k = true := by simpa [rowOnes] using hk
    by_contra hx
    have hx' : x k = true := by
      cases hxk : x k with
      | false => exact absurd hxk hx
      | true => rfl
    have hpos : 0 < rowSum A x j := by
      rw [rowSum]
      have hterm : (if A j k = true ∧ x k = true then (1 : ℕ) else 0) = 1 := by
        simp [hkA, hx']
      calc 0 < (if A j k = true ∧ x k = true then (1 : ℕ) else 0) := by
            rw [hterm]; norm_num
        _ ≤ ∑ l : Fin n, (if A j l = true ∧ x l = true then (1 : ℕ) else 0) :=
            Finset.single_le_sum
              (f := fun l : Fin n => if A j l = true ∧ x l = true then (1 : ℕ) else 0)
              (fun l _ => by
                show 0 ≤ (if A j l = true ∧ x l = true then (1 : ℕ) else 0)
                split <;> omega) (Finset.mem_univ k)
    omega
  have hrx : x r = false := hfalse r hr_mem
  have hzEq : prefixZeros A r.val x j = ((rowOnes A j).erase r).card := by
    rw [pzero_card]
    congr 1
    apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, rowOnes]
    constructor
    · rintro ⟨hklt, hkA, _⟩
      exact ⟨fun hkr => by subst hkr; exact Nat.lt_irrefl _ hklt, hkA⟩
    · rintro ⟨hkr, hkA⟩
      have hklt : k.val < r.val := by
        have hle' := hr_max k (by simp [rowOnes, hkA])
        exact lt_of_le_of_ne hle' (fun h => hkr (Fin.ext h))
      exact ⟨hklt, hkA, hfalse k (by simp [rowOnes, hkA])⟩
  have hz2 : prefixZeros A r.val x j = 2 := by
    rw [hzEq, Finset.card_erase_of_mem hr_mem, hrow j]
  have hall := hleg r r.isLt
  simp only [allowedAt, hrx, if_false] at hall
  exact hall j hrA hz2

theorem legal_of_one (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3) (x : Fin n → Bool)
    (hsum : ∀ j, rowSum A x j = 1) : legalAt A n x := by
  intro k hk
  by_cases hx : x k = true
  · simp only [allowedAt, hx, if_true]
    intro j hA
    by_contra hpos
    have hp1 : prefixSum A (k.val + 1) x j = prefixSum A k.val x j + 1 := by
      rw [psum_succ A k.val hk x j, if_pos ⟨hA, hx⟩]
    have hmono : prefixSum A k.val x j + 1 ≤ rowSum A x j := by
      rw [rowSum_eq_psum, ← hp1]
      exact psum_mono A x (Nat.succ_le_of_lt hk) j
    rw [hsum j] at hmono
    have : 1 ≤ prefixSum A k.val x j := Nat.one_le_iff_ne_zero.mpr hpos
    omega
  · have hkx : x k = false := by
      cases hxk : x k with
      | false => rfl
      | true => exact absurd hxk hx
    simp only [allowedAt, hkx, if_false]
    intro j hA hz2
    have hZsub : (Finset.univ.filter
        (fun l : Fin n => l.val < k.val ∧ A j l = true ∧ x l = false)) ⊆
        rowOnes A j := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp [rowOnes, hl.2.1]
    have hksub : k ∈ rowOnes A j := by simp [rowOnes, hA]
    have hknotZ : k ∉ Finset.univ.filter
        (fun l : Fin n => l.val < k.val ∧ A j l = true ∧ x l = false) := by
      simp
    have hcardZ : (Finset.univ.filter
        (fun l : Fin n => l.val < k.val ∧ A j l = true ∧ x l = false)).card = 2 := by
      rw [← pzero_card, hz2]
    have hunion : (Finset.univ.filter
          (fun l : Fin n => l.val < k.val ∧ A j l = true ∧ x l = false)) ∪ {k} =
        rowOnes A j := by
      apply Finset.eq_of_subset_of_card_le
      · intro l hl
        rcases Finset.mem_union.mp hl with h | h
        · exact hZsub h
        · rw [Finset.mem_singleton] at h
          subst h
          exact hksub
      · rw [Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hknotZ), hcardZ, hrow j]
        norm_num
    have hfalse : ∀ l ∈ rowOnes A j, x l = false := by
      intro l hl
      have hl' : l ∈ (Finset.univ.filter
          (fun l : Fin n => l.val < k.val ∧ A j l = true ∧ x l = false)) ∪ {k} := by
        rw [hunion]
        exact hl
      rcases Finset.mem_union.mp hl' with h | h
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h.2.2
      · rw [Finset.mem_singleton] at h
        subst h
        exact hkx
    have hzero : rowSum A x j = 0 := by
      rw [rowSum]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : A j l = true
      · have := hfalse l (by simp [rowOnes, hl])
        simp [hl, this]
      · simp [hl]
    rw [hsum j] at hzero
    exact absurd hzero (by norm_num)

theorem legal_iff_one (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3) (x : Fin n → Bool) :
    legalAt A n x ↔ ∀ j, rowSum A x j = 1 :=
  ⟨fun h j => rowSum_one A hrow x h j, fun h => legal_of_one A hrow x h⟩

theorem leaf_iff_cover (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3) :
    (∃ x : Fin n → Bool, legalAt A n x) ↔
      (∃ x : Fin n → Bool, ∀ j : Fin m, rowSum A x j = 1) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (legal_iff_one A hrow x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (legal_iff_one A hrow x).mpr hx⟩

theorem legal_succ (A : Fin m → Fin n → Bool) (x : Fin n → Bool) {i : ℕ}
    (hi : i < n) :
    legalAt A (i + 1) x ↔ legalAt A i x ∧ allowedAt A ⟨i, hi⟩ x := by
  constructor
  · intro h
    exact ⟨fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self i)),
      h ⟨i, hi⟩ (Nat.lt_succ_self i)⟩
  · rintro ⟨h1, h2⟩ k hk
    by_cases hki : k.val < i
    · exact h1 k hki
    · have hle : i ≤ k.val := Nat.le_of_not_lt hki
      have hge : k.val ≤ i := by
        have hk' : k.val < i + 1 := hk
        omega
      have hkeq : k = ⟨i, hi⟩ := Fin.ext (le_antisymm hge hle)
      rw [hkeq]
      exact h2

theorem support_card (A : Fin m → Fin n → Bool)
    (hrow : ∀ j, (rowOnes A j).card = 3)
    (hcol : ∀ i, (Finset.univ.filter (fun j : Fin m => A j i = true)).card ≤ 3)
    (i : Fin n) : (guardSupport A i).card ≤ 6 := by
  rw [guardSupport]
  refine le_trans Finset.card_biUnion_le ?_
  have hstep : ∀ j ∈ Finset.univ.filter (fun j : Fin m => A j i = true),
      ((rowOnes A j).erase i).card = 2 := by
    intro j hj
    have hji : i ∈ rowOnes A j := by
      simp [rowOnes, (Finset.mem_filter.mp hj).2]
    rw [Finset.card_erase_of_mem hji, hrow j]
  calc ∑ j ∈ Finset.univ.filter (fun j : Fin m => A j i = true),
        ((rowOnes A j).erase i).card
      = ∑ _j ∈ Finset.univ.filter (fun j : Fin m => A j i = true), (2 : ℕ) :=
        Finset.sum_congr rfl hstep
    _ = 2 * (Finset.univ.filter (fun j : Fin m => A j i = true)).card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring
    _ ≤ 2 * 3 := Nat.mul_le_mul_left 2 (hcol i)
    _ = 6 := by norm_num

theorem psum_agree (A : Fin m → Fin n → Bool) (i : Fin n) {x y : Fin n → Bool}
    (h : ∀ k ∈ guardSupport A i, x k = y k) {j : Fin m} (hA : A j i = true) :
    prefixSum A i.val x j = prefixSum A i.val y j := by
  rw [prefixSum, prefixSum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < i.val ∧ A j k = true
  · have hkS : k ∈ guardSupport A i := by
      rw [guardSupport]
      apply Finset.mem_biUnion.mpr
      refine ⟨j, ?_, ?_⟩
      · simp [hA]
      · rw [Finset.mem_erase]
        refine ⟨?_, by simp [rowOnes, hk.2]⟩
        intro hki
        subst hki
        exact absurd hk.1 (lt_irrefl _)
    have hxy := h k hkS
    by_cases hx : x k = true
    · have hy : y k = true := by rw [← hxy]; exact hx
      have hx' : k.val < i.val ∧ A j k = true ∧ x k = true := ⟨hk.1, hk.2, hx⟩
      have hy' : k.val < i.val ∧ A j k = true ∧ y k = true := ⟨hk.1, hk.2, hy⟩
      rw [if_pos hx', if_pos hy']
    · have hxf : x k = false := by
        cases hxk : x k with
        | false => rfl
        | true => exact absurd hxk hx
      have hy : ¬ (y k = true) := by
        intro hyy
        have : x k = true := by rw [hxy]; exact hyy
        exact hx this
      have hx' : ¬ (k.val < i.val ∧ A j k = true ∧ x k = true) := by
        intro hc; exact hx hc.2.2
      have hy' : ¬ (k.val < i.val ∧ A j k = true ∧ y k = true) := by
        intro hc; exact hy hc.2.2
      rw [if_neg hx', if_neg hy']
  · have h1 : ¬ (k.val < i.val ∧ A j k = true ∧ x k = true) := by tauto
    have h2 : ¬ (k.val < i.val ∧ A j k = true ∧ y k = true) := by tauto
    rw [if_neg h1, if_neg h2]

theorem pzero_eq (A : Fin m → Fin n → Bool) (i : Fin n) {x y : Fin n → Bool}
    (h : ∀ k ∈ guardSupport A i, x k = y k) {j : Fin m} (hA : A j i = true) :
    prefixZeros A i.val x j = prefixZeros A i.val y j := by
  rw [prefixZeros, prefixZeros]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < i.val ∧ A j k = true
  · have hkS : k ∈ guardSupport A i := by
      rw [guardSupport]
      apply Finset.mem_biUnion.mpr
      refine ⟨j, ?_, ?_⟩
      · simp [hA]
      · rw [Finset.mem_erase]
        refine ⟨?_, by simp [rowOnes, hk.2]⟩
        intro hki
        subst hki
        exact absurd hk.1 (lt_irrefl _)
    have hxy := h k hkS
    by_cases hx : x k = false
    · have hy : y k = false := by rw [← hxy]; exact hx
      have hx' : k.val < i.val ∧ A j k = true ∧ x k = false := ⟨hk.1, hk.2, hx⟩
      have hy' : k.val < i.val ∧ A j k = true ∧ y k = false := ⟨hk.1, hk.2, hy⟩
      rw [if_pos hx', if_pos hy']
    · have hxf : x k = true := by
        cases hxk : x k with
        | false => exact absurd hxk hx
        | true => rfl
      have hy : ¬ (y k = false) := by
        intro hyy
        have : x k = false := by rw [hxy]; exact hyy
        exact hx this
      have hx' : ¬ (k.val < i.val ∧ A j k = true ∧ x k = false) := by
        intro hc; exact hx hc.2.2
      have hy' : ¬ (k.val < i.val ∧ A j k = true ∧ y k = false) := by
        intro hc; exact hy hc.2.2
      rw [if_neg hx', if_neg hy']
  · have h1 : ¬ (k.val < i.val ∧ A j k = true ∧ x k = false) := by tauto
    have h2 : ¬ (k.val < i.val ∧ A j k = true ∧ y k = false) := by tauto
    rw [if_neg h1, if_neg h2]

theorem one_ext (A : Fin m → Fin n → Bool) (i : Fin n) {x y : Fin n → Bool}
    (h : ∀ k ∈ guardSupport A i, x k = y k) :
    allowedOne A i x ↔ allowedOne A i y := by
  constructor
  · intro hx j hA
    rw [← psum_agree A i h hA]
    exact hx j hA
  · intro hy j hA
    rw [psum_agree A i h hA]
    exact hy j hA

theorem zero_ext (A : Fin m → Fin n → Bool) (i : Fin n) {x y : Fin n → Bool}
    (h : ∀ k ∈ guardSupport A i, x k = y k) :
    allowedZero A i x ↔ allowedZero A i y := by
  constructor <;> intro hg j hA
  · rw [← pzero_eq A i h hA]
    exact hg j hA
  · rw [pzero_eq A i h hA]
    exact hg j hA

end Qatlib.Papers.DecisionTrees97.MainResults.ExactCoverGuards
