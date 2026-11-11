/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.SetLike.Fintype
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Minimal
import Mathlib.Tactic

/-!
# Counting subgroups and bounding query parameters

This module bounds the size of minimal generating sets and the number of subgroups of a finite
group using integer binary logarithms. These estimates control `exactQueryCountFloored` and the
depth of a binary candidate tree. This develops part of the framework of
[EttingerHoyerKnill2004].

## Main statements

* `exists_generating_finset_card_le_log2`: bounds the number of generators by `log2 |G|`.
* `card_subgroups_le_two_pow`: bounds the number of subgroups by a power of two.
* `exactQueryCountFloored_le`: gives a fourth-degree bound in the binary logarithm of the group
  order.

## References

* [Ettinger et al., 2004][EttingerHoyerKnill2004]
-/

set_option autoImplicit false

namespace Qatlib.Papers.EttingerHSP04.MainResults

open scoped BigOperators

/-- Adjoining an element outside a finite subgroup generates a subgroup with at least twice its
cardinality. See [EttingerHoyerKnill2004]. -/
theorem two_mul_card_le_card_closure_insert {G : Type*} [Group G] [Fintype G]
    (K : Subgroup G) (x : G) (hx : x ∉ K) :
    2 * Nat.card K ≤ Nat.card (Subgroup.closure (insert x (K : Set G))) := by
  classical
  let C : Subgroup G := Subgroup.closure (insert x (K : Set G))
  have hKC : K ≤ C := by
    rw [← Subgroup.closure_eq (K := K)]
    exact Subgroup.closure_mono (fun y hy => Or.inr hy)
  have hxC : x ∈ C := Subgroup.subset_closure (Or.inl rfl)
  let f : K × Bool → C := fun p =>
    match p.2 with
    | false => ⟨(p.1 : G), hKC p.1.2⟩
    | true => ⟨x * (p.1 : G), C.mul_mem hxC (hKC p.1.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨k₁, b₁⟩ ⟨k₂, b₂⟩ h
    cases b₁ <;> cases b₂
    · have hk : (k₁ : G) = (k₂ : G) := congrArg (fun z : C => (z : G)) h
      exact Prod.ext (Subtype.ext hk) rfl
    · have hk : (k₁ : G) = x * (k₂ : G) := congrArg (fun z : C => (z : G)) h
      exfalso
      apply hx
      have hxeq : x = (k₁ : G) * (k₂ : G)⁻¹ := by
        rw [hk, mul_inv_cancel_right]
      rw [hxeq]
      exact K.mul_mem k₁.2 (K.inv_mem k₂.2)
    · have hk : x * (k₁ : G) = (k₂ : G) := congrArg (fun z : C => (z : G)) h
      exfalso
      apply hx
      have hxeq : x = (k₂ : G) * (k₁ : G)⁻¹ := by
        rw [← hk, mul_inv_cancel_right]
      rw [hxeq]
      exact K.mul_mem k₂.2 (K.inv_mem k₁.2)
    · have hk : x * (k₁ : G) = x * (k₂ : G) := congrArg (fun z : C => (z : G)) h
      exact Prod.ext (Subtype.ext (mul_left_cancel hk)) rfl
  have hcard := Fintype.card_le_of_injective f hf
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa [C, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using hcard

/-- A minimal finite generating set of cardinality `k` generates a subgroup with at least `2 ^
k` elements. -/
theorem pow_card_le_card_of_minimal {G : Type*} [Group G] [Fintype G]
    (S : Finset G)
    (hmin : Minimal (fun T : Finset G =>
      Subgroup.closure (T : Set G) = Subgroup.closure (S : Set G)) S) :
    2 ^ S.card ≤ Nat.card (Subgroup.closure (S : Set G)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [Subgroup.closure_empty]
  | insert a s ha ih =>
      let H : Subgroup G := Subgroup.closure (insert a (s : Set G))
      let K : Subgroup G := Subgroup.closure (s : Set G)
      have hKH : K ≤ H :=
        Subgroup.closure_mono (fun y hy => Or.inr hy)
      have haK : a ∉ K := by
        intro haK
        have hHK : H ≤ K := by
          change Subgroup.closure (insert a (s : Set G)) ≤ Subgroup.closure (s : Set G)
          rw [Subgroup.closure_le]
          intro y hy
          rcases hy with rfl | hys
          · exact haK
          · exact Subgroup.subset_closure hys
        have hEq : Subgroup.closure (insert a (s : Set G)) = K := le_antisymm hHK hKH
        have hPs : (fun T : Finset G => Subgroup.closure (T : Set G) =
            Subgroup.closure ((insert a s : Finset G) : Set G)) s := by
          simp only [Finset.coe_insert]
          simpa only [K] using hEq.symm
        have hsub : insert a s ⊆ s := hmin.2 hPs (Finset.subset_insert a s)
        exact ha (hsub (Finset.mem_insert_self a s))
      have hmin_s : Minimal (fun T : Finset G =>
          Subgroup.closure (T : Set G) = Subgroup.closure (s : Set G)) s := by
        refine ⟨rfl, ?_⟩
        intro T hT hTs
        have hTsub : insert a T ⊆ insert a s := Finset.insert_subset_insert a hTs
        have hgen : Subgroup.closure ((insert a T : Finset G) : Set G) =
            Subgroup.closure ((insert a s : Finset G) : Set G) := by
          rw [Finset.coe_insert, Finset.coe_insert]
          apply le_antisymm
          · rw [Subgroup.closure_le]
            intro y hy
            rcases hy with rfl | hyT
            · exact Subgroup.subset_closure (Or.inl rfl)
            · exact Subgroup.subset_closure (Or.inr (hTs hyT))
          · rw [Subgroup.closure_le]
            intro y hy
            rcases hy with rfl | hys
            · exact Subgroup.subset_closure (Or.inl rfl)
            · have hyT' : y ∈ Subgroup.closure (T : Set G) := by
                rw [hT]
                exact Subgroup.subset_closure hys
              exact Subgroup.closure_mono (fun z hz => Or.inr hz) hyT'
        have hsub := hmin.2 hgen hTsub
        intro y hy
        have hy' : y ∈ insert a T := hsub (Finset.mem_insert_of_mem hy)
        rcases Finset.mem_insert.mp hy' with rfl | hyT
        · exact absurd hy ha
        · exact hyT
      have hIH : 2 ^ s.card ≤ Nat.card K := ih hmin_s
      have hclosure_congr :
          Subgroup.closure (insert a (K : Set G)) = Subgroup.closure (insert a (s : Set G)) := by
        apply le_antisymm
        · change Subgroup.closure (insert a (K : Set G)) ≤
            Subgroup.closure (insert a (s : Set G))
          rw [Subgroup.closure_le]
          intro y hy
          rcases hy with rfl | hyK
          · exact Subgroup.subset_closure (Or.inl rfl)
          · exact Subgroup.closure_mono (fun z hz => Or.inr hz) hyK
        · change Subgroup.closure (insert a (s : Set G)) ≤
            Subgroup.closure (insert a (K : Set G))
          rw [Subgroup.closure_le]
          intro y hy
          rcases hy with rfl | hys
          · exact Subgroup.subset_closure (Or.inl rfl)
          · exact Subgroup.subset_closure (Or.inr (Subgroup.subset_closure hys))
      have hdouble : 2 * Nat.card K ≤ Nat.card H := by
        have h := two_mul_card_le_card_closure_insert K a haK
        rwa [hclosure_congr] at h
      calc 2 ^ (insert a s).card = 2 * 2 ^ s.card := by
              rw [Finset.card_insert_of_notMem ha, pow_succ, Nat.mul_comm]
        _ ≤ 2 * Nat.card K := Nat.mul_le_mul_left 2 hIH
        _ ≤ Nat.card (Subgroup.closure ((insert a s : Finset G) : Set G)) := by
              simpa only [H, Finset.coe_insert] using hdouble

/-- Every subgroup of a finite group has a finite generating set of size at most the integer
binary logarithm of the ambient group order. See [EttingerHoyerKnill2004]. -/
theorem exists_generating_finset_card_le_log2 {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = H ∧ S.card ≤ (Fintype.card G).log2 := by
  classical
  have hex : ∃ S : Finset G, Subgroup.closure (S : Set G) = H := by
    refine ⟨Finset.univ.filter (fun g => g ∈ H), ?_⟩
    have hcoe : ((Finset.univ.filter (fun g => g ∈ H) : Finset G) : Set G) = (H : Set G) := by
      ext g
      simp
    rw [hcoe, Subgroup.closure_eq]
  obtain ⟨S, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun S : Finset G => Subgroup.closure (S : Set G) = H) hex
  have hcard : 2 ^ S.card ≤ Nat.card H := by
    have h := pow_card_le_card_of_minimal S (by simpa only [← hmin.prop] using hmin)
    rwa [hmin.prop] at h
  have hNG : Nat.card H ≤ Fintype.card G := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  refine ⟨S, hmin.prop, ?_⟩
  have hG : Fintype.card G ≠ 0 := by
    have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
    exact Nat.pos_iff_ne_zero.mp hpos
  exact (Nat.le_log2 hG).mpr (hcard.trans hNG)

/-- The number of subgroups is at most `(log2 |G| + 1) * |G| ^ log2 |G|`. -/
theorem card_subgroups_le {G : Type*} [Group G] [Fintype G] :
    Fintype.card (Subgroup G) ≤
      ((Fintype.card G).log2 + 1) * (Fintype.card G) ^ (Fintype.card G).log2 := by
  classical
  set N := Fintype.card G with hN
  set m := N.log2 with hm
  let gen : Subgroup G → Finset G := fun H =>
    Classical.choose (exists_generating_finset_card_le_log2 H)
  have hgen : ∀ H : Subgroup G,
      Subgroup.closure ((gen H : Finset G) : Set G) = H ∧ (gen H).card ≤ m := by
    intro H
    exact Classical.choose_spec (exists_generating_finset_card_le_log2 H)
  let A : Finset (Finset G) := Finset.univ.filter (fun S => S.card ≤ m)
  have hinj : Function.Injective (fun H : Subgroup G =>
      (⟨gen H, by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hgen H).2⟩ : A)) := by
    intro H₁ H₂ heq
    have hg : gen H₁ = gen H₂ := congrArg Subtype.val heq
    rw [← (hgen H₁).1, ← (hgen H₂).1, hg]
  have hcard1 : Fintype.card (Subgroup G) ≤ A.card := by
    have h := Fintype.card_le_of_injective _ hinj
    simpa using h
  have hAsub : A ⊆ (Finset.range (m + 1)).biUnion
      (fun k => Finset.powersetCard k (Finset.univ : Finset G)) := by
    intro S hS
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [Finset.mem_biUnion]
    exact ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hS),
      by rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ S, rfl⟩⟩
  have hNpos : 0 < N := by
    rw [hN]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hAcard : A.card ≤ (m + 1) * N ^ m := by
    calc A.card ≤ ((Finset.range (m + 1)).biUnion
          (fun k => Finset.powersetCard k (Finset.univ : Finset G))).card :=
          Finset.card_le_card hAsub
      _ ≤ (Finset.range (m + 1)).card * N ^ m := by
          apply Finset.card_biUnion_le_card_mul
          intro k hk
          rw [Finset.card_powersetCard, Finset.card_univ]
          have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          show Nat.choose N k ≤ N ^ m
          exact (Nat.choose_le_pow N k).trans (Nat.pow_le_pow_right hNpos hk')
      _ = (m + 1) * N ^ m := by simp
  calc Fintype.card (Subgroup G) ≤ A.card := hcard1
    _ ≤ (m + 1) * N ^ m := hAcard
    _ = ((Fintype.card G).log2 + 1) * (Fintype.card G) ^ (Fintype.card G).log2 := by
        simp [hN, hm]

/-- The number of subgroups is at most `2 ^ ((log2 |G| + 1) * (log2 |G| + 2))`. See
[EttingerHoyerKnill2004]. -/
theorem card_subgroups_le_two_pow {G : Type*} [Group G] [Fintype G] :
    Fintype.card (Subgroup G) ≤
      2 ^ (((Fintype.card G).log2 + 1) * ((Fintype.card G).log2 + 2)) := by
  classical
  set N := Fintype.card G with hN
  set m := N.log2 with hm
  have hNpos : 0 < N := by
    rw [hN]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hNne : N ≠ 0 := Nat.pos_iff_ne_zero.mp hNpos
  have hNlt : N < 2 ^ (m + 1) :=
    (Nat.log2_lt hNne).mp (Nat.lt_succ_self m)
  have hNm : N ^ m ≤ 2 ^ (m * (m + 1)) := by
    calc N ^ m ≤ (2 ^ (m + 1)) ^ m := Nat.pow_le_pow_left (Nat.le_of_lt hNlt) m
      _ = 2 ^ ((m + 1) * m) := by rw [← pow_mul]
      _ = 2 ^ (m * (m + 1)) := by rw [Nat.mul_comm]
  have hm1 : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hbase : Fintype.card (Subgroup G) ≤ (m + 1) * N ^ m := by
    simpa only [hN, hm] using card_subgroups_le (G := G)
  calc Fintype.card (Subgroup G) ≤ (m + 1) * N ^ m := hbase
    _ ≤ (m + 1) * 2 ^ (m * (m + 1)) := Nat.mul_le_mul_left _ hNm
    _ ≤ 2 ^ m * 2 ^ (m * (m + 1)) := Nat.mul_le_mul_right _ hm1
    _ = 2 ^ (m + m * (m + 1)) := by rw [← pow_add]
    _ = 2 ^ (m * (m + 2)) := by ring
    _ ≤ 2 ^ ((m + 1) * (m + 2)) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith

/-- The integer query parameter `2 * log2 (4 * r ^ 3) * (log2 r + 1)`. -/
noncomputable def exactQueryCountFloored (r : Nat) : Nat :=
  (2 * (4 * r ^ 3).log2) * (r.log2 + 1)

/-- At the number of subgroups of `G`, the query parameter is at most `64 * (log2 |G| + 1) ^ 4`.
See [EttingerHoyerKnill2004]. -/
theorem exactQueryCountFloored_le {G : Type*} [Group G] [Fintype G] :
    exactQueryCountFloored (Fintype.card (Subgroup G)) ≤
      64 * ((Fintype.card G).log2 + 1) ^ 4 := by
  classical
  set N := Fintype.card G with hN
  set m := N.log2 with hm
  set B := (m + 1) * (m + 2) with hBdef
  set r := Fintype.card (Subgroup G) with hrdef
  have hrB : r ≤ 2 ^ B := by
    have h := card_subgroups_le_two_pow (G := G)
    simpa only [hN, hm, hBdef, hrdef] using h
  have hrne : r ≠ 0 := by
    rw [hrdef]
    exact Fintype.card_ne_zero (α := Subgroup G)
  have hlogr : r.log2 ≤ B := by
    have hltB : r.log2 < B + 1 :=
      (Nat.log2_lt hrne).mpr
        (lt_of_le_of_lt hrB (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self B)))
    omega
  have hr3 : r ^ 3 ≤ 2 ^ (3 * B) := by
    calc r ^ 3 ≤ (2 ^ B) ^ 3 := Nat.pow_le_pow_left hrB 3
      _ = 2 ^ (B * 3) := by rw [← pow_mul]
      _ = 2 ^ (3 * B) := by rw [Nat.mul_comm]
  have hlt : 4 * r ^ 3 < 2 ^ (3 * B + 3) := by
    have h4 : 4 * r ^ 3 ≤ 4 * 2 ^ (3 * B) := Nat.mul_le_mul_left 4 hr3
    have h4' : 4 * 2 ^ (3 * B) = 2 ^ (3 * B + 2) := by
      calc 4 * 2 ^ (3 * B) = 2 ^ 2 * 2 ^ (3 * B) := by norm_num
        _ = 2 ^ (2 + 3 * B) := by rw [← pow_add]
        _ = 2 ^ (3 * B + 2) := by rw [Nat.add_comm]
    rw [h4'] at h4
    exact lt_of_le_of_lt h4 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hlog4 : (4 * r ^ 3).log2 ≤ 3 * B + 2 := by
    have h := (Nat.log2_lt (n := 4 * r ^ 3)
      (Nat.mul_ne_zero (by norm_num) (pow_ne_zero 3 hrne))).mpr hlt
    omega
  have hs : exactQueryCountFloored r ≤ (6 * B + 4) * (B + 1) := by
    unfold exactQueryCountFloored
    have h1 : 2 * (4 * r ^ 3).log2 ≤ 2 * (3 * B + 2) := Nat.mul_le_mul_left 2 hlog4
    have h2 : r.log2 + 1 ≤ B + 1 := Nat.add_le_add_right hlogr 1
    exact Nat.mul_le_mul (by omega) h2
  have hB : B ≤ 2 * (m + 1) ^ 2 := by
    rw [hBdef]
    nlinarith
  have hfinal : (6 * B + 4) * (B + 1) ≤ 64 * (m + 1) ^ 4 := by
    nlinarith [hB]
  exact hs.trans hfinal

/-- For every candidate count `r`, some depth at most `r.log2 + 1` has binary capacity at least
`r`. See [EttingerHoyerKnill2004]. -/
theorem candidate_tree_depth (r : Nat) : ∃ k ≤ r.log2 + 1, r ≤ 2 ^ k :=
  ⟨r.log2 + 1, le_rfl, le_of_lt Nat.lt_log2_self⟩

end Qatlib.Papers.EttingerHSP04.MainResults
