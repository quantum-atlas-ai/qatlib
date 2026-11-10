/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.FiniteRing09.MainResults.IterationCost

theorem strict_chain_doubling
    {A : Type*} [AddCommGroup A] [Finite A]
    {B C : AddSubgroup A} (hBC : B < C) :
    2 * Nat.card B ≤ Nat.card C := by
  have hle : B ≤ C := hBC.le
  let K : AddSubgroup C := B.comap C.subtype
  have hKtop : K ≠ ⊤ := by
    intro htop
    apply hBC.2
    intro x hx
    have hxC : x ∈ C := hx
    have hxK : (⟨x, hxC⟩ : C) ∈ K := by
      rw [htop]
      simp
    have hmem : ((⟨x, hxC⟩ : C) : A) ∈ B := AddSubgroup.mem_comap.mp hxK
    simpa using hmem
  haveI : Finite C := Subtype.finite
  haveI : Finite (C ⧸ K) := inferInstance
  have hidx : 1 < K.index := AddSubgroup.one_lt_index_of_ne_top hKtop
  have hcard : Nat.card K * K.index = Nat.card C := K.card_mul_index
  have hcardK : Nat.card K = Nat.card B :=
    Nat.card_congr
      { toFun := fun x => (⟨(x.1 : A), x.2⟩ : B)
        invFun := fun y => (⟨⟨(y.1 : A), hle y.2⟩, y.2⟩ : K)
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
  calc 2 * Nat.card B = Nat.card B * 2 := Nat.mul_comm 2 (Nat.card B)
    _ ≤ Nat.card B * K.index := Nat.mul_le_mul_left _ hidx
    _ = Nat.card K * K.index := by rw [hcardK]
    _ = Nat.card C := hcard

theorem chain_length_bound
    {A : Type*} [AddCommGroup A] [Finite A]
    (B : ℕ → AddSubgroup A) (n : ℕ)
    (hstrict : ∀ k < n, B k < B (k + 1)) :
    2 ^ n * Nat.card (B 0) ≤ Nat.card (B n) := by
  revert hstrict
  induction n with
  | zero =>
      intro _hstrict
      simp
  | succ n ih =>
      intro hstrict
      have hprev : ∀ k < n, B k < B (k + 1) := by
        intro k hk
        exact hstrict k (Nat.lt_succ_of_lt hk)
      have hchain := ih hprev
      have hstep : 2 * Nat.card (B n) ≤ Nat.card (B (n + 1)) :=
          strict_chain_doubling (hstrict n (Nat.lt_succ_self n))
      calc 2 ^ (n + 1) * Nat.card (B 0) = (2 ^ n * 2) * Nat.card (B 0) := by
            rw [pow_succ]
        _ = 2 * (2 ^ n * Nat.card (B 0)) := by ring
        _ ≤ 2 * Nat.card (B n) := Nat.mul_le_mul_left 2 hchain
        _ ≤ Nat.card (B (n + 1)) := hstep

theorem iterations_le_log_card
    {A : Type*} [AddCommGroup A] [Finite A]
    (B : ℕ → AddSubgroup A) (n : ℕ)
    (hstrict : ∀ k < n, B k < B (k + 1)) :
    n ≤ Nat.log 2 (Nat.card A) := by
  have hchain := chain_length_bound B n hstrict
  haveI : Nonempty (B 0) := ⟨0⟩
  have hpos : 0 < Nat.card (B 0) := Nat.card_pos
  have h2 : 2 ^ n ≤ Nat.card (B n) := by
    calc 2 ^ n = 2 ^ n * 1 := by simp
      _ ≤ 2 ^ n * Nat.card (B 0) := Nat.mul_le_mul_left _ hpos
      _ ≤ Nat.card (B n) := hchain
  have h3 : Nat.card (B n) ≤ Nat.card A :=
    Nat.card_le_card_of_injective (f := fun x : B n => (x : A))
      (fun _ _ h => Subtype.ext h)
  have hA : Nat.card A ≠ 0 := Nat.card_pos.ne'
  exact (Nat.le_log_iff_pow_le (by norm_num) hA).mpr (le_trans h2 h3)

theorem trials_per_step
    {R : Type*} [DecidableEq R] (Rs Bt : Finset R) :
    (Rs.product Bt).card = Rs.card * Bt.card :=
  Finset.card_product Rs Bt

theorem generator_set_card_bound
    {R : Type*} [DecidableEq R] (Bt : ℕ → Finset R) (m : ℕ)
    (hInit : (Bt 0).card = m) (hstep : ∀ k, (Bt (k + 1)).card ≤ (Bt k).card + 1)
    (n : ℕ) : (Bt n).card ≤ m + n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have := hstep n
    omega

theorem total_trial_cost_polynomial
    {R : Type*} [Fintype R] [DecidableEq R]
    (Rs : Finset R) (m n : ℕ)
    (hn : n ≤ Nat.log 2 (Fintype.card R)) :
    (∑ k ∈ Finset.range n, Rs.card * (m + k))
      ≤ (Nat.log 2 (Fintype.card R) + 1) * Rs.card * (m + Nat.log 2 (Fintype.card R)) := by
  set L := Nat.log 2 (Fintype.card R)
  have hterm : ∀ k ∈ Finset.range n, Rs.card * (m + k) ≤ Rs.card * (m + L) := by
    intro k hk
    have hkL : k ≤ L :=
      le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hn
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hkL m)
  have hsum : (∑ k ∈ Finset.range n, Rs.card * (m + k))
      ≤ ∑ _k ∈ Finset.range n, Rs.card * (m + L) := Finset.sum_le_sum hterm
  have hconst : (∑ _k ∈ Finset.range n, Rs.card * (m + L))
      = n * (Rs.card * (m + L)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp
  rw [hconst] at hsum
  calc (∑ k ∈ Finset.range n, Rs.card * (m + k))
      ≤ n * (Rs.card * (m + L)) := hsum
    _ ≤ (L + 1) * (Rs.card * (m + L)) :=
        Nat.mul_le_mul_right _ (Nat.le_succ_of_le hn)
    _ = (L + 1) * Rs.card * (m + L) := by ring

theorem total_trial_cost_polynomial_in_log
    {R : Type*} [Fintype R] [DecidableEq R]
    (Rs : Finset R) (m n : ℕ)
    (hn : n ≤ Nat.log 2 (Fintype.card R))
    (hRs : Rs.card ≤ Nat.log 2 (Fintype.card R))
    (hm : m ≤ Nat.log 2 (Fintype.card R)) :
    (∑ k ∈ Finset.range n, Rs.card * (m + k))
      ≤ 2 * (Nat.log 2 (Fintype.card R) + 1) ^ 3 := by
  have hpoly := total_trial_cost_polynomial Rs m n hn
  set L := Nat.log 2 (Fintype.card R)
  have hmL : m + L ≤ 2 * (L + 1) := by omega
  have hRs1 : Rs.card ≤ L + 1 := Nat.le_succ_of_le hRs
  have h1 : Rs.card * (m + L) ≤ (L + 1) * (2 * (L + 1)) :=
    Nat.mul_le_mul hRs1 hmL
  have h2 : (L + 1) * (Rs.card * (m + L)) ≤ (L + 1) * ((L + 1) * (2 * (L + 1))) :=
    Nat.mul_le_mul_left _ h1
  have h3 : (L + 1) * ((L + 1) * (2 * (L + 1))) = 2 * (L + 1) ^ 3 := by ring
  calc (∑ k ∈ Finset.range n, Rs.card * (m + k))
      ≤ (L + 1) * Rs.card * (m + L) := by
        simpa [L, Nat.mul_assoc] using hpoly
    _ = (L + 1) * (Rs.card * (m + L)) := by ring
    _ ≤ (L + 1) * ((L + 1) * (2 * (L + 1))) := h2
    _ = 2 * (L + 1) ^ 3 := h3

end Qatlib.Papers.FiniteRing09.MainResults.IterationCost
