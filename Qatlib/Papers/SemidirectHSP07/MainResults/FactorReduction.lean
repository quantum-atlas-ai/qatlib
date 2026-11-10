/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.ProductIsomorphism
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

theorem prod_pow_fst {A B : Type*} [Monoid A] [Monoid B] (x : A × B) (n : ℕ) :
    (x ^ n).1 = x.1 ^ n :=
  map_pow (MonoidHom.fst A B) x n

theorem prod_pow_snd {A B : Type*} [Monoid A] [Monoid B] (x : A × B) (n : ℕ) :
    (x ^ n).2 = x.2 ^ n :=
  map_pow (MonoidHom.snd A B) x n

theorem fst_mem_of_coprime
    {A B : Type*} [Group A] [Group B] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (H : Subgroup (A × B)) {a : A} {b : B} (h : (a, b) ∈ H) : (a, 1) ∈ H := by
  have hpow_eq : ((a, 1) : A × B) ^ Nat.card B = (a, b) ^ Nat.card B := by
    apply Prod.ext
    · rw [prod_pow_fst, prod_pow_fst]
    · rw [prod_pow_snd, prod_pow_snd]
      simp [pow_card_eq_one']
  have hpow : ((a, 1) : A × B) ^ Nat.card B ∈ H := by
    rw [hpow_eq]
    exact H.pow_mem h _
  have hmem : ((a, 1) : A × B) ∈
      Subgroup.zpowers (((a, 1) : A × B) ^ Nat.card B) := by
    rw [mem_zpowers_pow_iff]
    rw [show orderOf ((a, 1) : A × B) = orderOf a by
      rw [Prod.orderOf_mk]
      simp]
    exact hcop.symm.coprime_dvd_right (orderOf_dvd_natCard a)
  exact Subgroup.zpowers_le.mpr hpow hmem

theorem snd_mem_of_coprime
    {A B : Type*} [Group A] [Group B] [Finite A]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (H : Subgroup (A × B)) {a : A} {b : B} (h : (a, b) ∈ H) : (1, b) ∈ H := by
  have hpow_eq : ((1, b) : A × B) ^ Nat.card A = (a, b) ^ Nat.card A := by
    apply Prod.ext
    · rw [prod_pow_fst, prod_pow_fst]
      simp [pow_card_eq_one']
    · rw [prod_pow_snd, prod_pow_snd]
  have hpow : ((1, b) : A × B) ^ Nat.card A ∈ H := by
    rw [hpow_eq]
    exact H.pow_mem h _
  have hmem : ((1, b) : A × B) ∈
      Subgroup.zpowers (((1, b) : A × B) ^ Nat.card A) := by
    rw [mem_zpowers_pow_iff]
    rw [show orderOf ((1, b) : A × B) = orderOf b by
      rw [Prod.orderOf_mk]
      simp]
    exact hcop.coprime_dvd_right (orderOf_dvd_natCard b)
  exact Subgroup.zpowers_le.mpr hpow hmem

theorem subgroup_eq_prod_of_coprime_card
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) (H : Subgroup (A × B)) :
    H = (H.map (MonoidHom.fst A B)).prod (H.map (MonoidHom.snd A B)) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_prod]
    exact ⟨Subgroup.mem_map_of_mem _ hx, Subgroup.mem_map_of_mem _ hx⟩
  · intro hx
    rw [Subgroup.mem_prod] at hx
    obtain ⟨ha, hb⟩ := hx
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨⟨a₁, b₁⟩, h₁, ha_eq⟩ := ha
    obtain ⟨⟨a₂, b₂⟩, h₂, hb_eq⟩ := hb
    have hx1 : x.1 = a₁ := ha_eq.symm
    have hx2 : x.2 = b₂ := hb_eq.symm
    have hxeq : x = (a₁, b₂) := Prod.ext hx1 hx2
    rw [hxeq]
    have hfst : (a₁, 1) ∈ H := fst_mem_of_coprime hcop H h₁
    have hsnd : (1, b₂) ∈ H := snd_mem_of_coprime hcop H h₂
    have hmul := H.mul_mem hfst hsnd
    simpa using hmul

theorem coprime_card_cyc_sdg (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hs : 0 < s) (hne : p ≠ q)
    (ψ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nat.Coprime (Nat.card (Cyc (q ^ s))) (Nat.card (SDG p r ψ)) := by
  rw [card_Cyc, card_SDG_prime_pow p r hp ψ]
  have hpq : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hne)
  refine (Nat.coprime_pow_left_iff hs q (p ^ (r + 2))).mpr ?_
  exact (Nat.coprime_pow_right_iff (Nat.succ_pos (r + 1)) q p).mpr hpq

theorem source_factor_split (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hs : 0 < s) (hne : p ≠ q)
    (ψ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r)))
    (H : Subgroup (Cyc (q ^ s) × SDG p r ψ)) :
    H = (H.map (MonoidHom.fst _ _)).prod (H.map (MonoidHom.snd _ _)) := by
  haveI : NeZero (q ^ s) := ⟨pow_ne_zero s hq.ne_zero⟩
  haveI : Finite (Cyc (q ^ s)) := Finite.of_fintype _
  haveI : Finite (SDG p r ψ) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_SDG_prime_pow p r hp ψ]
      exact pow_ne_zero _ hp.ne_zero)
  exact subgroup_eq_prod_of_coprime_card (coprime_card_cyc_sdg p q r s hp hq hs hne ψ) H

end Qatlib.Papers.SemidirectHSP07.MainResults
