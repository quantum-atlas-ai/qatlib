/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.ProductIsomorphism
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Splitting subgroups of products of coprime order

This module proves the subgroup decomposition underlying the direct-product reduction in
[CosmePortugal2007]. A subgroup of a product of finite groups with coprime orders contains each
separate coordinate of each of its elements and consequently equals the product of its two
projected subgroups.

The results are specialized to `Cyc (q ^ s) × SDG p r ψ`, whose factor orders are coprime when
`p` and `q` are distinct primes and `s` is positive.

## Main statements

* `fst_mem_of_coprime` and `snd_mem_of_coprime` extract the separate coordinates of a subgroup
  element.
- `subgroup_eq_prod_of_coprime_card` proves the general subgroup splitting theorem.
* `coprime_card_cyc_sdg` verifies the order condition, and `source_factor_split` gives the
  specialized splitting.

## References

* [Cosme and Portugal, 2007][CosmePortugal2007]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

/-- The first coordinate of a natural power in a product of monoids is the same power of the
first coordinate. -/
theorem prod_pow_fst {A B : Type*} [Monoid A] [Monoid B] (x : A × B) (n : ℕ) :
    (x ^ n).1 = x.1 ^ n :=
  map_pow (MonoidHom.fst A B) x n

/-- The second coordinate of a natural power in a product of monoids is the same power of the
second coordinate. -/
theorem prod_pow_snd {A B : Type*} [Monoid A] [Monoid B] (x : A × B) (n : ℕ) :
    (x ^ n).2 = x.2 ^ n :=
  map_pow (MonoidHom.snd A B) x n

/-- If `Nat.card A` and `Nat.card B` are coprime and `B` is finite, membership of `(a, b)` in a
subgroup of `A × B` implies membership of `(a, 1)`. -/
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

/-- If `Nat.card A` and `Nat.card B` are coprime and `A` is finite, membership of `(a, b)` in a
subgroup of `A × B` implies membership of `(1, b)`. -/
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

/-- Every subgroup of a product of finite groups of coprime orders equals the product of its
images under the two coordinate projections [CosmePortugal2007]. -/
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

/-- For distinct primes `p` and `q` and positive `s`, the cardinalities of `Cyc (q ^ s)` and
`SDG p r ψ` are coprime [CosmePortugal2007]. -/
theorem coprime_card_cyc_sdg (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hs : 0 < s) (hne : p ≠ q)
    (ψ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) :
    Nat.Coprime (Nat.card (Cyc (q ^ s))) (Nat.card (SDG p r ψ)) := by
  rw [card_Cyc, card_SDG_prime_pow p r hp ψ]
  have hpq : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hne)
  refine (Nat.coprime_pow_left_iff hs q (p ^ (r + 2))).mpr ?_
  exact (Nat.coprime_pow_right_iff (Nat.succ_pos (r + 1)) q p).mpr hpq

/-- For distinct primes `p` and `q` and positive `s`, every subgroup of `Cyc (q ^ s) × SDG p r
ψ` is the product of its two projected subgroups [CosmePortugal2007]. -/
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
