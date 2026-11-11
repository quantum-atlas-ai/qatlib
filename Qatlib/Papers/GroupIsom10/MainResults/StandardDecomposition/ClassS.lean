/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

set_option autoImplicit false

/-!
# Groups in the class `S` and standard decompositions

Source: François Le Gall, *An Efficient Quantum Algorithm for some Instances of the Group
Isomorphism Problem*, arXiv:1001.0608v1 (2010).

This file contains the paper-level definitions of the class `S` (Definition 1.1, p.2)
and of the sets `D_G^m` / standard decompositions (Definition 2.1, p.4), together with
the structural lemmas about them that the proofs of Lemma 3.1 and Lemma 3.2 use:

* `InD.inf_zpowers_eq_bot` — the abelian part and the cyclic part of a standard
  decomposition meet trivially (their orders are coprime);
* `InD.exists_decomp` — every element of `G` is `a * y ^ n` with `a ∈ A`;
* `InD.commutator_le` — the derived subgroup `G'` is contained in `A`.

All statements are in the paper's multiplicative notation.  The only translation is that
`B = ⟨y⟩` is written `Subgroup.zpowers y` and `G = A B` is written `A ⊔ Subgroup.zpowers y = ⊤`.
-/

namespace Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition

/-- A natural number is a **prime power** when it has the form `p ^ k` with `p` prime and
`k ≥ 1`.  (Lemma 3.1 and Lemma 3.2 speak of elements "of prime power order".) -/
def IsPrimePower (n : ℕ) : Prop := ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k

/-- `(A, ⟨y⟩) ∈ D_G^m` (Definition 2.1, p.4 of arXiv:1001.0608v1):

* `A` is a normal abelian subgroup of `G`;
* `A` has order coprime with `m`;
* `B = ⟨y⟩` is a cyclic subgroup of order `m`;
* `G = A B`.

The paper writes `D_G^m` for the set (possibly empty) of such pairs.  `m` is required to be
a positive integer, as in Definition 2.1. -/
structure InD {G : Type*} [Group G] (A : Subgroup G) (y : G) (m : ℕ) : Prop where
  /-- `m` is a positive integer (Definition 2.1 quantifies over positive `m`). -/
  m_pos : 0 < m
  /-- `A` is a normal subgroup of `G`. -/
  normal : A.Normal
  /-- `A` is abelian. -/
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  /-- The order of `A` is coprime with `m`. -/
  coprime : Nat.Coprime (Nat.card A) m
  /-- The subgroup `⟨y⟩` has order `m`. -/
  order_y : orderOf y = m
  /-- `G = A B` with `B = ⟨y⟩`. -/
  sup_eq_top : A ⊔ Subgroup.zpowers y = ⊤

/-- `G` is a group **in the class `S`** (Definition 1.1, p.2): there is a normal abelian
subgroup `A` and an element `y` of order coprime with `|A|` with `G = ⟨A, y⟩`. -/
def InClassS (G : Type*) [Group G] : Prop := ∃ (A : Subgroup G) (y : G) (m : ℕ), InD A y m

section Structural

variable {G : Type*} [Group G] {A : Subgroup G} {y : G} {m : ℕ}

/-- In a standard decomposition the abelian part `A` and the cyclic part `⟨y⟩` meet
trivially: any common element has order dividing both `|A|` and `m`, which are coprime. -/
lemma InD.inf_zpowers_eq_bot (hD : InD A y m) : A ⊓ Subgroup.zpowers y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxA, hxy⟩ := hx
  have hdvdA : orderOf x ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hxA
  have hdvdY : orderOf x ∣ orderOf y := orderOf_dvd_of_mem_zpowers hxy
  have hg : orderOf x ∣ Nat.gcd (Nat.card A) m := by
    rw [hD.order_y] at hdvdY
    exact Nat.dvd_gcd hdvdA hdvdY
  rw [hD.coprime] at hg
  have h1 : orderOf x = 1 := Nat.dvd_one.mp hg
  simpa [orderOf_eq_one_iff] using h1

/-- Every element of a group carrying a standard decomposition is of the form `a * y ^ n`
with `a ∈ A` and `n : ℕ`.  This is the paper's use of `G = A B`. -/
lemma InD.exists_decomp (hD : InD A y m) (g : G) :
    ∃ a ∈ A, ∃ n : ℕ, a * y ^ n = g := by
  haveI : A.Normal := hD.normal
  have hmem : g ∈ (↑(A ⊔ Subgroup.zpowers y) : Set G) := by
    rw [hD.sup_eq_top]; exact Subgroup.mem_top g
  rw [Subgroup.normal_mul] at hmem
  rw [Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨a, ha, (k % (m : ℤ)).toNat, ?_⟩
  have hnonneg : 0 ≤ k % (m : ℤ) := Int.emod_nonneg k (by exact_mod_cast (ne_of_gt hD.m_pos))
  have hcast : (((k % (m : ℤ)).toNat) : ℤ) = k % (m : ℤ) := Int.toNat_of_nonneg hnonneg
  have hy : y ^ ((k % (m : ℤ)).toNat) = y ^ k := by
    rw [← zpow_natCast, hcast]
    simpa [hD.order_y] using (zpow_mod_orderOf y k)
  rw [hy, hk, hab]

/-- The derived subgroup `G' = [G, G]` is contained in the abelian part `A` of a standard
decomposition, because `G/A ≅ ⟨y⟩` is cyclic.  Used in the proofs of Lemma 3.1 and 3.2
(the paper: "`a^{p^r} ∈ G' ⊆ A`"). -/
lemma InD.commutator_le (hD : InD A y m) : commutator G ≤ A := by
  haveI : A.Normal := hD.normal
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ A
  rw [Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨a, ha, n, rfl⟩ := hD.exists_decomp g₁
  obtain ⟨b, hb, l, rfl⟩ := hD.exists_decomp g₂
  have hφ : (QuotientGroup.mk' A) ⁅a * y ^ n, b * y ^ l⁆ = 1 := by
    rw [map_commutatorElement]
    have ha1 : (QuotientGroup.mk' A) a = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact ha
    have hb1 : (QuotientGroup.mk' A) b = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hb
    have h1 : (QuotientGroup.mk' A) (a * y ^ n) = (QuotientGroup.mk' A) y ^ n := by
      rw [map_mul, map_pow, ha1, one_mul]
    have h2 : (QuotientGroup.mk' A) (b * y ^ l) = (QuotientGroup.mk' A) y ^ l := by
      rw [map_mul, map_pow, hb1, one_mul]
    rw [h1, h2]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.pow_pow_self ((QuotientGroup.mk' A) y) n l)
  rw [← QuotientGroup.ker_mk' A]
  exact MonoidHom.mem_ker.mpr hφ

end Structural

end Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition
