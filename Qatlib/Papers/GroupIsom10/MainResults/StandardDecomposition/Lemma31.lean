/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition.ClassS
import Mathlib.GroupTheory.Abelianization.Defs

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Lemma 3.1 of arXiv:1001.0608v1 (p.10)

Paper statement:

> **Lemma 3.1.** Let `G` be a group in the class `S` and suppose that `(A, ⟨y⟩) ∈ D_G^m`.
> Let `w = a y^α` be an element of `G` with `a ∈ A` and `α ≢ 0 mod m`.  If the order of
> `w` is a prime power, then `a ∈ G'`.

Proof route (paper, p.10): write `p^r = |w|`.  Since `α ≢ 0 (mod m)`, the image of `w` in
`G/A ≅ Z_m` is nontrivial, so `p | m`.  From `(a y^α)^{p^r} = 1` and `m | α p^r` one gets
`a^{p^r} ∈ G'`; as `p^r` is coprime with `|A|` and `a^{p^r}` generates `a`, this gives
`a ∈ G'`.

Plain-English proof in this file: project `(a y^α)^{p^r} = 1` to `G ⧸ A` to obtain
`m ∣ α p^r`; conclude `p ∣ m`, hence `p ∤ |A|`; project to the abelianization to obtain
`a^{p^r} ∈ G'`; finally `a` is a power of `a^{p^r}` because `p^r` is coprime with `|a|`.
-/

open scoped commutatorElement

namespace Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition

variable {G : Type*} [Group G]

/-- **Lemma 3.1** (arXiv:1001.0608v1, p.10).  If `(A, ⟨y⟩) ∈ D_G^m`, `a ∈ A`, `α` is not
divisible by `m`, and `a * y ^ α` has prime-power order, then `a` lies in the derived
subgroup `G'` (the commutator subgroup `[G, G]`). -/
theorem lemma_3_1 [Fintype G] {A : Subgroup G} {y : G} {m α : ℕ} {a : G}
    (hD : InD A y m) (ha : a ∈ A) (hα : ¬ m ∣ α)
    (hpp : IsPrimePower (orderOf (a * y ^ α))) :
    a ∈ commutator G := by
  obtain ⟨p, r, hp, hr, hord⟩ := hpp
  haveI : A.Normal := hD.normal
  -- `(a y^α)^{p^r} = 1`
  have hpow : (a * y ^ α) ^ (p ^ r) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one _
  -- Step 1: `m ∣ α * p^r`, by projecting to `G ⧸ A`.
  have hφpow : (QuotientGroup.mk' A) (y ^ (α * p ^ r)) = 1 := by
    have h := congrArg (QuotientGroup.mk' A) hpow
    simp only [map_pow, map_mul, map_one] at h
    have ha1 : (QuotientGroup.mk' A) a = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact ha
    rw [ha1, one_mul, ← pow_mul] at h
    simpa using h
  have hyA : y ^ (α * p ^ r) ∈ A := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [QuotientGroup.mk'_apply] using hφpow
  have hy1 : y ^ (α * p ^ r) = 1 := by
    have hmem : y ^ (α * p ^ r) ∈ A ⊓ Subgroup.zpowers y :=
      ⟨hyA, Subgroup.npow_mem_zpowers y _⟩
    rw [hD.inf_zpowers_eq_bot] at hmem
    simpa using hmem
  have hm_dvd : m ∣ α * p ^ r := by
    rw [← hD.order_y]
    exact orderOf_dvd_iff_pow_eq_one.mpr hy1
  -- Step 2: `p ∣ m` (otherwise `m ∣ α`, contradicting `α ≢ 0`).
  have hp_dvd_m : p ∣ m := by
    by_contra hpm
    have hcop : Nat.Coprime m (p ^ r) :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)).pow_right r
    exact hα (hcop.dvd_mul_right.mp hm_dvd)
  -- Step 3: `p ∤ |A|`, hence `p^r` is coprime with `|A|`.
  have hp_not_dvd_A : ¬ p ∣ Nat.card A := by
    intro hpdvd
    have hpdvd_gcd : p ∣ Nat.gcd (Nat.card A) m := Nat.dvd_gcd hpdvd hp_dvd_m
    rw [hD.coprime] at hpdvd_gcd
    exact hp.not_dvd_one hpdvd_gcd
  have hcop_pr_A : Nat.Coprime (p ^ r) (Nat.card A) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp_not_dvd_A).pow_left r
  -- Step 4: `a^{p^r} ∈ G'`, by projecting to the abelianization.
  have hap_mem : a ^ (p ^ r) ∈ commutator G := by
    have h := congrArg Abelianization.of hpow
    simp only [map_pow, map_mul, map_one] at h
    have hyα1 : (Abelianization.of y) ^ (α * p ^ r) = 1 := by
      have h1 : Abelianization.of (y ^ (α * p ^ r)) = 1 := by rw [hy1, map_one]
      simpa [map_pow] using h1
    have hpa : (Abelianization.of a) ^ (p ^ r) = 1 := by
      have h2 : (Abelianization.of y ^ α) ^ (p ^ r) = 1 := by
        rw [← pow_mul]; exact hyα1
      have hmul : (Abelianization.of a) ^ (p ^ r) * (Abelianization.of y ^ α) ^ (p ^ r) = 1 := by
        rw [← mul_pow]; exact h
      rwa [h2, mul_one] at hmul
    rw [← Abelianization.ker_of]
    exact MonoidHom.mem_ker.mpr (by simpa [map_pow] using hpa)
  -- Step 5: `a` is a power of `a^{p^r}`, since `p^r` is coprime with `|a|`.
  have hcop_a : Nat.Coprime (p ^ r) (orderOf a) :=
    Nat.Coprime.of_dvd_right (Subgroup.orderOf_dvd_natCard A ha) hcop_pr_A
  have hord_a : orderOf (a ^ (p ^ r)) = orderOf a := hcop_a.symm.orderOf_pow
  have hzp : Subgroup.zpowers (a ^ (p ^ r)) = Subgroup.zpowers a := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers a _)
    · have h1 : Nat.card ↥(Subgroup.zpowers a) = orderOf a := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.card_zpowers
      have h2 : Nat.card ↥(Subgroup.zpowers (a ^ (p ^ r))) = orderOf (a ^ (p ^ r)) := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.card_zpowers
      rw [h1, h2, hord_a]
  have hle : Subgroup.zpowers (a ^ (p ^ r)) ≤ commutator G :=
    Subgroup.zpowers_le.mpr hap_mem
  rw [hzp] at hle
  exact hle (Subgroup.mem_zpowers a)

end Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition
