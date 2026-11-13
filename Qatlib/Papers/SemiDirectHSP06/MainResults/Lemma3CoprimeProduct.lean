/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Subgroups of products of finite groups of coprime orders

`lemma3_coprime_product` identifies a subgroup of a product of finite groups of coprime orders
with the product of its two projection images. The auxiliary power congruences allow the
coordinates of a subgroup element to be isolated. See [ChiKimLee2006] for the mathematical
setting.

## Main statements

* `lemma3_coprime_product`: expresses any subgroup as the product of its projection images.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

/-- If `a ^ m = 1` and `k` is congruent to one modulo `m`, then `a ^ k = a`. -/
private lemma pow_eq_pow_of_modEq_one {G : Type*} [Group G] {a : G} {m k : ℕ}
    (hm : a ^ m = 1) (hk : k ≡ 1 [MOD m]) : a ^ k = a := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hk1 : k = 1 := by simpa [Nat.mod_zero] using hk
    rw [hk1, pow_one]
  · rw [← Nat.div_add_mod k m, pow_add, pow_mul, hm, one_pow, one_mul]
    have hmod : k % m = 1 % m := hk
    rw [hmod]
    rcases Nat.lt_or_eq_of_le (Nat.one_le_of_lt hmpos) with hm2 | hm1
    · rw [Nat.mod_eq_of_lt hm2, pow_one]
    · subst hm1
      rw [Nat.mod_one, pow_zero]
      simpa using hm.symm

/-- If `a ^ m = 1` and `k` is congruent to zero modulo `m`, then `a ^ k = 1`. -/
private lemma pow_eq_one_of_modEq_zero {G : Type*} [Group G] {a : G} {m k : ℕ}
    (hm : a ^ m = 1) (hk : k ≡ 0 [MOD m]) : a ^ k = 1 := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hk0 : k = 0 := by simpa [Nat.mod_zero] using hk
    rw [hk0, pow_zero]
  · rw [← Nat.div_add_mod k m, pow_add, pow_mul, hm, one_pow, one_mul]
    have hmod : k % m = 0 := by simpa [Nat.mod_zero] using! hk
    rw [hmod, pow_zero]

/-- A subgroup of a product of finite groups of coprime orders is the product of its images
under the two coordinate projections. See [Chi et al., 2006, Lemma 3][ChiKimLee2006]. -/
theorem lemma3_coprime_product {G0 G1 : Type*} [Group G0] [Group G1] [Finite G0] [Finite G1]
    (hcop : Nat.Coprime (Nat.card G0) (Nat.card G1))
    (H : Subgroup (G0 × G1)) :
    H = (H.map (MonoidHom.fst G0 G1)).prod (H.map (MonoidHom.snd G0 G1)) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_prod]
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  · intro x hx
    rw [Subgroup.mem_prod] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Subgroup.mem_map] at hx1 hx2
    obtain ⟨y, hyH, hy1⟩ := hx1
    obtain ⟨z, hzH, hz2⟩ := hx2

    obtain ⟨k, hk⟩ := Nat.chineseRemainder hcop 1 0
    obtain ⟨hk1, hk2⟩ := hk
    have hpow : y ^ k = (x.1, (1 : G1)) := by
      apply Prod.ext
      · change y.1 ^ k = x.1
        rw [pow_eq_pow_of_modEq_one (pow_card_eq_one' (x := y.1)) hk1]
        simpa using hy1
      · change y.2 ^ k = 1
        rw [pow_eq_one_of_modEq_zero (pow_card_eq_one' (x := y.2)) hk2]
    have hmem1 : (x.1, (1 : G1)) ∈ H := by
      rw [← hpow]; exact H.pow_mem hyH k

    obtain ⟨k', hk'⟩ := Nat.chineseRemainder hcop 0 1
    obtain ⟨hk1', hk2'⟩ := hk'
    have hpow' : z ^ k' = ((1 : G0), x.2) := by
      apply Prod.ext
      · change z.1 ^ k' = 1
        rw [pow_eq_one_of_modEq_zero (pow_card_eq_one' (x := z.1)) hk1']
      · change z.2 ^ k' = x.2
        rw [pow_eq_pow_of_modEq_one (pow_card_eq_one' (x := z.2)) hk2']
        simpa using hz2
    have hmem2 : ((1 : G0), x.2) ∈ H := by
      rw [← hpow']; exact H.pow_mem hzH k'
    have hprod : (x.1, (1 : G1)) * ((1 : G0), x.2) ∈ H := H.mul_mem hmem1 hmem2
    have heq : (x.1, (1 : G1)) * ((1 : G0), x.2) = x := by ext <;> simp
    rwa [heq] at hprod

end Qatlib.Papers.SemiDirectHSP06.MainResults
