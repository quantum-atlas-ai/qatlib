/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition.ClassS
import Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition.Lemma31
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Nat.GCD.Basic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Lemma 3.2 of arXiv:1001.0608v1 (p.9)

Paper statement (arXiv:1001.0608v1, Lemma 3.2, p.9):

> **Lemma 3.2.** Let `G` be a group in the class `S` and suppose that `(A, ⟨y⟩) ∈ D_G^m`.
> Let `Σ` be a set of elements of `G` of prime power order such that each element of `Σ`
> has order coprime with `|G'|` and commutes with all the elements in `G'`.  Let `w` and `z`
> be two elements of `Σ` such that `[w, z] ≠ e`.  Then
>
> 1. if `z w z⁻¹ ∈ ⟨w⟩` then `w ∈ A` and `z = a y^α` with `a ∈ A` and `α ≢ 0 mod m`;
> 2. if `z w z⁻¹ ∉ ⟨w⟩` then `z ∈ A` and `w = a y^α` with `a ∈ A` and `α ≢ 0 mod m`.

The paper's proof (p.9) has two ingredients.

* Since `[w, z] ≠ e` and `A` is abelian, at least one of `w`, `z` is outside `A`.  Both
  being outside `A` is impossible: writing `w = a y^α` and `z = b y^β` with `a, b ∈ G'`
  (Lemma 3.1), the commutation with `G'` forces `a = b = 1` — indeed `a^{|w|} = 1` follows
  from `(a y^α)^{|w|} = 1` by separating the `A`-part and the `⟨y⟩`-part, which meet
  trivially — so both `w`, `z` are powers of `y` and commute.  Hence exactly one of them
  lies in `A`; this is `not_both_not_mem` plus `sigma_coeff_eq_one` below.
* In case (1), `z ∈ A` gives `[z, w] = (z w z⁻¹) w⁻¹ ∈ ⟨w⟩ ∩ G'`, which is trivial because
  the order of `w` is coprime with `|G'|`; this contradicts `[w, z] ≠ e`.
* In case (2), `w ∈ A` makes `z w z⁻¹ ∈ A`, so `[z, w] = (z w z⁻¹) w⁻¹` is a product of two
  commuting elements of order dividing `|w|`, hence has order dividing `|w|`; as `[z, w] ∈ G'`
  and `gcd(|w|, |G'|) = 1` this forces `[z, w] = e`, i.e. `z w z⁻¹ = w ∈ ⟨w⟩`.

The formal statements below are exactly the two assertions of Lemma 3.2.  The `Σ`-hypotheses
are bundled in `IsSigma`.
-/

open scoped commutatorElement

namespace Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition

/-- The hypotheses on the set `Σ` of Lemma 3.2: every element of `Σ` has prime-power order,
its order is coprime with `|G'|`, and it commutes with every element of `G'`. -/
structure IsSigma {G : Type*} [Group G] (S : Set G) : Prop where
  /-- Every element of `Σ` has prime-power order. -/
  primePower : ∀ s ∈ S, IsPrimePower (orderOf s)
  /-- Every element of `Σ` has order coprime with `|G'|`. -/
  coprime : ∀ s ∈ S, Nat.Coprime (orderOf s) (Nat.card (commutator G))
  /-- Every element of `Σ` commutes with every element of `G'`. -/
  commute : ∀ s ∈ S, ∀ g ∈ commutator G, s * g = g * s

section Lemma32

variable {G : Type*} [Group G] [Fintype G]
variable {A : Subgroup G} {y : G} {m : ℕ} {S : Set G}

/-- If `s ∈ S` does not lie in `A`, then it admits a standard decomposition `s = a y^n`
with `a ∈ G'` and `n` not divisible by `m`.  This is the combination of
`InD.exists_decomp` with Lemma 3.1 used at the start of the proof of Lemma 3.2. -/
lemma sigma_decomp (hD : InD A y m) (hS : IsSigma S)
    {s : G} (hs : s ∈ S) (hns : s ∉ A) :
    ∃ a ∈ A, a ∈ commutator G ∧ ∃ n : ℕ, ¬ m ∣ n ∧ s = a * y ^ n := by
  obtain ⟨a, haA, n, hseq⟩ := hD.exists_decomp s
  have hnm : ¬ m ∣ n := by
    intro hmn
    apply hns
    have hydvd : orderOf y ∣ n := by
      rw [hD.order_y]; exact hmn
    have hy : y ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hydvd
    rw [← hseq, hy, mul_one]; exact haA
  exact ⟨a, haA, lemma_3_1 hD haA hnm (by rw [hseq]; exact hS.primePower s hs),
    n, hnm, hseq.symm⟩

/-- Key auxiliary step of Lemma 3.2: an element `s = a y^n` of `Σ` with `a ∈ G'` has
`a = 1`.  Indeed `s` commutes with `a`, so `y^n` commutes with `a`; then
`(a y^n)^{|s|} = 1` decomposes as `a^{|s|} = (y^n)^{-|s|}`, and the left-hand side lies in
`A` while the right-hand side lies in `⟨y⟩`; these meet trivially, so `a^{|s|} = 1`.  Thus
`|a|` divides both `|s|` and `|G'|`, which are coprime, and `a = 1`. -/
lemma sigma_coeff_eq_one (hD : InD A y m) (hS : IsSigma S)
    {s : G} (hs : s ∈ S) {a : G} (haA : a ∈ A) (haG : a ∈ commutator G)
    {n : ℕ} (hseq : s = a * y ^ n) : a = 1 := by
  -- `s` commutes with `a`, hence `y^n` commutes with `a`.
  have hcomm : s * a = a * s := hS.commute s hs a haG
  rw [hseq] at hcomm
  have hcy : Commute a (y ^ n) := by
    have key : a * (y ^ n * a) = a * (a * y ^ n) := by
      rw [← mul_assoc, hcomm]
    exact (mul_left_cancel key).symm
  -- Expand `(a y^n)^{|s|} = 1`.
  set k := orderOf s with hk
  have hk1 : s ^ k = 1 := pow_orderOf_eq_one s
  rw [hseq] at hk1
  have hk2 : a ^ k * (y ^ n) ^ k = 1 := by
    rw [← hcy.mul_pow, hk1]
  have hak : a ^ k = ((y ^ n) ^ k)⁻¹ := mul_eq_one_iff_eq_inv.mp hk2
  -- `a^k` lies in `A ⊓ ⟨y⟩ = ⊥`.
  have hmemA : a ^ k ∈ A := Subgroup.pow_mem _ haA k
  have hmemY : ((y ^ n) ^ k)⁻¹ ∈ Subgroup.zpowers y := by
    rw [← pow_mul]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y (n * k))
  have hzero : a ^ k = 1 := by
    have hinf : a ^ k ∈ A ⊓ Subgroup.zpowers y := by
      rw [Subgroup.mem_inf]
      exact ⟨hmemA, by rw [hak]; exact hmemY⟩
    rw [hD.inf_zpowers_eq_bot] at hinf
    exact Subgroup.mem_bot.mp hinf
  -- `|a|` divides `|s|` and `|G'|`, which are coprime.
  have hdvd : orderOf a ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hzero
  have hcop : Nat.Coprime k (Nat.card (commutator G)) := hS.coprime s hs
  have hcop' : Nat.Coprime (orderOf a) (Nat.card (commutator G)) :=
    Nat.Coprime.of_dvd_left hdvd hcop
  have hdvdG : orderOf a ∣ Nat.card (commutator G) :=
    Subgroup.orderOf_dvd_natCard (commutator G) haG
  have hone : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop' dvd_rfl hdvdG
  exact orderOf_eq_one_iff.mp hone

/-- The cyclic subgroup `⟨w⟩` of an element `w ∈ S` meets `G'` trivially: an element of the
intersection has order dividing both `|w|` and `|G'|`, which are coprime. -/
lemma zpowers_inter_commutator_eq_bot (hS : IsSigma S) {s : G} (hs : s ∈ S) :
    Subgroup.zpowers s ⊓ commutator G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxs, hxG⟩ := hx
  have h1 : orderOf x ∣ orderOf s := orderOf_dvd_of_mem_zpowers hxs
  have h2 : orderOf x ∣ Nat.card (commutator G) :=
    Subgroup.orderOf_dvd_natCard (commutator G) hxG
  have hc : Nat.Coprime (orderOf s) (Nat.card (commutator G)) := hS.coprime s hs
  have h1' : Nat.Coprime (orderOf x) (Nat.card (commutator G)) :=
    Nat.Coprime.of_dvd_left h1 hc
  have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes h1' dvd_rfl h2
  simpa [orderOf_eq_one_iff] using hone

/-- Two elements of `A` commute, so their commutator is trivial (used to see that `w` and `z`
cannot both lie in `A` when `[w, z] ≠ e`). -/
lemma commutator_eq_one_of_mem (hD : InD A y m) {w z : G} (hw : w ∈ A) (hz : z ∈ A) :
    ⁅w, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (hD.comm w hw z hz)

/-- In Lemma 3.2, `w` and `z` cannot both lie outside `A`: writing `w = a y^n` and
`z = b y^l` with `a, b ∈ G'`, the auxiliary lemma `sigma_coeff_eq_one` forces `a = b = 1`,
so both are powers of `y` and hence commute, contradicting `[w, z] ≠ e`. -/
lemma not_both_not_mem (hD : InD A y m) (hS : IsSigma S)
    {w z : G} (hw : w ∈ S) (hz : z ∈ S) (hne : ⁅w, z⁆ ≠ 1) :
    ¬ (w ∉ A ∧ z ∉ A) := by
  rintro ⟨hwA, hzA⟩
  obtain ⟨a, haA, haG, n, _hnm, hwe⟩ := sigma_decomp hD hS hw hwA
  obtain ⟨b, hbA, hbG, l, _hlm, hze⟩ := sigma_decomp hD hS hz hzA
  have ha1 : a = 1 := sigma_coeff_eq_one hD hS hw haA haG hwe
  have hb1 : b = 1 := sigma_coeff_eq_one hD hS hz hbA hbG hze
  have hw' : w = y ^ n := by rw [hwe, ha1, one_mul]
  have hz' : z = y ^ l := by rw [hze, hb1, one_mul]
  exact hne (by
    rw [hw', hz']
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.pow_pow_self y n l))

/-- **Lemma 3.2 (1)** (arXiv:1001.0608v1, p.9).  If `w, z ∈ S` satisfy `[w, z] ≠ e` and
`z w z⁻¹ ∈ ⟨w⟩`, then `w ∈ A` and `z = a y^α` with `a ∈ A` and `α ≢ 0 mod m`. -/
theorem lemma_3_2_part1 (hD : InD A y m) (hS : IsSigma S)
    {w z : G} (hw : w ∈ S) (hz : z ∈ S) (hne : ⁅w, z⁆ ≠ 1)
    (hconj : z * w * z⁻¹ ∈ Subgroup.zpowers w) :
    w ∈ A ∧ ∃ a ∈ A, ∃ α : ℕ, ¬ m ∣ α ∧ z = a * y ^ α := by
  -- `z ∉ A`: otherwise `[z, w] ∈ ⟨w⟩ ∩ G' = ⊥`, contradicting `[w, z] ≠ e`.
  have hzA : z ∉ A := by
    intro _hzA
    have hmem1 : ⁅z, w⁆ ∈ Subgroup.zpowers w := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ (Subgroup.mem_zpowers w))
    have hmem2 : ⁅z, w⁆ ∈ commutator G := by
      show ⁅z, w⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top z) (Subgroup.mem_top w)
    have hinter : ⁅z, w⁆ ∈ Subgroup.zpowers w ⊓ commutator G :=
      Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rw [zpowers_inter_commutator_eq_bot hS hw] at hinter
    have hzw : ⁅z, w⁆ = 1 := Subgroup.mem_bot.mp hinter
    apply hne
    have hinv : ⁅w, z⁆⁻¹ = ⁅z, w⁆ := commutatorElement_inv w z
    rw [hzw] at hinv
    exact inv_eq_one.mp hinv
  -- Hence `w ∈ A`, because `w` and `z` cannot both lie outside `A`.
  have hwA : w ∈ A := by
    by_contra hwA
    exact not_both_not_mem hD hS hw hz hne ⟨hwA, hzA⟩
  obtain ⟨a, haA, _haG, α, hα, hzeq⟩ := sigma_decomp hD hS hz hzA
  exact ⟨hwA, a, haA, α, hα, hzeq⟩

/-- **Lemma 3.2 (2)** (arXiv:1001.0608v1, p.9).  If `w, z ∈ S` satisfy `[w, z] ≠ e` and
`z w z⁻¹ ∉ ⟨w⟩`, then `z ∈ A` and `w = a y^α` with `a ∈ A` and `α ≢ 0 mod m`. -/
theorem lemma_3_2_part2 (hD : InD A y m) (hS : IsSigma S)
    {w z : G} (hw : w ∈ S) (hz : z ∈ S) (hne : ⁅w, z⁆ ≠ 1)
    (hconj : z * w * z⁻¹ ∉ Subgroup.zpowers w) :
    z ∈ A ∧ ∃ a ∈ A, ∃ α : ℕ, ¬ m ∣ α ∧ w = a * y ^ α := by
  -- `w ∉ A`: otherwise `z w z⁻¹ = w`, i.e. `z w z⁻¹ ∈ ⟨w⟩`.
  have hwA : w ∉ A := by
    intro hwA
    apply hconj
    haveI : A.Normal := hD.normal
    have hqA : z * w * z⁻¹ ∈ A := hD.normal.conj_mem w hwA z
    -- `[z, w] = (z w z⁻¹) w⁻¹` has order dividing `|w|`.
    have hcommA : ⁅z, w⁆ ∈ A := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ hqA (Subgroup.inv_mem _ hwA)
    have hcommG : ⁅z, w⁆ ∈ commutator G := by
      show ⁅z, w⁆ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top z) (Subgroup.mem_top w)
    have hord : orderOf ⁅z, w⁆ ∣ orderOf w := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have hqpow : (z * w * z⁻¹) ^ orderOf w = 1 := by
        rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      have hwinv : (w⁻¹) ^ orderOf w = 1 := by
        rw [inv_pow, pow_orderOf_eq_one, inv_one]
      have hcy : Commute (z * w * z⁻¹) w⁻¹ :=
        hD.comm _ hqA _ (Subgroup.inv_mem _ hwA)
      rw [commutatorElement_def, hcy.mul_pow, hqpow, hwinv, mul_one]
    have hcop : Nat.Coprime (orderOf w) (Nat.card (commutator G)) := hS.coprime w hw
    have hcop' : Nat.Coprime (orderOf ⁅z, w⁆) (Nat.card (commutator G)) :=
      Nat.Coprime.of_dvd_left hord hcop
    have hdvdG : orderOf ⁅z, w⁆ ∣ Nat.card (commutator G) :=
      Subgroup.orderOf_dvd_natCard (commutator G) hcommG
    have hone : orderOf ⁅z, w⁆ = 1 := Nat.eq_one_of_dvd_coprimes hcop' dvd_rfl hdvdG
    have hzw : ⁅z, w⁆ = 1 := orderOf_eq_one_iff.mp hone
    have hqeq : z * w * z⁻¹ = w := by
      rw [commutatorElement_def] at hzw
      exact mul_inv_eq_one.mp hzw
    rw [hqeq]
    exact Subgroup.mem_zpowers w
  -- Hence `z ∈ A`, because `w` and `z` cannot both lie outside `A`.
  have hzA : z ∈ A := by
    by_contra hzA
    exact not_both_not_mem hD hS hw hz hne ⟨hwA, hzA⟩
  obtain ⟨a, haA, _haG, α, hα, hweq⟩ := sigma_decomp hD hS hw hwA
  exact ⟨hzA, a, haA, α, hα, hweq⟩

end Lemma32

end Qatlib.Papers.GroupIsom10.MainResults.StandardDecomposition
