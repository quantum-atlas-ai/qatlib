/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.Proposition3Presentation
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Order-p units modulo twice an odd prime power

`shiftUnit` has order `p`, and the unit group modulo `2 * p ^ r` is cyclic for odd prime `p`.
`proposition1_unit_order` characterizes every unit of order `p` as a nonidentity power of
`shiftUnit` and gives its explicit residue. See [ChiKimLee2006] for the mathematical setting.

## Main statements

* `orderOf_shiftUnit_eq_p`: computes the order of the distinguished unit.
* `proposition1_unit_order`: characterizes order-`p` units by powers and residues.

## References

* [Chi et al., 2006][ChiKimLee2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p r : ℕ}

/-- For prime `p` and `r ≥ 2`, the `p`th power of `shiftUnit` is one. -/
lemma shiftUnit_pow_eq_one (hp : p.Prime) (hr : 2 ≤ r) :
    shiftUnit p r hp hr ^ p = 1 := by
  apply Units.ext
  change ((shiftUnit p r hp hr : ZMod (2 * p ^ r)) ^ p) = 1
  rw [coe_shiftUnit, shiftVal_pow_mod hp hr p]
  have h2 : 2 * p * p ^ (r - 1) = 2 * p ^ r := by
    rw [pow_eq_mul_pred (p := p) (by omega : 1 ≤ r)]
    ring
  rw [h2, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]

/-- For prime `p` and `r ≥ 2`, `shiftUnit` differs from one. -/
lemma shiftUnit_ne_one (hp : p.Prime) (hr : 2 ≤ r) :
    shiftUnit p r hp hr ≠ 1 := by
  intro hone
  have hcoe : ((shiftUnit p r hp hr : (ZMod (2 * p ^ r))ˣ) : ZMod (2 * p ^ r)) = 1 := by
    rw [hone]; rfl
  rw [coe_shiftUnit] at hcoe
  unfold shiftVal at hcoe
  rw [Nat.cast_add, Nat.cast_one] at hcoe
  have hzero : ((2 * p ^ (r - 1) : ℕ) : ZMod (2 * p ^ r)) = 0 := by
    have h' : ((2 * p ^ (r - 1) : ℕ) : ZMod (2 * p ^ r)) + 1 = 0 + 1 := by
      rw [hcoe]; simp
    exact add_right_cancel h'
  have hdvd : 2 * p ^ r ∣ 2 * p ^ (r - 1) :=
    (ZMod.natCast_eq_zero_iff (2 * p ^ (r - 1)) (2 * p ^ r)).mp hzero
  have hprdvd : p ^ r ∣ p ^ (r - 1) :=
    (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdvd
  have hlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
  exact Nat.not_le_of_lt hlt (Nat.le_of_dvd hpos hprdvd)

/-- For prime `p` and `r ≥ 2`, `shiftUnit` has order `p`. -/
lemma orderOf_shiftUnit_eq_p (hp : p.Prime) (hr : 2 ≤ r) :
    orderOf (shiftUnit p r hp hr) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (shiftUnit_pow_eq_one hp hr) (shiftUnit_ne_one hp hr)

/-- For odd prime `p` and `r ≥ 2`, the unit group modulo `2 * p ^ r` has cardinality `p ^ (r -
1) * (p - 1)`. -/
lemma card_units_two_pow (hp : p.Prime) (hodd : p ≠ 2) (hr : 2 ≤ r) :
    Nat.card (ZMod (2 * p ^ r))ˣ = p ^ (r - 1) * (p - 1) := by
  haveI : NeZero (2 * p ^ r) :=
    ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero)⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_two_mul_of_odd ((hp.odd_of_ne_two hodd).pow),
    Nat.totient_prime_pow hp (by omega)]

/-- For odd prime `p` and `r ≥ 2`, `p` divides the cardinality of the unit group modulo `2 * p ^
r`. -/
lemma p_dvd_card_units (hp : p.Prime) (hodd : p ≠ 2) (hr : 2 ≤ r) :
    p ∣ Nat.card (ZMod (2 * p ^ r))ˣ := by
  rw [card_units_two_pow hp hodd hr]
  exact dvd_mul_of_dvd_left
    (by simpa using pow_dvd_pow p (show 1 ≤ r - 1 by omega)) _

/-- For odd prime `p`, the unit group modulo `2 * p ^ r` is cyclic. -/
lemma isCyclic_units_two_pow (hp : p.Prime) (hodd : p ≠ 2) :
    IsCyclic (ZMod (2 * p ^ r))ˣ := by
  rw [ZMod.isCyclic_units_two_mul_iff_of_odd (p ^ r) ((hp.odd_of_ne_two hodd).pow)]
  exact ZMod.isCyclic_units_of_prime_pow p hp hodd r

/-- For odd prime `p` and `r ≥ 2`, a unit has order `p` exactly when it is `shiftUnit ^ i` for
`1 ≤ i ≤ p - 1`, with residue `2 * i * p ^ (r - 1) + 1`. See [Chi et al., 2006, Proposition
1][ChiKimLee2006]. -/
theorem proposition1_unit_order
    {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hodd : p ≠ 2) :
    ∀ α : (ZMod (2 * p ^ r))ˣ,
      orderOf α = p ↔
        ∃ i : ℕ, 1 ≤ i ∧ i ≤ p - 1 ∧
          (α = shiftUnit p r hp hr ^ i ∧
            ((α : ZMod (2 * p ^ r)) =
              ((2 * i * p ^ (r - 1) + 1 : ℕ) : ZMod (2 * p ^ r)))) := by
  intro α
  constructor
  · intro hα
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (2 * p ^ r) :=
      ⟨Nat.mul_ne_zero (by norm_num) (pow_ne_zero _ hp.ne_zero)⟩
    haveI : IsCyclic (ZMod (2 * p ^ r))ˣ := isCyclic_units_two_pow hp hodd

    have hαK : α ∈ (powMonoidHom p : (ZMod (2 * p ^ r))ˣ →* (ZMod (2 * p ^ r))ˣ).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h := pow_orderOf_eq_one α
      rwa [hα] at h

    have hcardK : Nat.card
        (powMonoidHom p : (ZMod (2 * p ^ r))ˣ →* (ZMod (2 * p ^ r))ˣ).ker = p := by
      rw [IsCyclic.card_powMonoidHom_ker, card_units_two_pow hp hodd hr]
      have hdvd : p ∣ p ^ (r - 1) * (p - 1) := by
        have h := p_dvd_card_units hp hodd hr
        rwa [card_units_two_pow hp hodd hr] at h
      exact Nat.gcd_eq_right hdvd

    have hshiftK : shiftUnit p r hp hr ∈
        (powMonoidHom p : (ZMod (2 * p ^ r))ˣ →* (ZMod (2 * p ^ r))ˣ).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      exact shiftUnit_pow_eq_one hp hr
    have hle : Subgroup.zpowers (shiftUnit p r hp hr) ≤
        (powMonoidHom p : (ZMod (2 * p ^ r))ˣ →* (ZMod (2 * p ^ r))ˣ).ker :=
      Subgroup.zpowers_le.mpr hshiftK
    have hcardZ : Nat.card (Subgroup.zpowers (shiftUnit p r hp hr)) = p := by
      rw [Nat.card_zpowers, orderOf_shiftUnit_eq_p hp hr]
    have heq : Subgroup.zpowers (shiftUnit p r hp hr) =
        (powMonoidHom p : (ZMod (2 * p ^ r))ˣ →* (ZMod (2 * p ^ r))ˣ).ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardK, hcardZ])

    have hmem : α ∈ Subgroup.zpowers (shiftUnit p r hp hr) := by
      rw [heq]; exact hαK
    obtain ⟨m, hm⟩ := (Subgroup.mem_zpowers_iff).mp hmem
    have hαne : α ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hα
      exact hp.ne_one hα.symm
    have hmod_nonneg : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (by exact_mod_cast hp.ne_zero)
    have hmod_lt : m % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast hp.pos)
    have hα_eq : α = shiftUnit p r hp hr ^ (m % (p : ℤ)).toNat := by
      rw [← hm, zpow_eq_zpow_emod' m (shiftUnit_pow_eq_one hp hr), ← zpow_natCast,
        Int.toNat_of_nonneg hmod_nonneg]
    have hi1 : 1 ≤ (m % (p : ℤ)).toNat := by
      rcases Nat.eq_zero_or_pos ((m % (p : ℤ)).toNat) with h | h
      · exfalso
        exact hαne (by rw [hα_eq, h, pow_zero])
      · exact h
    have hile : (m % (p : ℤ)).toNat ≤ p - 1 := by
      have hcast : (((m % (p : ℤ)).toNat : ℕ) : ℤ) = m % (p : ℤ) :=
        Int.toNat_of_nonneg hmod_nonneg
      omega
    have hcoe : ((α : ZMod (2 * p ^ r)) =
        ((2 * (m % (p : ℤ)).toNat * p ^ (r - 1) + 1 : ℕ) : ZMod (2 * p ^ r))) := by
      rw [hα_eq]
      change ((shiftUnit p r hp hr : ZMod (2 * p ^ r)) ^ (m % (p : ℤ)).toNat) =
        ((2 * (m % (p : ℤ)).toNat * p ^ (r - 1) + 1 : ℕ) : ZMod (2 * p ^ r))
      rw [coe_shiftUnit]
      exact shiftVal_pow_mod hp hr (m % (p : ℤ)).toNat
    exact ⟨(m % (p : ℤ)).toNat, hi1, hile, hα_eq, hcoe⟩
  · rintro ⟨i, hi1, hile, hα, hcoe⟩
    rw [hα]

    have hcop : Nat.Coprime p i := (hp.coprime_iff_not_dvd).mpr (by
      intro hdvd
      have hle : p ≤ i := Nat.le_of_dvd (by omega) hdvd
      omega)
    rw [Nat.Coprime.orderOf_pow (y := shiftUnit p r hp hr) (m := i) (by
      rw [orderOf_shiftUnit_eq_p hp hr]; exact hcop), orderOf_shiftUnit_eq_p hp hr]

end Qatlib.Papers.SemiDirectHSP06.MainResults
