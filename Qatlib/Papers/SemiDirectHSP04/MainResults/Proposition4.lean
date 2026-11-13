/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Card

/-!
# Prime-order units modulo prime powers

This module classifies prime-order units modulo `p ^ r` in the cases used for cyclic semidirect
products. `candUnit` supplies the units `1 + t * p ^ (r - 1)` for the odd-prime case, while
separate residue calculations describe the involutions modulo powers of two. See
[InuiLeGall2007] for the mathematical setting.

## Main statements

* `prop4_case_ii_characterization`: describes all order-`p` units for odd prime `p` and `r > 1`.
* `prop4_case_iii_gt_two`: lists the three involution residues modulo `2 ^ r` for `r > 2`.
* `prop4_only_cases`: restricts a prime order `q` to the two possible arithmetic cases.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition4

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

/-- The unit modulo `p ^ r` represented by `1 + t * p ^ (r - 1)`, for prime `p` and `r ≥ 2`. -/
def candUnit (p r t : ℕ) (hp : p.Prime) (hr : 2 ≤ r) : (ZMod (p ^ r))ˣ :=
  ZMod.unitOfCoprime (1 + t * p ^ (r - 1)) (by
    have hpdvd : p ∣ p ^ (r - 1) := dvd_pow_self p (by omega)
    have hptdvd : p ∣ t * p ^ (r - 1) := dvd_mul_of_dvd_right hpdvd t
    have hpnd : ¬ p ∣ (1 + t * p ^ (r - 1)) := by
      intro h
      have hsub : p ∣ (1 + t * p ^ (r - 1)) - t * p ^ (r - 1) :=
        Nat.dvd_sub h hptdvd
      rw [Nat.add_sub_cancel] at hsub
      exact hp.not_dvd_one hsub
    have hcop : Nat.Coprime (1 + t * p ^ (r - 1)) p :=
      ((hp.coprime_iff_not_dvd).mpr hpnd).symm
    rw [Nat.coprime_pow_right_iff (by omega)]
    exact hcop)

/-- The underlying residue of `candUnit` is the natural number `1 + t * p ^ (r - 1)` cast modulo
`p ^ r`. -/
@[simp]
theorem candUnit_coe (p r t : ℕ) (hp : p.Prime) (hr : 2 ≤ r) :
    ((candUnit p r t hp hr : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      = ((1 + t * p ^ (r - 1) : ℕ) : ZMod (p ^ r)) := by
  simp [candUnit]

/-- If prime `q` divides `p - 1` and `r ≥ 1`, exactly `q - 1` units modulo `p ^ r` have order
`q`. See [Inui and Le Gall, 2007, Proposition 4][InuiLeGall2007]. -/
theorem prop4_case_i (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : 1 ≤ r)
    (hqr : q ∣ p - 1) :
    Nat.card {α : (ZMod (p ^ r))ˣ // orderOf α = q} = q - 1 := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    have : q ∣ 1 := by simpa using hqr
    have hq1 : q = 1 := Nat.dvd_one.mp this
    exact hq.ne_one hq1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod (p ^ r))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 r
  have hdvd : q ∣ Fintype.card (ZMod (p ^ r))ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hr]
    exact dvd_mul_of_dvd_right hqr (p ^ (r - 1))
  have hcard := IsCyclic.card_orderOf_eq_totient (α := (ZMod (p ^ r))ˣ) hdvd
  rw [Nat.totient_prime hq] at hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcard

/-- For odd prime `p`, `r ≥ 2`, and `0 < t < p`, the candidate unit has order `p`. -/
theorem prop4_case_ii_candUnit_order (p r t : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 2 ≤ r) (ht0 : 0 < t) (htp : t < p) :
    orderOf (candUnit p r t hp hr) = p := by
  have hm0 : r - 1 ≠ 0 := by omega
  have hpm : (r - 1) + 2 ≤ p * (r - 1) := by
    have hm1 : 1 ≤ r - 1 := by omega
    have hp3 : 3 ≤ p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hmul : 3 * (r - 1) ≤ p * (r - 1) := Nat.mul_le_mul_right _ hp3
    nlinarith
  have hnot : ¬ (p : ℤ) ∣ (t : ℤ) := by
    intro h
    have hle : (p : ℤ) ≤ (t : ℤ) := Int.le_of_dvd (by exact_mod_cast ht0) h
    have : p ≤ t := by exact_mod_cast hle
    omega
  have hord := ZMod.orderOf_one_add_mul_prime_pow hp (r - 1) hm0 hpm (t : ℤ) hnot 1
  rw [show 1 + (r - 1) = r from by omega, pow_one] at hord
  have hcoe : ((candUnit p r t hp hr : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      = (1 + p ^ (r - 1) * (t : ℤ) : ZMod (p ^ r)) := by
    rw [candUnit_coe]
    push_cast
    ring
  rw [← orderOf_units, hcoe]
  exact hord

/-- For odd prime `p` and `r > 1`, exactly `p - 1` units modulo `p ^ r` have order `p`. See
[Inui and Le Gall, 2007, Proposition 4][InuiLeGall2007]. -/
theorem prop4_case_ii_card (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 < r) :
    Nat.card {α : (ZMod (p ^ r))ˣ // orderOf α = p} = p - 1 := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod (p ^ r))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 r
  have hdvd : p ∣ Fintype.card (ZMod (p ^ r))ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega)]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) (p - 1)
  have hcard := IsCyclic.card_orderOf_eq_totient (α := (ZMod (p ^ r))ˣ) hdvd
  rw [Nat.totient_prime hp] at hcard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hcard

/-- For odd prime `p` and `r > 1`, the order-`p` units are precisely the candidate units with
parameter `0 < t < p`. See [Inui and Le Gall, 2007, Proposition 4][InuiLeGall2007]. -/
theorem prop4_case_ii_characterization (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 1 < r) :
    {α : (ZMod (p ^ r))ˣ | orderOf α = p}
      = {α : (ZMod (p ^ r))ˣ | ∃ t : ℕ, 0 < t ∧ t < p ∧
          α = candUnit p r t hp (by omega)} := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩

  have h2 : 2 ≤ r := by omega

  let f : ℕ → (ZMod (p ^ r))ˣ := fun t => candUnit p r t hp h2
  have hcoe : ∀ t : ℕ, ((f t : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      = ((1 + t * p ^ (r - 1) : ℕ) : ZMod (p ^ r)) := by
    intro t; exact candUnit_coe p r t hp h2

  have hinj : Set.InjOn f ↑(Finset.Icc 1 (p - 1)) := by
    intro t1 ht1 t2 ht2 heq
    rw [Finset.coe_Icc, Set.mem_Icc] at ht1 ht2
    obtain ⟨ht1a, ht1b⟩ := ht1
    obtain ⟨ht2a, ht2b⟩ := ht2
    have hval : ((1 + t1 * p ^ (r - 1) : ℕ) : ZMod (p ^ r))
        = ((1 + t2 * p ^ (r - 1) : ℕ) : ZMod (p ^ r)) := by
      rw [← hcoe t1, ← hcoe t2, heq]
    rw [ZMod.natCast_eq_natCast_iff] at hval
    have hlt1 : t1 < p := by omega
    have hlt2 : t2 < p := by omega
    have hcpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
    have hpr : p ^ r = p ^ (r - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rcases le_total t1 t2 with hle | hle
    · have hale : 1 + t1 * p ^ (r - 1) ≤ 1 + t2 * p ^ (r - 1) := by
        have h : t1 * p ^ (r - 1) ≤ t2 * p ^ (r - 1) := Nat.mul_le_mul_right _ hle
        omega
      have hdvd : p ^ r ∣ (1 + t2 * p ^ (r - 1)) - (1 + t1 * p ^ (r - 1)) :=
        (Nat.modEq_iff_dvd' hale).mp hval
      have hdiff : (1 + t2 * p ^ (r - 1)) - (1 + t1 * p ^ (r - 1))
          = (t2 - t1) * p ^ (r - 1) := by
        rw [Nat.add_sub_add_left, ← Nat.sub_mul]
      rw [hdiff, hpr, mul_comm (t2 - t1) (p ^ (r - 1))] at hdvd
      have hpdiv : p ∣ (t2 - t1) := Nat.dvd_of_mul_dvd_mul_left hcpos hdvd
      have hzero : t2 - t1 = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv (by omega)
      omega
    · have hale : 1 + t2 * p ^ (r - 1) ≤ 1 + t1 * p ^ (r - 1) := by
        have h : t2 * p ^ (r - 1) ≤ t1 * p ^ (r - 1) := Nat.mul_le_mul_right _ hle
        omega
      have hdvd : p ^ r ∣ (1 + t1 * p ^ (r - 1)) - (1 + t2 * p ^ (r - 1)) :=
        (Nat.modEq_iff_dvd' hale).mp hval.symm
      have hdiff : (1 + t1 * p ^ (r - 1)) - (1 + t2 * p ^ (r - 1))
          = (t1 - t2) * p ^ (r - 1) := by
        rw [Nat.add_sub_add_left, ← Nat.sub_mul]
      rw [hdiff, hpr, mul_comm (t1 - t2) (p ^ (r - 1))] at hdvd
      have hpdiv : p ∣ (t1 - t2) := Nat.dvd_of_mul_dvd_mul_left hcpos hdvd
      have hzero : t1 - t2 = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv (by omega)
      omega

  have hFcard : ((Finset.Icc 1 (p - 1)).image f).card = p - 1 := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  have hScard :
      (Finset.univ.filter (fun α : (ZMod (p ^ r))ˣ => orderOf α = p)).card = p - 1 := by
    have h := prop4_case_ii_card p r hp hp2 hr
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    simpa using h
  have hsub : (Finset.Icc 1 (p - 1)).image f ⊆
      (Finset.univ.filter (fun α : (ZMod (p ^ r))ˣ => orderOf α = p)) := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨t, ht, rfl⟩ := hα
    rw [Finset.mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact prop4_case_ii_candUnit_order p r t hp hp2 h2 (by omega) (by omega)
  have heqF : (Finset.Icc 1 (p - 1)).image f
      = (Finset.univ.filter (fun α : (ZMod (p ^ r))ˣ => orderOf α = p)) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hFcard, hScard])
  ext α
  constructor
  · intro hα
    have hmem : α ∈ Finset.univ.filter (fun α : (ZMod (p ^ r))ˣ => orderOf α = p) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hα⟩
    rw [← heqF, Finset.mem_image] at hmem
    obtain ⟨t, ht, hft⟩ := hmem
    rw [Finset.mem_Icc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    refine ⟨t, by omega, by omega, ?_⟩
    have heqproof : candUnit p r t hp (by omega : 2 ≤ r) = candUnit p r t hp h2 :=
      congrArg (candUnit p r t hp) (Subsingleton.elim _ _)
    rw [heqproof]
    exact hft.symm
  · rintro ⟨t, ht0, htp, rfl⟩
    have heqproof : candUnit p r t hp (by omega : 2 ≤ r) = candUnit p r t hp h2 :=
      congrArg (candUnit p r t hp) (Subsingleton.elim _ _)
    rw [heqproof]
    exact prop4_case_ii_candUnit_order p r t hp hp2 h2 ht0 htp

/-- For `r > 2`, the square of `2 ^ (r - 1)` vanishes modulo `2 ^ r`. -/
theorem zpow_sq_zero (r : ℕ) (hr : 2 < r) :
    (((2 ^ (r - 1) : ℕ)) : ZMod (2 ^ r)) ^ 2 = 0 := by
  rw [← Nat.cast_pow]
  have hdvd : 2 ^ r ∣ (2 ^ (r - 1)) ^ 2 := by
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- For `r ≥ 1`, the natural power `2 ^ r` equals `2 * 2 ^ (r - 1)`. -/
theorem two_pow_eq_two_mul (r : ℕ) (hr : 1 ≤ r) : (2 : ℕ) ^ r = 2 * 2 ^ (r - 1) := by
  conv_lhs => rw [show r = (r - 1) + 1 by omega]
  rw [pow_succ]; ring

/-- For `r > 2`, twice the residue of `2 ^ (r - 1)` vanishes modulo `2 ^ r`. -/
theorem two_mul_zpow_eq_zero (r : ℕ) (hr : 2 < r) :
    (2 : ZMod (2 ^ r)) * ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) = 0 := by
  have hmul : ((2 * 2 ^ (r - 1) : ℕ) : ZMod (2 ^ r))
      = (2 : ZMod (2 ^ r)) * ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) := by
    rw [Nat.cast_mul]; norm_num
  rw [← hmul, ← two_pow_eq_two_mul r (by omega), ZMod.natCast_self]

/-- For `r > 2`, the residue of `2 ^ (r - 1) + 1` has square one modulo `2 ^ r`. -/
theorem sq_zpow_add_one (r : ℕ) (hr : 2 < r) :
    ((2 ^ (r - 1) + 1 : ℕ) : ZMod (2 ^ r)) ^ 2 = 1 := by
  have hz2 := zpow_sq_zero r hr
  have h2z := two_mul_zpow_eq_zero r hr
  have hcast : ((2 ^ (r - 1) + 1 : ℕ) : ZMod (2 ^ r))
      = ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  calc (((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) + 1) ^ 2
      = ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) ^ 2
          + 2 * (((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r))) + 1 := by ring
    _ = 0 + 0 + 1 := by rw [hz2, h2z]
    _ = 1 := by ring

/-- For `r > 2`, the residue of `2 ^ (r - 1) - 1` has square one modulo `2 ^ r`. -/
theorem sq_zpow_sub_one (r : ℕ) (hr : 2 < r) :
    ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r)) ^ 2 = 1 := by
  have hz2 := zpow_sq_zero r hr
  have h2z := two_mul_zpow_eq_zero r hr
  have hcast : ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r))
      = ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one]
  rw [hcast]
  calc (((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) - 1) ^ 2
      = ((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r)) ^ 2
          - 2 * (((2 ^ (r - 1) : ℕ) : ZMod (2 ^ r))) + 1 := by ring
    _ = 0 - 0 + 1 := by rw [hz2, h2z]
    _ = 1 := by ring

/-- The residue of the natural number `2 ^ r - 1` has square one modulo `2 ^ r`. -/
theorem sq_pow_sub_one (r : ℕ) :
    ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r)) ^ 2 = 1 := by
  have hcast : ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r)) = -1 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow), ZMod.natCast_self, Nat.cast_one]
    ring
  rw [hcast]; ring

/-- A natural number strictly between one and `2 ^ r` does not represent one modulo `2 ^ r`. -/
theorem natCast_ne_one_of_gt {r x : ℕ} (h1 : 1 < x) (h2 : x < 2 ^ r) :
    ((x : ℕ) : ZMod (2 ^ r)) ≠ 1 := by
  intro hc
  have heq : ((x : ℕ) : ZMod (2 ^ r)) = ((1 : ℕ) : ZMod (2 ^ r)) := by simpa using hc
  rw [ZMod.natCast_eq_natCast_iff] at heq
  have hd : 2 ^ r ∣ x - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ x)).mp heq.symm
  have hlt : x - 1 < 2 ^ r := by omega
  have := Nat.eq_zero_of_dvd_of_lt hd hlt
  omega

/-- A unit modulo `2 ^ r` whose underlying residue has square one and differs from one has order
two. -/
theorem orderOf_eq_two_of_residue (r : ℕ) (α : (ZMod (2 ^ r))ˣ)
    (hsq : ((α : ZMod (2 ^ r))) ^ 2 = 1) (hne : ((α : ZMod (2 ^ r))) ≠ 1) :
    orderOf α = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hsq
  · intro hcontra
    apply hne
    rw [hcontra, Units.val_one]

/-- For `r > 2`, a unit modulo `2 ^ r` has order two exactly when its residue is `2 ^ (r - 1) +
1`, `2 ^ (r - 1) - 1`, or `2 ^ r - 1`. See [Inui and Le Gall, 2007, Proposition
4][InuiLeGall2007]. -/
theorem prop4_case_iii_gt_two (r : ℕ) (hr : 2 < r) :
    ∀ α : (ZMod (2 ^ r))ˣ, orderOf α = 2 ↔
      ((α : ZMod (2 ^ r)) = ((2 ^ (r - 1) + 1 : ℕ) : ZMod (2 ^ r))
        ∨ (α : ZMod (2 ^ r)) = ((2 ^ (r - 1) - 1 : ℕ) : ZMod (2 ^ r))
        ∨ (α : ZMod (2 ^ r)) = ((2 ^ r - 1 : ℕ) : ZMod (2 ^ r))) := by
  intro α
  haveI : NeZero (2 ^ r) := ⟨pow_ne_zero r (by norm_num)⟩
  constructor
  · intro hord
    have h2 : α ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    have hcoe : ((α : ZMod (2 ^ r))) ^ 2 = 1 := by
      have hcongr : ((α ^ 2 : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r))
          = ((1 : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) := by rw [h2]
      rw [Units.val_pow_eq_pow_val, Units.val_one] at hcongr
      exact hcongr
    set n := (α : ZMod (2 ^ r)).val with hn
    have hncast : ((n : ℕ) : ZMod (2 ^ r)) = (α : ZMod (2 ^ r)) := ZMod.natCast_zmod_val _
    have hn_lt : n < 2 ^ r := ZMod.val_lt _
    have hcop : Nat.Coprime n (2 ^ r) := by
      rw [← ZMod.isUnit_iff_coprime n (2 ^ r), hncast]
      exact α.isUnit
    have hodd : Odd n :=
      Nat.coprime_two_right.mp ((Nat.coprime_pow_right_iff (by omega) n 2).mp hcop)
    obtain ⟨m, hm⟩ := hodd
    have hn1 : 1 ≤ n := by omega
    have hsq : ((n ^ 2 : ℕ) : ZMod (2 ^ r)) = 1 := by
      rw [Nat.cast_pow, hncast]; exact hcoe
    have hmod : n ^ 2 ≡ 1 [MOD 2 ^ r] :=
      (ZMod.natCast_eq_natCast_iff (n ^ 2) 1 (2 ^ r)).mp (by simpa using hsq)
    have hdvd : 2 ^ r ∣ n ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' (by nlinarith)).mp hmod.symm
    have hfac : n ^ 2 - 1 = 4 * (m * (m + 1)) := by
      have hsqeq : n ^ 2 = 4 * (m * (m + 1)) + 1 := by rw [hm]; ring
      rw [hsqeq]; omega
    have hdvd2 : 2 ^ r ∣ 4 * (m * (m + 1)) := by rw [← hfac]; exact hdvd
    have hpow : 2 ^ r = 4 * 2 ^ (r - 2) := by
      conv_lhs => rw [show r = (r - 2) + 2 by omega]
      rw [pow_add]; ring
    have hdvd3 : 2 ^ (r - 2) ∣ m * (m + 1) := by
      have h := hdvd2
      rw [hpow] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) h
    have hpr : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      conv_lhs => rw [show r - 1 = (r - 2) + 1 by omega]
      rw [pow_succ, mul_comm]
    rcases Nat.even_or_odd m with hmeven | hmodd
    · have hm1odd : Odd (m + 1) := hmeven.add_one
      have hcopm1 : Nat.Coprime (2 ^ (r - 2)) (m + 1) := by
        rw [Nat.coprime_pow_left_iff (by omega : 0 < r - 2)]
        exact Nat.coprime_two_left.mpr hm1odd
      have hdvd3' : 2 ^ (r - 2) ∣ (m + 1) * m := by rw [mul_comm]; exact hdvd3
      have hdvd4 : 2 ^ (r - 2) ∣ m := Nat.Coprime.dvd_of_dvd_mul_left hcopm1 hdvd3'
      have hdvd5 : 2 ^ (r - 1) ∣ n - 1 := by
        have hnsub : n - 1 = 2 * m := by omega
        rw [hnsub, hpr]
        exact Nat.mul_dvd_mul_left 2 hdvd4
      obtain ⟨k, hk⟩ := hdvd5
      have hklt : k < 2 := by
        have h2r : 2 ^ r = 2 ^ (r - 1) * 2 := by
          rw [two_pow_eq_two_mul r (by omega), mul_comm]
        have hpos : 0 < 2 ^ (r - 1) := pow_pos (by norm_num) _
        have hlt : n - 1 < 2 ^ r := by omega
        rw [hk, h2r] at hlt
        exact (Nat.mul_lt_mul_left hpos).mp hlt
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with hk0 | hk1
      · exfalso
        have hzero : n - 1 = 0 := by rw [hk, hk0, mul_zero]
        have hn_eq : n = 1 := by omega
        have hα1 : α = 1 := by
          apply Units.ext
          rw [Units.val_one, ← hncast, hn_eq]
          norm_num
        rw [hα1, orderOf_one] at hord
        omega
      · left
        have hnval : n = 2 ^ (r - 1) + 1 := by rw [hk1, mul_one] at hk; omega
        rw [← hncast, hnval]
    · have hcopm : Nat.Coprime (2 ^ (r - 2)) m := by
        rw [Nat.coprime_pow_left_iff (by omega : 0 < r - 2)]
        exact Nat.coprime_two_left.mpr hmodd
      have hdvd4 : 2 ^ (r - 2) ∣ m + 1 := Nat.Coprime.dvd_of_dvd_mul_left hcopm hdvd3
      have hdvd5 : 2 ^ (r - 1) ∣ n + 1 := by
        have hnadd : n + 1 = 2 * (m + 1) := by omega
        rw [hnadd, hpr]
        exact Nat.mul_dvd_mul_left 2 hdvd4
      obtain ⟨k, hk⟩ := hdvd5
      have hkpos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · exfalso
          have hzero : n + 1 = 0 := by rw [hk, hk0, mul_zero]
          omega
        · exact hkpos
      have hkle : k ≤ 2 := by
        have h2r : 2 ^ r = 2 ^ (r - 1) * 2 := by
          rw [two_pow_eq_two_mul r (by omega), mul_comm]
        have hpos : 0 < 2 ^ (r - 1) := pow_pos (by norm_num) _
        have hle : n + 1 ≤ 2 ^ r := by omega
        rw [hk, h2r] at hle
        exact Nat.le_of_mul_le_mul_left hle hpos
      have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with hk1 | hk2
      · right; left
        have hnval : n = 2 ^ (r - 1) - 1 := by rw [hk1, mul_one] at hk; omega
        rw [← hncast, hnval]
      · right; right
        have h2r : 2 ^ r = 2 ^ (r - 1) * 2 := by
          rw [two_pow_eq_two_mul r (by omega), mul_comm]
        have hnval : n = 2 ^ r - 1 := by rw [hk2] at hk; rw [← h2r] at hk; omega
        rw [← hncast, hnval]
  · rintro (h1 | h2 | h3)
    · have hx1g : 1 < 2 ^ (r - 1) + 1 := by
        have h := Nat.one_le_two_pow (n := r - 1); omega
      have hx1l : 2 ^ (r - 1) + 1 < 2 ^ r := by
        have h2r := two_pow_eq_two_mul r (by omega)
        have hlt : 1 < 2 ^ (r - 1) := Nat.one_lt_two_pow (by omega)
        rw [h2r]; omega
      apply orderOf_eq_two_of_residue
      · rw [h1]; exact sq_zpow_add_one r hr
      · rw [h1]; exact natCast_ne_one_of_gt hx1g hx1l
    · have hx2g : 1 < 2 ^ (r - 1) - 1 := by
        have h4 : 4 ≤ 2 ^ (r - 1) := by
          have h := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega : 2 ≤ r - 1)
          simpa using h
        omega
      have hx2l : 2 ^ (r - 1) - 1 < 2 ^ r := by
        have hle : 2 ^ (r - 1) ≤ 2 ^ r :=
          Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega : r - 1 ≤ r)
        have hpos : 0 < 2 ^ (r - 1) := pow_pos (by norm_num : (0:ℕ) < 2) _
        omega
      apply orderOf_eq_two_of_residue
      · rw [h2]; exact sq_zpow_sub_one r hr
      · rw [h2]; exact natCast_ne_one_of_gt hx2g hx2l
    · have hx3g : 1 < 2 ^ r - 1 := by
        have h4 : 4 ≤ 2 ^ r := by
          have h := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) (by omega : 2 ≤ r)
          simpa using h
        omega
      have hx3l : 2 ^ r - 1 < 2 ^ r := by
        have hpos : 0 < 2 ^ r := pow_pos (by norm_num : (0:ℕ) < 2) _
        omega
      apply orderOf_eq_two_of_residue
      · rw [h3]; exact sq_pow_sub_one r
      · rw [h3]; exact natCast_ne_one_of_gt hx3g hx3l

/-- A unit modulo four has natural representative one or three. -/
theorem units_zmod_four_val (α : (ZMod 4)ˣ) :
    (α : ZMod 4).val = 1 ∨ (α : ZMod 4).val = 3 := by
  have hunit : IsUnit (α : ZMod 4) := α.isUnit
  have hcop : Nat.Coprime (α : ZMod 4).val 4 := by
    have haeq : (((α : ZMod 4).val : ℕ) : ZMod 4) = (α : ZMod 4) :=
      ZMod.natCast_zmod_val _
    rw [← haeq] at hunit
    exact (ZMod.isUnit_iff_coprime _ 4).mp hunit
  set n := (α : ZMod 4).val with hn
  have hlt : n < 4 := ZMod.val_lt _
  interval_cases n
  · simp [Nat.Coprime] at hcop
  · left; rfl
  · simp [Nat.Coprime] at hcop
  · right; rfl

/-- A unit modulo four has order two exactly when its residue is three. See [Inui and Le Gall,
2007, Proposition 4][InuiLeGall2007]. -/
theorem prop4_case_iii_two :
    ∀ α : (ZMod 4)ˣ, orderOf α = 2 ↔ (α : ZMod 4) = 3 := by
  intro α
  constructor
  · intro hord
    have hne : α ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    rcases units_zmod_four_val α with hv | hv
    · exfalso
      apply hne
      apply Units.ext
      rw [Units.val_one]
      have haeq : (((α : ZMod 4).val : ℕ) : ZMod 4) = (α : ZMod 4) :=
        ZMod.natCast_zmod_val _
      rw [← haeq, hv]
      norm_num
    · have haeq : (((α : ZMod 4).val : ℕ) : ZMod 4) = (α : ZMod 4) :=
        ZMod.natCast_zmod_val _
      rw [← haeq, hv]
      norm_num
  · intro hcoe
    have hpow : α ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, hcoe]
      decide
    have hne : α ≠ 1 := by
      intro h
      rw [h] at hcoe
      exact absurd hcoe (by decide)
    exact orderOf_eq_prime hpow hne

/-- If a unit modulo `p ^ r` has prime order `q`, then `q` divides `p - 1` or `r > 1` and `q =
p`. See [Inui and Le Gall, 2007, Proposition 4][InuiLeGall2007]. -/
theorem prop4_only_cases (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : 1 ≤ r)
    (α : (ZMod (p ^ r))ˣ) (hα : orderOf α = q) :
    q ∣ p - 1 ∨ (1 < r ∧ q = p) := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hdvd : orderOf α ∣ Fintype.card (ZMod (p ^ r))ˣ := orderOf_dvd_card
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hr] at hdvd
  have hq' : q ∣ p ^ (r - 1) * (p - 1) := by rw [← hα]; exact hdvd
  have hor : q ∣ p ^ (r - 1) ∨ q ∣ p - 1 := hq.dvd_mul.mp hq'
  rcases hor with hqpow | hpminus
  · have hqp : q = p := Nat.prime_eq_prime_of_dvd_pow hq hp hqpow
    refine Or.inr ⟨?_, hqp⟩
    by_contra hle
    have hr1 : r - 1 = 0 := by omega
    rw [hqp, hr1, pow_zero] at hqpow
    exact hp.not_dvd_one hqpow
  · exact Or.inl hpminus

end Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition4
