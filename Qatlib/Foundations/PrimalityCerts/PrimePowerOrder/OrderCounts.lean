/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Unit orders and prime extraction from prime powers

This module counts order-divisibility events in finite cyclic groups and applies them to units
modulo odd prime powers. It shows that sufficiently large p-power divisibility of an exact order
makes the gcd postprocessing recover `p`, and bounds both the order event and successful
extraction below by 2/3, as in [ChauLo1995].

## Main statements

* `filter_card_orderOf_dvd`: The order-divisibility count in a finite cyclic group is a gcd.
* `prime_power_gcd`: A suitable exact order recovers the prime base by gcd postprocessing.
* `prime_power_extraction_probability`: At least two thirds of the units yield the prime base
  for odd p and n ≥ 2.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.PrimalityCerts.PrimePowerOrder

/-- If `r ∣ p ^ (n - 1) * (p - 1)` for prime `p` and `n ≥ 2`, but `p ^ (n - 1)` does not divide
`r`, then `r ∣ p ^ (n - 2) * (p - 1)`. -/
lemma dvd_of_not_dvd_prime_pow_mul {p n r : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hr : r ∣ p ^ (n - 1) * (p - 1)) (hnot : ¬ p ^ (n - 1) ∣ r) :
    r ∣ p ^ (n - 2) * (p - 1) := by
  have hp2 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have hbig_ne : p ^ (n - 1) * (p - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by have := hp.two_le; omega)
  have htarget_ne : p ^ (n - 2) * (p - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by have := hp.two_le; omega)
  have hr_ne : r ≠ 0 := by
    intro h
    exact hbig_ne (Nat.eq_zero_of_zero_dvd (h ▸ hr))
  have hbig_eq : p ^ (n - 1) * (p - 1) = p * (p ^ (n - 2) * (p - 1)) := by
    have hpn : p ^ (n - 1) = p ^ (n - 2) * p := by
      have h : n - 1 = (n - 2) + 1 := by omega
      rw [h, pow_succ]
    rw [hpn]; ring
  rw [← Nat.factorization_le_iff_dvd hr_ne htarget_ne]
  intro q
  have hle : r.factorization q ≤ (p ^ (n - 1) * (p - 1)).factorization q :=
    (Nat.factorization_le_iff_dvd hr_ne hbig_ne).mpr hr q
  rw [hbig_eq, Nat.factorization_mul hp.pos.ne' htarget_ne, Finsupp.add_apply] at hle
  by_cases hqp : q = p
  · rw [hqp]
    have hrfac : r.factorization p ≤ n - 2 := by
      have hnp : ¬ (n - 1 ≤ r.factorization p) := by
        intro hle2
        exact hnot ((hp.pow_dvd_iff_le_factorization hr_ne).mpr hle2)
      omega
    have htgt : (p ^ (n - 2) * (p - 1)).factorization p = n - 2 := by
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
        (by have := hp.two_le; omega : p - 1 ≠ 0)]
      simp only [Finsupp.add_apply, Nat.factorization_pow_self hp,
        Nat.factorization_eq_zero_of_lt (by have := hp.two_le; omega : p - 1 < p),
        add_zero]
    rw [htgt]
    exact hrfac
  · have hpfac : p.factorization q = 0 := by
      rw [Nat.Prime.factorization hp, Finsupp.single_apply, if_neg (Ne.symm hqp)]
    rw [hpfac, zero_add] at hle
    exact hle

/-- For a unit modulo `p ^ n` with `p` prime and `n ≥ 1`, divisibility of its order by `p ^ (n -
1)` implies that `p ^ n / Nat.gcd (p ^ n) (orderOf m) = p`. See [ChauLo1995]. -/
theorem prime_power_gcd
    (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (m : (ZMod (p ^ n))ˣ) (hr : p ^ (n - 1) ∣ orderOf m) :
    p ^ n / Nat.gcd (p ^ n) (orderOf m) = p := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hcard : Fintype.card (ZMod (p ^ n))ˣ = p ^ (n - 1) * (p - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega)]
  have hrdvd : orderOf m ∣ p ^ (n - 1) * (p - 1) := by
    have h := orderOf_dvd_card (x := m)
    rwa [hcard] at h
  obtain ⟨s, hs⟩ := hr
  have hs_dvd : s ∣ p - 1 := by
    have hbig : p ^ (n - 1) * s ∣ p ^ (n - 1) * (p - 1) := by
      rw [← hs]; exact hrdvd
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos (n - 1))).mp hbig
  have hpn : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hgcd : Nat.gcd (p ^ n) (orderOf m) = p ^ (n - 1) := by
    rw [hs, hpn, Nat.gcd_mul_left]
    have hcp : Nat.Coprime p s := by
      rw [hp.coprime_iff_not_dvd]
      intro hpd
      have hp_dvd_pm1 : p ∣ p - 1 := dvd_trans hpd hs_dvd
      have h1 : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) hp_dvd_pm1
      have h2 : p - (p - 1) = 1 := by have := hp.two_le; omega
      rw [h2] at h1
      exact hp.not_dvd_one h1
    rw [hcp.gcd_eq_one, mul_one]
  rw [hgcd, hpn]
  exact Nat.mul_div_cancel_left p (pow_pos hp.pos (n - 1))

/-- In a finite cyclic commutative group, the number of elements whose order divides `D` equals
the gcd of the group cardinality and `D`. -/
lemma filter_card_orderOf_dvd (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G]
    (D : ℕ) :
    (Finset.univ.filter (fun m : G => orderOf m ∣ D)).card =
      Nat.gcd (Fintype.card G) D := by
  classical
  have h1 : (Finset.univ.filter (fun m : G => orderOf m ∣ D)).card =
      Fintype.card {m : G // orderOf m ∣ D} :=
    (Fintype.card_subtype (fun m : G => orderOf m ∣ D)).symm
  rw [h1]
  have h2 : Fintype.card {m : G // orderOf m ∣ D} =
      Nat.card (powMonoidHom D : G →* G).ker := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl G) ?_)
    intro m
    simp only [Equiv.refl_apply, MonoidHom.mem_ker, powMonoidHom_apply,
      orderOf_dvd_iff_pow_eq_one]
  rw [h2, IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card]

/-- For odd prime `p` and `n ≥ 2`, at least two thirds of the units modulo `p ^ n` have order
divisible by `p ^ (n - 1)`. -/
theorem prime_power_probability
    (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n) :
    (2 : ℚ) / 3 ≤
      (Nat.card {m : (ZMod (p ^ n))ˣ // p ^ (n - 1) ∣ orderOf m} : ℚ) /
        (Nat.card (ZMod (p ^ n))ˣ : ℚ) := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  haveI hcyc : IsCyclic (ZMod (p ^ n))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set D : ℕ := p ^ (n - 2) * (p - 1) with hD
  have hDne : D ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by have := hp.two_le; omega)
  have hcard : Fintype.card (ZMod (p ^ n))ˣ = p ^ (n - 1) * (p - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by omega)]
  have hcardpos_nat : 0 < Fintype.card (ZMod (p ^ n))ˣ := by
    rw [hcard]
    exact Nat.mul_pos (pow_pos hp.pos _) (by have := hp.two_le; omega)
  have hcard_eq : Fintype.card (ZMod (p ^ n))ˣ = p * D := by
    rw [hcard, hD]
    have hpn : p ^ (n - 1) = p ^ (n - 2) * p := by
      have h : n - 1 = (n - 2) + 1 := by omega
      rw [h, pow_succ]
    rw [hpn]; ring
  have hDdvd : D ∣ Fintype.card (ZMod (p ^ n))ˣ :=
    ⟨p, by rw [hcard_eq, mul_comm]⟩
  have hpart : (Finset.univ.filter
        (fun m : (ZMod (p ^ n))ˣ => p ^ (n - 1) ∣ orderOf m)).card +
      (Finset.univ.filter
        (fun m : (ZMod (p ^ n))ˣ => ¬ p ^ (n - 1) ∣ orderOf m)).card =
      Fintype.card (ZMod (p ^ n))ˣ := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hbad_eq : (Finset.univ.filter
        (fun m : (ZMod (p ^ n))ˣ => ¬ p ^ (n - 1) ∣ orderOf m)) =
      Finset.univ.filter (fun m : (ZMod (p ^ n))ˣ => orderOf m ∣ D) := by
    apply Finset.filter_congr
    intro m _
    have hrdvd : orderOf m ∣ p ^ (n - 1) * (p - 1) := by
      have h := orderOf_dvd_card (x := m)
      rwa [hcard] at h
    constructor
    · intro hnot
      exact dvd_of_not_dvd_prime_pow_mul hp hn hrdvd hnot
    · intro hd hdvd
      have hDfac : D.factorization p = n - 2 := by
        rw [hD, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
          (by have := hp.two_le; omega : p - 1 ≠ 0)]
        simp only [Finsupp.add_apply, Nat.factorization_pow_self hp,
          Nat.factorization_eq_zero_of_lt (by have := hp.two_le; omega : p - 1 < p),
          add_zero]
      have hDvd : p ^ (n - 1) ∣ D := dvd_trans hdvd hd
      have hle : n - 1 ≤ D.factorization p :=
        (hp.pow_dvd_iff_le_factorization hDne).mp hDvd
      omega
  have hbad_card : (Finset.univ.filter
        (fun m : (ZMod (p ^ n))ˣ => ¬ p ^ (n - 1) ∣ orderOf m)).card = D := by
    rw [hbad_eq, filter_card_orderOf_dvd]
    exact Nat.gcd_eq_right hDdvd
  have hDle : D ≤ Fintype.card (ZMod (p ^ n))ˣ :=
    Nat.le_of_dvd hcardpos_nat hDdvd
  have hgood_card : (Finset.univ.filter
        (fun m : (ZMod (p ^ n))ˣ => p ^ (n - 1) ∣ orderOf m)).card =
      Fintype.card (ZMod (p ^ n))ˣ - D := by
    have hsub := Nat.eq_sub_of_add_eq hpart
    rw [hsub, hbad_card]
  have h3D : 3 * D ≤ Fintype.card (ZMod (p ^ n))ˣ := by
    rw [hcard_eq]
    exact Nat.mul_le_mul_right D (by have := hp.two_le; omega : 3 ≤ p)
  have hcardpos : (0 : ℚ) < (Fintype.card (ZMod (p ^ n))ˣ : ℚ) := by
    exact_mod_cast hcardpos_nat
  rw [le_div_iff₀ hcardpos]
  have hgoodq : (((Finset.univ.filter
        (fun m : (ZMod (p ^ n))ˣ => p ^ (n - 1) ∣ orderOf m)).card : ℕ) : ℚ) =
      (Fintype.card (ZMod (p ^ n))ˣ : ℚ) - (D : ℚ) := by
    rw [hgood_card, Nat.cast_sub hDle]
  have h3Dq : (3 : ℚ) * (D : ℚ) ≤ (Fintype.card (ZMod (p ^ n))ˣ : ℚ) := by
    exact_mod_cast h3D
  rw [hgoodq]
  nlinarith [h3Dq]

/-- For odd prime `p` and `n ≥ 2`, at least two thirds of the units modulo `p ^ n` recover `p`
by dividing `p ^ n` by its gcd with the unit's order. -/
theorem prime_power_extraction_probability
    (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n) :
    (2 : ℚ) / 3 ≤
      (Nat.card {m : (ZMod (p ^ n))ˣ //
        p ^ n / Nat.gcd (p ^ n) (orderOf m) = p} : ℚ) /
        (Nat.card (ZMod (p ^ n))ˣ : ℚ) := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hc : Nat.card {m : (ZMod (p ^ n))ˣ // p ^ (n - 1) ∣ orderOf m} ≤
      Nat.card {m : (ZMod (p ^ n))ˣ // p ^ n / Nat.gcd (p ^ n) (orderOf m) = p} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective
      (fun m => ⟨m.val, prime_power_gcd p n hp (by omega) m.val m.property⟩)
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {m : (ZMod (p ^ n))ˣ //
          p ^ n / Nat.gcd (p ^ n) (orderOf m) = p} => z.val) h)
  exact (prime_power_probability p n hp hp2 hn).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _))

end Qatlib.Foundations.PrimalityCerts.PrimePowerOrder
