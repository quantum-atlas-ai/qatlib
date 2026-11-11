/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Associated

/-!
# Lucas primality certificates with separate witnesses

This module proves a Lucas primality criterion allowing a different modular witness for each
prime divisor of `N - 1`. Valuation comparisons combine the separate order witnesses into a
divisibility statement, and `separateLucasProduct` accepts an explicit prime-power product for
`N - 1`; this certificate framework is relevant to quantum primality testing [ChauLo1995].

## Main statements

* `forcedValuation`: Failure to divide m/q forces the full q-adic exponent of m.
* `separateLucas`: Separate witnesses for the prime divisors of N - 1 imply primality.
* `separateLucasProduct`: A prime-power product supplies the factors for the criterion.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false

namespace Qatlib.Foundations.PrimalityCerts.LucasTests

/-- If `d ∣ m` but `d` does not divide `m / q`, where `q` is a prime divisor of nonzero `m`, the
q-adic exponent of `m` is at most that of `d`. -/
theorem forcedValuation {m d q : ℕ} (hm : m ≠ 0) (hq : q.Prime)
    (hqm : q ∣ m) (hdm : d ∣ m) (hnot : ¬ d ∣ m / q) :
    m.factorization q ≤ d.factorization q := by
  have hd : d ≠ 0 := by rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd hdm)
  have hdiv : m / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hqm) hq.pos).ne'
  have hle := (Nat.factorization_le_iff_dvd hd hm).mpr hdm
  by_contra h
  apply hnot
  apply (Nat.factorization_le_iff_dvd hd hdiv).mp
  intro p
  rw [Nat.factorization_div hqm, Finsupp.tsub_apply]
  by_cases hp : p = q
  · subst p
    rw [hq.factorization_self]
    omega
  · have hzero : q.factorization p = 0 := by
      rw [Nat.Prime.factorization hq, Finsupp.single_apply, if_neg (Ne.symm hp)]
    rw [hzero, Nat.sub_zero]
    exact hle p

/-- Nonzero `m` divides nonzero `c` if each prime divisor `q` of `m` has a common divisor of `m`
and `c` that does not divide `m / q`. -/
theorem dvd_fromSeparateWitnesses {m c : ℕ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hw : ∀ q : ℕ, q.Prime → q ∣ m →
      ∃ d : ℕ, d ∣ m ∧ d ∣ c ∧ ¬ d ∣ m / q) : m ∣ c := by
  apply (Nat.factorization_prime_le_iff_dvd hm hc).mp
  intro q hq
  by_cases hqm : q ∣ m
  · obtain ⟨d, hdm, hdc, hn⟩ := hw q hq hqm
    have hd : d ≠ 0 := by rintro rfl; exact hm (Nat.eq_zero_of_zero_dvd hdm)
    exact (forcedValuation hm hq hqm hdm hn).trans
      ((Nat.factorization_le_iff_dvd hd hc).mpr hdc q)
  · rw [Nat.factorization_eq_zero_of_not_dvd hqm]
    exact Nat.zero_le _

/-- The Lucas criterion with a separate witness for each prime divisor of `N - 1`: witnesses
satisfying the full-power equality and reduced-power inequality imply `N.Prime`. -/
theorem separateLucas (N : ℕ)
    (hw : ∀ q : ℕ, q.Prime → q ∣ N - 1 →
      ∃ a : ZMod N, a ^ (N - 1) = 1 ∧ a ^ ((N - 1) / q) ≠ 1) : N.Prime := by
  classical
  have hN : 1 < N := by
    by_contra h
    have hz : N - 1 = 0 := by omega
    obtain ⟨a, _, ha⟩ := hw 2 Nat.prime_two (by rw [hz]; exact dvd_zero _)
    simp [hz] at ha
  haveI : NeZero N := ⟨by omega⟩
  rw [Nat.prime_iff_card_units]
  apply (Nat.card_units_zmod_lt_sub_one hN).antisymm
  have hdiv : N - 1 ∣ Fintype.card (ZMod N)ˣ := by
    apply dvd_fromSeparateWitnesses (by omega) Fintype.card_ne_zero
    intro q hq hqd
    obtain ⟨a, ha, han⟩ := hw q hq hqd
    let u : (ZMod N)ˣ := Units.mkOfMulEqOne a _
      (by rwa [← pow_succ', tsub_add_eq_add_tsub hN])
    have horder : orderOf a = orderOf u := orderOf_injective (Units.coeHom _) Units.val_injective u
    refine ⟨orderOf u, ?_, orderOf_dvd_card, ?_⟩
    · rw [← horder]
      exact orderOf_dvd_of_pow_eq_one ha
    · intro hd
      apply han
      exact orderOf_dvd_iff_pow_eq_one.mp (horder ▸ hd)
  exact Nat.le_of_dvd Fintype.card_pos hdiv

/-- If `N - 1` is the specified product of prime powers and each listed prime has a Lucas
witness, then `N` is prime. -/
theorem separateLucasProduct (N : ℕ) (S : Finset ℕ) (β : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hfactor : N - 1 = ∏ p ∈ S, p ^ β p)
    (hw : ∀ p ∈ S, ∃ a : ZMod N,
      a ^ (N - 1) = 1 ∧ a ^ ((N - 1) / p) ≠ 1) : N.Prime := by
  apply separateLucas N
  intro q hq hqd
  rw [hfactor] at hqd
  obtain ⟨p, hp, hqp⟩ := ((Nat.prime_iff.mp hq).dvd_finsetProd_iff _).mp hqd
  have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hq (hprime p hp)).mp
    (hq.dvd_of_dvd_pow hqp)
  subst q
  exact hw p hp

end Qatlib.Foundations.PrimalityCerts.LucasTests
