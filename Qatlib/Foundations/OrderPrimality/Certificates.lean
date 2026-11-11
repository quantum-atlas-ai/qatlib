/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Logic.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

/-!
# Order and congruence certificates for primality

Proves three arithmetic certificates relevant to order-based primality testing. For `N ≥ 2`, a
unit modulo `N` of order `N - 1` proves primality; a unit violating the Fermat congruence or a
positive integer below `N` with nontrivial gcd proves nonprimality. See
[DonisVelaGarciaEscartin2017] for related background.

## Main statements

* `orderOf_eq_pred_prime`: If `N ≥ 2` and a unit modulo `N` has multiplicative order `N - 1`,
  then `N` is prime [DonisVelaGarciaEscartin2017].
* `fermat_witness_not_prime`: A unit modulo `N` whose `(N - 1)`st power is not one proves that
  `N` is not prime [Donis-Vela and Garcia-Escartin, Theorem 1][DonisVelaGarciaEscartin2017].

## References

* [Donis-Vela and Garcia-Escartin, 2017][DonisVelaGarciaEscartin2017]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.OrderPrimality.Certificates

open Asymptotics Filter

/-- If `N ≥ 2` and a unit modulo `N` has multiplicative order `N - 1`, then `N` is prime
[DonisVelaGarciaEscartin2017]. -/
theorem orderOf_eq_pred_prime {N : ℕ} (hN : 2 ≤ N) (a : (ZMod N)ˣ)
    (hord : orderOf a = N - 1) : Nat.Prime N := by
  haveI : NeZero N := ⟨by omega⟩

  have hdvd : N - 1 ∣ Nat.totient N := by
    rw [← hord, ← ZMod.card_units_eq_totient N]
    exact orderOf_dvd_card

  have hpos : 0 < Nat.totient N := Nat.totient_pos.mpr (by omega)
  have hle : Nat.totient N ≤ N - 1 := Nat.le_sub_one_of_lt (Nat.totient_lt N (by omega))
  have htot : Nat.totient N = N - 1 := le_antisymm hle (Nat.le_of_dvd hpos hdvd)

  rw [Nat.prime_iff_card_units N, ZMod.card_units_eq_totient N, htot]

/-- A unit modulo `N` whose `(N - 1)`st power is not one proves that `N` is not prime
[Donis-Vela and Garcia-Escartin, Theorem 1][DonisVelaGarciaEscartin2017]. -/
theorem fermat_witness_not_prime {N : ℕ} (a : (ZMod N)ˣ)
    (hw : a ^ (N - 1) ≠ 1) : ¬ Nat.Prime N := by
  intro hp
  haveI : Fact N.Prime := ⟨hp⟩
  exact hw (ZMod.units_pow_card_sub_one_eq_one N a)

/-- If `0 < a < N` and `Nat.gcd a N ≠ 1`, then `N` is not prime [DonisVelaGarciaEscartin2017]. -/
theorem gcd_witness_not_prime {N a : ℕ} (ha : 0<a) (haN : a<N)
    (hw : Nat.gcd a N ≠ 1) : ¬N.Prime := by
  intro hp
  have hd : ¬N ∣ a := Nat.not_dvd_of_pos_of_lt ha haN
  have hc : Nat.Coprime a N := (hp.coprime_iff_not_dvd.mpr hd).symm
  exact hw hc.gcd_eq_one

end Qatlib.Foundations.OrderPrimality.Certificates
