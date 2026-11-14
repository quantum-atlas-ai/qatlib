/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Tactic

@[expose] public section

/-!
# Counting elements of prescribed order modulo a prime

This module counts units of each order dividing `p - 1` in the cyclic group of units modulo a
prime. It specializes the count to generators and expresses their proportion among all units as
a totient ratio, as used in order-based primality testing [DonisVelaGarciaEscartin2017].

## Main statements

* `card_units_orderOf_eq_totient`: There are φ(d) units of order d when d divides p - 1.
* `order_pred_fraction`: The full-order fraction is φ(N - 1) / (N - 1).

## References

* [Donis-Vela and Garcia-Escartin, 2017][DonisVelaGarciaEscartin2017]
-/

set_option autoImplicit false
open scoped Finset
namespace Qatlib.Foundations.OrderPrimality.GeneratorCount

/-- For prime `p` and `d ∣ p - 1`, exactly `Nat.totient d` units modulo `p` have order `d`. See
[DonisVelaGarciaEscartin2017]. -/
theorem card_units_orderOf_eq_totient {p d : ℕ} [NeZero p] (hp : p.Prime)
    (hd : d ∣ p - 1) :
    #{a : (ZMod p)ˣ | orderOf a = d} = Nat.totient d := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  refine IsCyclic.card_orderOf_eq_totient ?_
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  exact hd

/-- For prime `N`, the number of units modulo `N` of order `N - 1` is `Nat.totient (N - 1)`. -/
theorem card_order_pred_eq_totient {N : ℕ} [NeZero N] (hN : N.Prime) :
    #{a : (ZMod N)ˣ | orderOf a = N - 1} = Nat.totient (N - 1) :=
  card_units_orderOf_eq_totient hN dvd_rfl

/-- For prime `N`, the fraction of all units with order `N - 1` is φ(N - 1) / (N - 1). See
[DonisVelaGarciaEscartin2017]. -/
theorem order_pred_fraction {N : ℕ} [NeZero N] (hN : N.Prime) :
    ((#{a : (ZMod N)ˣ | orderOf a = N - 1} : ℕ) : ℚ) /
        ((Fintype.card (ZMod N)ˣ : ℕ) : ℚ)
      = (Nat.totient (N - 1) : ℚ) / (((N - 1 : ℕ)) : ℚ) := by
  have : Fact N.Prime := ⟨hN⟩
  rw [card_order_pred_eq_totient hN, ZMod.card_units_eq_totient, Nat.totient_prime hN]

end Qatlib.Foundations.OrderPrimality.GeneratorCount
