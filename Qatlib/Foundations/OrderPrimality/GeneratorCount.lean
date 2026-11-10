/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

set_option autoImplicit false
open scoped Finset
namespace Qatlib.Foundations.OrderPrimality.GeneratorCount

theorem card_units_orderOf_eq_totient {p d : ℕ} [NeZero p] (hp : p.Prime)
    (hd : d ∣ p - 1) :
    #{a : (ZMod p)ˣ | orderOf a = d} = Nat.totient d := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  refine IsCyclic.card_orderOf_eq_totient ?_
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  exact hd

theorem card_order_pred_eq_totient {N : ℕ} [NeZero N] (hN : N.Prime) :
    #{a : (ZMod N)ˣ | orderOf a = N - 1} = Nat.totient (N - 1) :=
  card_units_orderOf_eq_totient hN dvd_rfl

theorem order_pred_fraction {N : ℕ} [NeZero N] (hN : N.Prime) :
    ((#{a : (ZMod N)ˣ | orderOf a = N - 1} : ℕ) : ℚ) /
        ((Fintype.card (ZMod N)ˣ : ℕ) : ℚ)
      = (Nat.totient (N - 1) : ℚ) / (((N - 1 : ℕ)) : ℚ) := by
  haveI : Fact N.Prime := ⟨hN⟩
  rw [card_order_pred_eq_totient hN, ZMod.card_units_eq_totient, Nat.totient_prime hN]

end Qatlib.Foundations.OrderPrimality.GeneratorCount
