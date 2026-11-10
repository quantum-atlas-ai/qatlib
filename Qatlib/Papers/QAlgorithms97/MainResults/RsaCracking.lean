/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units

set_option autoImplicit false

namespace Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking

theorem rsa_order_pow_eq {N e : ℕ} [NeZero N] (P : (ZMod N)ˣ)
    (he : Nat.Coprime e (Nat.totient N)) :
    orderOf (P ^ e) = orderOf P := by
  have hdvd : orderOf P ∣ Nat.totient N := by
    rw [← ZMod.card_units_eq_totient N]
    exact orderOf_dvd_card
  have hcop : Nat.Coprime (orderOf P) e :=
    Nat.Coprime.of_dvd_left hdvd he.symm
  exact hcop.orderOf_pow

theorem rsa_recover_plaintext {N e d : ℕ} [NeZero N] (P : (ZMod N)ˣ)
    (hde : d * e ≡ 1 [MOD orderOf P]) :
    (P ^ e) ^ d = P := by
  rw [← pow_mul]
  have hde' : e * d ≡ 1 [MOD orderOf P] := by
    simpa [Nat.mul_comm] using hde
  rw [pow_eq_pow_of_modEq hde' (pow_orderOf_eq_one P)]
  simp

theorem rsa_cracking_order_argument {N e d : ℕ} [NeZero N] (P : (ZMod N)ˣ)
    (he : Nat.Coprime e (Nat.totient N))
    (hde : d * e ≡ 1 [MOD orderOf P]) :
    orderOf (P ^ e) = orderOf P ∧ (P ^ e) ^ d = P :=
  ⟨rsa_order_pow_eq P he, rsa_recover_plaintext P hde⟩

end Qatlib.Papers.QAlgorithms97.MainResults.RsaCracking
