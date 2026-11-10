/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.OrderCounts

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.PrimalityCerts.PrimePowerOrder

theorem primePower_log (p n : ℕ) (hp : p.Prime) : Nat.log p (p ^ n) = n :=
  Nat.log_pow hp.one_lt n

theorem primePower_factorization (p n M : ℕ) (hp : p.Prime) (hM : M = p ^ n) :
    p ^ Nat.log p M = M := by
  subst hM
  rw [primePower_log p n hp]

theorem primePower_exponent_unique (p a b : ℕ) (hp : p.Prime) (h : p ^ a = p ^ b) :
    a = b :=
  Nat.pow_right_injective hp.one_lt h

def factorPrimePower (p M : ℕ) : Option ℕ :=
  if 1 < p ∧ p ^ Nat.log p M = M then some (Nat.log p M) else none

theorem factorPrimePower_eq_some (p n M : ℕ) (hp : p.Prime) (hM : M = p ^ n) :
    factorPrimePower p M = some n := by
  subst hM
  unfold factorPrimePower
  rw [primePower_log p n hp]
  simp [hp.one_lt]

theorem primePower_exponent_eq_log (p n M : ℕ) (hp : p.Prime) (hM : M = p ^ n) :
    Nat.log p M = n := by
  subst hM
  exact primePower_log p n hp

end Qatlib.Foundations.PrimalityCerts.PrimePowerOrder
