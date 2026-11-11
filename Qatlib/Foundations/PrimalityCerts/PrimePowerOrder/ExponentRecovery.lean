/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PrimalityCerts.PrimePowerOrder.OrderCounts

/-!
# Recovering the exponent of a known prime power

Once the prime base of `M = p ^ n` is known, `Nat.log p M` recovers its exponent uniquely. This
module defines the checked procedure `factorPrimePower` and proves its correctness on prime
powers, formalizing the deterministic exponent-recovery step in [ChauLo1995].

## Main statements

* `primePower_log`: The base-p natural logarithm of pⁿ is n for prime p.
* `factorPrimePower_eq_some`: The checked procedure returns the known exponent.
* `primePower_exponent_unique`: Powers of a fixed prime have unique exponents.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.PrimalityCerts.PrimePowerOrder

/-- For prime `p`, the natural logarithm of `p ^ n` to base `p` is `n`. -/
theorem primePower_log (p n : ℕ) (hp : p.Prime) : Nat.log p (p ^ n) = n :=
  Nat.log_pow hp.one_lt n

/-- If `M = p ^ n` with `p` prime, raising `p` to `Nat.log p M` reconstructs `M`. See
[ChauLo1995]. -/
theorem primePower_factorization (p n M : ℕ) (hp : p.Prime) (hM : M = p ^ n) :
    p ^ Nat.log p M = M := by
  subst hM
  rw [primePower_log p n hp]

/-- Equal powers of a fixed prime have equal natural-number exponents. See [ChauLo1995]. -/
theorem primePower_exponent_unique (p a b : ℕ) (hp : p.Prime) (h : p ^ a = p ^ b) :
    a = b :=
  Nat.pow_right_injective hp.one_lt h

/-- Return `some (Nat.log p M)` when `1 < p` and exponentiating that logarithm reconstructs `M`;
otherwise return `none`. -/
def factorPrimePower (p M : ℕ) : Option ℕ :=
  if 1 < p ∧ p ^ Nat.log p M = M then some (Nat.log p M) else none

/-- For prime `p` and `M = p ^ n`, `factorPrimePower p M` returns `some n`. See [ChauLo1995]. -/
theorem factorPrimePower_eq_some (p n M : ℕ) (hp : p.Prime) (hM : M = p ^ n) :
    factorPrimePower p M = some n := by
  subst hM
  unfold factorPrimePower
  rw [primePower_log p n hp]
  simp [hp.one_lt]

/-- If `M = p ^ n` with `p` prime, its base-p natural logarithm equals `n`. -/
theorem primePower_exponent_eq_log (p n M : ℕ) (hp : p.Prime) (hM : M = p ^ n) :
    Nat.log p M = n := by
  subst hM
  exact primePower_log p n hp

end Qatlib.Foundations.PrimalityCerts.PrimePowerOrder
