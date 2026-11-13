/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms

/-!
# CRT recovery uniqueness contract

This module defines `DlogCrtRecovery`, the modular uniqueness contract for discrete-logarithm
recovery. The target and competing exponents are both below `p - 1` and satisfy the same sampled
linear congruences.

For prime divisors above eighteen, the contract requires a sampled coefficient not divisible by
that prime; for smaller prime divisors, it requires agreement modulo the full prime-power factor
of `p - 1`. These conditions formalize a CRT recovery step in the setting of [Shor1997].

## Main statements

* `DlogCrtRecovery`: uniqueness from sampled congruences, large-prime witnesses, and
  small-prime-power residues.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogCRTRecovery

open Qatlib

/-- For prime `p ≥ 3`, `p < q`, and target exponent `r < p - 1`, the sampling congruences
uniquely specify a competing exponent in that range when large prime divisors have
nondivisibility witnesses and small prime-power residues agree. -/
def DlogCrtRecovery : Prop :=
  ∀ (p q r : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → r < p - 1 →
    ∀ (t : ℕ) (c : Fin t → Fin q) (d' : Fin t → ℤ),
      (∀ i, (d' i + r * dlogCprime p q (c i) : ℤ)
          % ((p - 1 : ℕ) : ℤ) = 0) →
      (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ p - 1 → 18 < ℓ →
          ∃ i, ¬ (ℓ : ℤ) ∣ dlogCprime p q (c i)) →
      ∀ r' : ℕ, r' < p - 1 →
        (∀ i, (d' i + r' * dlogCprime p q (c i) : ℤ)
            % ((p - 1 : ℕ) : ℤ) = 0) →
        (∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ∣ p - 1 → ℓ ≤ 18 →
            r' % ℓ ^ ((p - 1).factorization ℓ)
              = r % ℓ ^ ((p - 1).factorization ℓ)) →
        r' = r

end Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
