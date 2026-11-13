/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms

/-!
# Discrete-logarithm divisibility counting contract

This module defines `DlogPrimePowerDivisibility` for prime `p ≥ 3` and `p < q < 2 * p`. The
contract asserts injectivity of `dlogCprime` on small-residue coordinates and bounds these
integer values between zero and `p - 1`.

For every divisor `w ≥ 2` of `p - 1`, it also bounds the number of small-residue coordinates
having coefficient divisible by `w` by `(p - 1) / w + 1`. The contract describes the
divisibility-counting ingredient of the discrete-logarithm recovery analysis in [Shor1997].

## Main statements

* `DlogPrimePowerDivisibility`: the corrected injectivity, range, and divisor-count proposition.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open scoped Classical

/-- For prime `p ≥ 3` and `p < q < 2 * p`, asserts injectivity of `dlogCprime` on small-residue
coordinates, values in `[0, p - 1]`, and at most `(p - 1) / w + 1` such coordinates
divisible by each divisor `w ≥ 2` of `p - 1`. -/
def DlogPrimePowerDivisibility : Prop :=
  ∀ (p q : ℕ) [NeZero p], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → q < 2 * p →
    (∀ c₁ c₂ : Fin q, dlogSmallResidue p q c₁ → dlogSmallResidue p q c₂ →
        dlogCprime p q c₁ = dlogCprime p q c₂ → c₁ = c₂) ∧
    (∀ c : Fin q, dlogSmallResidue p q c →
        0 ≤ dlogCprime p q c ∧ dlogCprime p q c ≤ (p - 1 : ℕ)) ∧
    (∀ w : ℕ, 2 ≤ w → w ∣ p - 1 →
        (Finset.univ.filter fun c : Fin q =>
            dlogSmallResidue p q c ∧ (w : ℤ) ∣ dlogCprime p q c).card
          ≤ (p - 1) / w + 1)

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
