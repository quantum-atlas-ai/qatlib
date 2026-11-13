/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms

/-!
# Good-pair candidate recovery contract

This module defines `DlogCandidateRecovery`, an existence statement for integer candidates
obtained from a good discrete-logarithm sampling pair. For prime `p ≥ 3`, `p < q`, and `r < p -
1`, the candidate lies within one half of the scaled second coordinate and satisfies a
congruence modulo `p - 1`.

The contract also records existence of a congruent exponent candidate under the specified
coprimality condition. It expresses part of the rounding and division step discussed in
[Shor1997].

## Main statements

* `DlogCandidateRecovery`: the integer rounding and modular candidate-existence proposition.

## References

* [Shor, 1997, Section 6][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogCRTRecovery

/-- For prime `p ≥ 3`, `p < q`, and `r < p - 1`, every good pair has an integer rounding
candidate within one half of `d * (p - 1) / q` satisfying the recovery congruence. Under the
stated coprimality condition, a congruent exponent candidate in the required range also
exists. -/
def DlogCandidateRecovery : Prop :=
  ∀ (p q r : ℕ), Nat.Prime p → 3 ≤ p → (p : ℕ) < q → r < p - 1 →
    ∀ c d : Fin q, dlogGoodPair p q r c d →
      (∃ dprime : ℤ,
          |((dprime : ℝ) - ((d : ℕ) * (p - 1) : ℝ) / (q : ℝ))| ≤ 1 / 2 ∧
          ((dprime + r * dlogCprime p q c : ℤ) : ℤ) % ((p - 1 : ℕ) : ℤ) = 0 ∧
          (Nat.gcd (dlogCprime p q c).natAbs (p - 1) = 1 →
            ∃ r' : ℕ, r' < p - 1 ∧
              ((r' : ℤ) * dlogCprime p q c + dprime) % ((p - 1 : ℕ) : ℤ) = 0 ∧
              (r' : ℤ) ≡ (r : ℤ) [ZMOD ((p - 1 : ℕ) : ℤ)]))

end Qatlib.Concepts.PeriodSampling.DlogCRTRecovery
