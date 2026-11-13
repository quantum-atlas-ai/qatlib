/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms

/-!
# Common-divisor tail contract

Defines `DlogTSampleTail`, the probability bound for a common prime-power divisor greater than
18 across independent uniform good samples. The contract includes both a divisor-sum estimate
and a strict one-half bound from twelve samples onward, for the discrete-logarithm setting of
[Shor1997].

## Main statements

* `DlogTSampleTail`: Specifies the divisor-sum and constant-probability tail bounds.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open Qatlib

/-- The common prime-power divisibility contract for uniform good samples: a divisor-sum bound
for every sample count and a strict one-half bound for counts at least twelve, under the
stated prime and modulus assumptions. -/
def DlogTSampleTail : Prop :=
  ∀ (p q t : ℕ) [NeZero p] [NeZero q], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → q < 2 * p →
    (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q)
      ≤ ∑ w ∈ (Nat.divisors (p - 1)).filter
            (fun w => dlogIsPrimePower w ∧ 18 < w),
          ((((p - 1) / w + 1 : ℕ) : ℝ) / ((q / 12 : ℕ) : ℝ)) ^ t ∧
    (12 ≤ t →
      (dlogUniformGoodLaw p q).probEvent (L := t) (dlogCommonPpDivides p q)
        < 1 / 2)

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
