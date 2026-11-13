/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogDivBudget.DlogRecoveryPrograms

/-!
# Uniform-good divisibility contract

Defines `DlogUniformGoodDivisibility`, a bound on the probability that a divisor of `p - 1`
divides the recovered integer `dlogCprime`. Its scaled form avoids dividing by `q / 12` and
supports the discrete-logarithm divisor estimates associated with [Shor1997].

## Main statements

* `DlogUniformGoodDivisibility`: Specifies the scaled single-sample divisibility bound.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogDivBudget

open Qatlib

/-- For the stated prime and modulus range and each divisor `w ≥ 2` of `p - 1`, requires the
divisibility probability multiplied by `q / 12` to be at most `(p - 1) / w + 1`. -/
def DlogUniformGoodDivisibility : Prop :=
  ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Prime p → 3 ≤ p → (p : ℕ) < q → q < 2 * p →
    ∀ w : ℕ, 2 ≤ w → w ∣ p - 1 →
      (dlogUniformGoodLaw p q).probEvent (L := 1)
          (fun ω => (w : ℤ) ∣ dlogCprime p q (ω 0).val)
        * ((q / 12 : ℕ) : ℝ) ≤ (((p - 1) / w + 1 : ℕ) : ℝ)

end Qatlib.Concepts.PeriodSampling.DlogDivBudget
