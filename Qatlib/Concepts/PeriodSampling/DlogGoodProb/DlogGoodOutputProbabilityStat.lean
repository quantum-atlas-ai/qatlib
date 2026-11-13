/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms

/-!
# Good-output probability contract

Defines `DlogGoodOutputProbability`, collecting lower bounds for the total good-pair probability
and for individual outcomes over a generator orbit. A constant success bound follows within the
additional Fourier-modulus window used in the analysis associated with [Shor1997].

## Main statements

* `DlogGoodOutputProbability`: Specifies total and individual good-outcome probability bounds.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.DlogSamplingLaw

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb

open Qatlib
open scoped Classical

/-- Under the prime, generator, and modulus assumptions, requires good-pair probability at least
`(p - 1) / (240 * q)`, each stated good outcome to have probability at least `1 / (20 * q ^
2)`, and total probability at least `1 / 480` when `q ≤ 2 * (p - 1)`. -/
def DlogGoodOutputProbability : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → orderOf g = p - 1 → x = g ^ r →
    (MeasureProb (dlogTwoDimState p q g x)
        (Finset.univ.filter fun t : Fin q × Fin q × ZMod p =>
          dlogGoodPair p q r t.1 t.2.1)
      ≥ (p - 1 : ℝ) / (240 * q)) ∧
    (∀ (c d : Fin q) (k : ℕ), k < p - 1 → dlogGoodPair p q r c d →
        BornProb (dlogTwoDimState p q g x) (c, d, g ^ k) ≥ 1 / (20 * q ^ 2)) ∧
    (q ≤ 2 * (p - 1) →
      MeasureProb (dlogTwoDimState p q g x)
          (Finset.univ.filter fun t : Fin q × Fin q × ZMod p =>
            dlogGoodPair p q r t.1 t.2.1)
        ≥ 1 / 480)

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
