/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.DlogSamplingLaw.DlogPrograms

/-!
# Good marginal probability contract

Defines `DlogGoodCMarginal`, lower bounds on the measurement probability of any small-residue
first coordinate. The contract assumes a generator of the nonzero residues and supplies an
additional bound when `q ≤ 2 * (p - 1)`, in the setting of [Shor1997].

## Main statements

* `DlogGoodCMarginal`: Specifies the first-coordinate marginal lower bounds.

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

/-- The generator-based marginal contract requires mass at least `(p - 1) / (20 * q ^ 2)` for
each small-residue first coordinate, and at least `1 / (40 * q)` when `q ≤ 2 * (p - 1)`. -/
def DlogGoodCMarginal : Prop :=
  ∀ (p q r : ℕ) [NeZero p] (g x : ZMod p), Nat.Prime p → 3 ≤ p → x ≠ 0 →
    (p : ℕ) < q → orderOf g = p - 1 → x = g ^ r →
    ∀ c : Fin q, dlogSmallResidue p q c →
      (MeasureProb (dlogTwoDimState p q g x)
          (Finset.univ.filter fun t : Fin q × Fin q × ZMod p => t.1 = c)
        ≥ (p - 1 : ℝ) / (20 * q ^ 2)) ∧
      (q ≤ 2 * (p - 1) →
        MeasureProb (dlogTwoDimState p q g x)
            (Finset.univ.filter fun t : Fin q × Fin q × ZMod p => t.1 = c)
          ≥ 1 / (40 * q))

end Qatlib.Concepts.PeriodSampling.DlogGoodProb
