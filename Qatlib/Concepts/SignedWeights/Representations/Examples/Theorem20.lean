/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryFourBitWitness

/-!
# A Four-Bit Negative-Weight Bound

This module records the numerical negative-weight adversary lower bound for `ambainisSorted4`,
the four-bit example associated with Theorem 20 of [HoyerLeeSpalek2007]. The theorem obtains the
printed decimal bound from the exact rational witness estimate and states it using the extended
nonnegative value `advPmValue`.

## Main statements

* `theorem20_four_bit_bound` proves that `advPmValue` for `ambainisSorted4` is at least
  `2.5135`.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Theorem 20.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Examples

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- The negative-weight adversary value of `ambainisSorted4` is at least `2.5135`, the four-bit
bound stated in Theorem 20 of [HoyerLeeSpalek2007]. -/
theorem theorem20_four_bit_bound :
    ENNReal.ofReal (2.5135 : ℝ) ≤
      advPmValue (fun w : FourBitWord => w) ambainisSorted4 := by
  have hdec : (2.5135 : ℝ) = 25135 / 10000 := by norm_num
  rw [hdec]
  exact ambainis_four_bit_printed_bound

end

end Qatlib.Concepts.SignedWeights.Representations.Examples
