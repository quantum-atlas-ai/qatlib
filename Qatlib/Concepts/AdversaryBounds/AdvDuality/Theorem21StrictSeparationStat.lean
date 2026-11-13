/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21Defs

/-!
# Statement of the Kushilevitz adversary separation

`Theorem21StrictSeparation` states two bounds for the total six-bit function
`kushilevitzMonotone` with unit coordinate costs: its nonnegative adversary value is at most
three, and its general adversary value is at least `2 + 3 * sqrt 5 / 5`.

The proposition records the comparison of adversary values associated with Theorem 21 of
[HoyerLeeSpalek2007].

## Main statements

* `Theorem21StrictSeparation`: states the nonnegative upper bound and general adversary lower
  bound.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Finset

/-- The conjunction asserting that the unit-cost nonnegative adversary value of
`kushilevitzMonotone` is at most three and its general adversary value is at least `2 + 3 *
sqrt 5 / 5`. See [Hoyer, Lee, and Spalek, Theorem 21][HoyerLeeSpalek2007]. -/
def Theorem21StrictSeparation : Prop :=
  advNonneg (fun w => w) kushilevitzMonotone (fun _ => 1) ≤ ENNReal.ofReal 3 ∧
    ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPlus (fun w => w) kushilevitzMonotone (fun _ => 1)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
