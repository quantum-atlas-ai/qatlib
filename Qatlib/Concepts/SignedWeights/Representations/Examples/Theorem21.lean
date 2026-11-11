/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversary

/-!
# The Kushilevitz Negative-Weight Bound

This module presents the explicit negative-weight adversary lower bound for `kushilevitzInputW`
and `kushilevitzFunW` associated with Theorem 21 of [HoyerLeeSpalek2007]. The result is
expressed directly as a lower bound on `advPmValue`, with the exact real constant `2 + 3 *
Real.sqrt 5 / 5`.

## Main statements

- `theorem21_kushilevitz_bound` proves the exact lower bound for the Kushilevitz instance.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Theorem 21.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Examples

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- The negative-weight adversary value of the Kushilevitz instance is at least `2 + 3 *
Real.sqrt 5 / 5`, as in Theorem 21 of [HoyerLeeSpalek2007]. -/
theorem theorem21_kushilevitz_bound :
    ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPmValue kushilevitzInputW kushilevitzFunW :=
  advPmValue_kushilevitz_ge

end

end Qatlib.Concepts.SignedWeights.Representations.Examples
