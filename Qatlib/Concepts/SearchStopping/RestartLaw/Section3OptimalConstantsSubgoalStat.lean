/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile

/-!
# Statement of certified Grover restart constants

Defines `Section3OptimalConstantsSubgoal`, conditional rational bounds for the success,
iteration, and expected-cost coefficients at the isolated restart root. It also compares the
expected-cost coefficient with the benchmark `Real.pi / 4`. For the quantum-search analysis, see
[BoyerEtAl1998].

## Main statements

* `Section3OptimalConstantsSubgoal`: The proposition giving rational enclosures for `Real.sin (z
  / 2) ^ 2`, `z / 4`, and `z / (4 * Real.sin (z / 2) ^ 2)` when `Real.tan (z / 2) = z` and
  `2.33112 < z < 2.33113`, including bounds between 0.87 and 0.88 times `Real.pi / 4` for the
  last quantity.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition giving rational enclosures for `Real.sin (z / 2) ^ 2`, `z / 4`, and `z / (4
* Real.sin (z / 2) ^ 2)` when `Real.tan (z / 2) = z` and `2.33112 < z < 2.33113`, including
bounds between 0.87 and 0.88 times `Real.pi / 4` for the last quantity. -/
def Section3OptimalConstantsSubgoal : Prop :=
  ∀ z : ℝ, Real.tan (z / 2) = z → 233112 / 100000 < z → z < 233113 / 100000 →
    8445 / 10000 < Real.sin (z / 2) ^ 2 ∧ Real.sin (z / 2) ^ 2 < 8446 / 10000 ∧
    58278 / 100000 < z / 4 ∧ z / 4 < 58279 / 100000 ∧
    69002 / 100000 < z / (4 * Real.sin (z / 2) ^ 2) ∧
      z / (4 * Real.sin (z / 2) ^ 2) < 69003 / 100000 ∧
    87 / 100 * (Real.pi / 4) < z / (4 * Real.sin (z / 2) ^ 2) ∧
      z / (4 * Real.sin (z / 2) ^ 2) < 22 / 25 * (Real.pi / 4)

end Qatlib.Concepts.SearchStopping.RestartLaw
