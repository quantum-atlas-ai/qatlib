/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile

/-!
# Statement of the restart angle root enclosure

Defines `Section3OptimalAngleSubgoal`, the existence and uniqueness of a root of `Real.tan (z /
2) = z` within the interval `(2.33112, 2.33113)`. The interval isolates the root used for the
restart constants. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Section3OptimalAngleSubgoal`: The proposition that exactly one real `z` satisfies `Real.tan
  (z / 2) = z` together with `2.33112 < z < 2.33113`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that exactly one real `z` satisfies `Real.tan (z / 2) = z` together with
`2.33112 < z < 2.33113`. -/
def Section3OptimalAngleSubgoal : Prop :=
  ∃! z : ℝ, Real.tan (z / 2) = z ∧ 233112 / 100000 < z ∧ z < 233113 / 100000

end Qatlib.Concepts.SearchStopping.RestartLaw
