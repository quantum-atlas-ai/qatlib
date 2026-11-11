/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Singleton phase-query lower-bound contract

`Section6LowerBoundSubgoal` states the fixed-space lower bound for search with `MarkOracle`. The
budget is the natural floor of sin(π/8) times the square root of the search-space cardinality.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `Section6LowerBoundSubgoal`: The universal proposition asserting fixed-space singleton
  phase-oracle query lower bound ⌊sin(π/8)√N⌋ at success threshold 1/2.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The universal proposition asserting fixed-space singleton phase-oracle query lower bound
⌊sin(π/8)√N⌋ at success threshold 1/2. -/
def Section6LowerBoundSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I],
    FixedSpaceQueryLowerBound (MarkOracle (I := I)) (fun w => {w}) (1 / 2)
      (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card I : ℝ)))

end Qatlib.Concepts.SearchStopping.KnownCount
