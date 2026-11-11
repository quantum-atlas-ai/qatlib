/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalStat
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LowerBoundSubgoalStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Search optimality contract

`SummarySearchOptimality` records both explicit square-root query bounds for singleton
phase-oracle search on finite spaces of size at least two. Its upper-bound component is
`SingleTargetSearchClaim`, and its lower budget is ⌊sin(π/8)√N⌋ at success threshold 1/2.

For the mathematical background, see [Grover1997].

## Main statements

* `SummarySearchOptimality`: The conjunction of the single-target search upper-bound claim and
  fixed-space phase-query lower bound ⌊sin(π/8)√N⌋ for every finite space of size at least two.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The conjunction of the single-target search upper-bound claim and fixed-space phase-query
lower bound ⌊sin(π/8)√N⌋ for every finite space of size at least two. -/
def SummarySearchOptimality : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I], 2 ≤ Fintype.card I →
    SingleTargetSearchClaim I ∧
      FixedSpaceQueryLowerBound (MarkOracle (I := I)) (fun w => {w}) (1 / 2)
        (Nat.floor (Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card I : ℝ)))

end Qatlib.Concepts.SearchStopping.KnownCount
