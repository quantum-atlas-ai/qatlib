/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.SummarySearchOptimalityStat
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LowerBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas

/-!
# Matching square-root search bounds

`summarySearchOptimality` combines the singleton search upper bound with the fixed-space
phase-query lower bound. On every finite space with at least two elements, it gives the explicit
upper budget in `SingleTargetSearchClaim` and lower budget ⌊sin(π/8)√N⌋ at success threshold
1/2.

For the mathematical background, see [Grover1997].

## Main statements

* `summarySearchOptimality`: For finite search spaces with at least two elements, both
  `SingleTargetSearchClaim` and the fixed-space singleton query lower bound ⌊sin(π/8)√N⌋ at
  success threshold 1/2 hold.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- For finite search spaces with at least two elements, both `SingleTargetSearchClaim` and the
fixed-space singleton query lower bound ⌊sin(π/8)√N⌋ at success threshold 1/2 hold. -/
theorem summarySearchOptimality : SummarySearchOptimality := by
  intro I _ _ hN
  exact ⟨singleTarget_searchClaim hN, section6LowerBoundSubgoal I⟩

end Qatlib.Concepts.SearchStopping.KnownCount
