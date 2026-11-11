/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountDefs

/-!
# Known-count search upper-bound contract

`Section3KnownCountSubgoal` asserts `KnownCountSearchClaim` for every positive marked count at
most half the finite search-space size. The claim uses the phase-oracle model and success
threshold 1/2.

For the mathematical background, see [Grover1997].

## Main statements

* `Section3KnownCountSubgoal`: The universal known-count search claim for positive m satisfying
  2m ≤ the search-space cardinality.

## References

* [Grover, 1997][Grover1997]
-/

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The universal known-count search claim for positive m satisfying 2m ≤ the search-space
cardinality. -/
def Section3KnownCountSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ),
    0 < m → 2 * m ≤ Fintype.card I → KnownCountSearchClaim I m

end Qatlib.Concepts.SearchStopping.KnownCount
