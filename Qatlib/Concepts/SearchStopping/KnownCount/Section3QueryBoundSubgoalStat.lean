/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Single-target search upper-bound contract

`SingleTargetSearchClaim` specifies a common fixed-space singleton search algorithm with success
at least 1/2 and budget at most π/(4√(1/N)). `Section3QueryBoundSubgoal` asserts this claim for
finite spaces with at least two elements.

For the mathematical background, see [Grover1997].

## Main statements

* `Section3QueryBoundSubgoal`: The universal singleton search upper-bound claim for finite
  spaces of cardinality at least two.

## References

* [Grover, 1997][Grover1997]
-/

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that singleton phase-oracle search has a fixed-space success bound 1/2
within a natural query budget k ≤ π/(4√(1/N)). -/
def SingleTargetSearchClaim (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∃ k : ℕ, FixedSpaceQueryUpperBound (MarkOracle (I := I)) (fun w => {w}) (1 / 2) k ∧
    (k : ℝ) ≤ Real.pi / (4 * Real.sqrt (1 / (Fintype.card I : ℝ)))

/-- The universal singleton search upper-bound claim for finite spaces of cardinality at least
two. -/
def Section3QueryBoundSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I],
    2 ≤ Fintype.card I → SingleTargetSearchClaim I

end Qatlib.Concepts.SearchStopping.KnownCount
