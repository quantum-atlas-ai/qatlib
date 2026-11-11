/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Single-target Grover query upper bound

`singleTarget_searchClaim` specializes the known-count construction to one marked element.
`section3QueryBoundSubgoal` packages the result for every finite search space with at least two
elements.

For the mathematical background, see [Grover1997].

## Main statements

* `section3QueryBoundSubgoal`: Establishes the universal single-target query upper-bound
  proposition `Section3QueryBoundSubgoal`.

## References

* [Grover, 1997][Grover1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Concepts.SearchStopping.KnownCount

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- On a finite search space with at least two elements, singleton phase-oracle search achieves
success at least 1/2 within a natural query budget at most π/(4√(1/N)). See [Ambainis2005]. -/
theorem singleTarget_searchClaim (hN : 2 ≤ Fintype.card I) : SingleTargetSearchClaim I := by
  obtain ⟨k, hupper, hbudget⟩ := knownCount_searchClaim (I := I) (m := 1)
    (by norm_num) (by simpa using hN)
  obtain ⟨hε, _, C, ψ, hC, hψ, hk, hsolve⟩ := hupper
  refine ⟨k, ⟨hε, markOracle_unitary, C, ψ, hC, hψ, hk, ?_⟩, ?_⟩
  · intro w
    have hs := hsolve (⟨{w}, by simp⟩ : KnownMarkedSets I 1)
    simpa only [markOracle_eq_setOracle] using hs
  · simpa using hbudget

/-- Establishes the universal single-target query upper-bound proposition
`Section3QueryBoundSubgoal`. -/
theorem section3QueryBoundSubgoal : Section3QueryBoundSubgoal := by
  intro I _ _ hN
  exact singleTarget_searchClaim hN

end Qatlib.Concepts.SearchStopping.KnownCount
