/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Exact search at quarter marked density

Defines `QuarterDensitySearchClaim` as an exact fixed-space query upper bound for marked sets of
known cardinality. The specification uses zero error and one oracle query, providing the
interface for the quarter-density result. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `QuarterDensitySearchClaim`: The exact one-query fixed-space search upper-bound proposition
  for all marked sets of cardinality `m`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.PaidRestart

/-- The exact one-query fixed-space search upper-bound proposition for all marked sets of
cardinality `m`. -/
def QuarterDensitySearchClaim (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) : Prop :=
  FixedSpaceQueryUpperBound
    (fun A : KnownMarkedSets I m => SetOracle A.val) (fun A => A.val) 0 1
end Qatlib.Concepts.SearchStopping.PaidRestart
