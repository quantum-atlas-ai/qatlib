/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.SearchStopping.PaidRestart

def QuarterDensitySearchClaim (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) : Prop :=
  FixedSpaceQueryUpperBound
    (fun A : KnownMarkedSets I m => SetOracle A.val) (fun A => A.val) 0 1
end Qatlib.Concepts.SearchStopping.PaidRestart
