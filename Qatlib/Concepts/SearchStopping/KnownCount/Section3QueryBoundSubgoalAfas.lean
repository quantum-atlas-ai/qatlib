/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Concepts.SearchStopping.KnownCount

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem singleTarget_searchClaim (hN : 2 ≤ Fintype.card I) : SingleTargetSearchClaim I := by
  obtain ⟨k, hupper, hbudget⟩ := knownCount_searchClaim (I := I) (m := 1)
    (by norm_num) (by simpa using hN)
  obtain ⟨hε, _, C, ψ, hC, hψ, hk, hsolve⟩ := hupper
  refine ⟨k, ⟨hε, markOracle_unitary, C, ψ, hC, hψ, hk, ?_⟩, ?_⟩
  · intro w
    have hs := hsolve (⟨{w}, by simp⟩ : KnownMarkedSets I 1)
    simpa only [markOracle_eq_setOracle] using hs
  · simpa using hbudget

theorem section3QueryBoundSubgoal : Section3QueryBoundSubgoal := by
  intro I _ _ hN
  exact singleTarget_searchClaim hN

end Qatlib.Concepts.SearchStopping.KnownCount
