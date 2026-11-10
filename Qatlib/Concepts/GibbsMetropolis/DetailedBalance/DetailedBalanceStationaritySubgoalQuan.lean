/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.DetailedBalance.DetailedBalanceStationaritySubgoalStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.GibbsMetropolis.DetailedBalance

open Qatlib

theorem detailedBalanceStationaritySubgoal : DetailedBalanceStationaritySubgoal :=
  fun I _ _ P hP π hπ hsum hrev =>
    Qatlib.Concepts.WalkSearch.TwoLevelLower.reversible_stationary hP ⟨hπ, hsum⟩ hrev

end Qatlib.Concepts.GibbsMetropolis.DetailedBalance
