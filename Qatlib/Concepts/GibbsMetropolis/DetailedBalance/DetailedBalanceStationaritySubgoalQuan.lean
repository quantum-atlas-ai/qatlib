/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.DetailedBalance.DetailedBalanceStationaritySubgoalStat

/-!
# Stationarity from detailed balance

`detailedBalanceStationaritySubgoal` proves that a reversible finite transition matrix preserves
its normalized nonnegative reference distribution. This supplies the stationarity step used in
finite Metropolis constructions. See [TemmeEtAl2011] for background.

## Main statements

* `detailedBalanceStationaritySubgoal`: A normalized nonnegative distribution satisfying
  detailed balance for a finite transition matrix is stationary.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.GibbsMetropolis.DetailedBalance

open Qatlib

/-- A normalized nonnegative distribution satisfying detailed balance for a finite transition
matrix is stationary. -/
theorem detailedBalanceStationaritySubgoal : DetailedBalanceStationaritySubgoal :=
  fun I _ _ P hP π hπ hsum hrev =>
    Qatlib.Concepts.WalkSearch.TwoLevelLower.reversible_stationary hP ⟨hπ, hsum⟩ hrev

end Qatlib.Concepts.GibbsMetropolis.DetailedBalance
