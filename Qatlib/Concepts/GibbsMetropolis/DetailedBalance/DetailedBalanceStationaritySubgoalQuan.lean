/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsMetropolis.DetailedBalance.DetailedBalanceStationaritySubgoalStat

@[expose] public section

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

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.GibbsMetropolis.DetailedBalance

open Qatlib

/-- A normalized nonnegative distribution satisfying detailed balance for a finite transition
matrix is stationary. -/
theorem detailedBalanceStationaritySubgoal : DetailedBalanceStationaritySubgoal :=
  fun _I _ _ _P hP _π hπ hsum hrev =>
    Qatlib.Concepts.WalkSearch.TwoLevelLower.reversible_stationary hP ⟨hπ, hsum⟩ hrev

end Qatlib.Concepts.GibbsMetropolis.DetailedBalance
