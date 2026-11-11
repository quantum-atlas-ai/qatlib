/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower

/-!
# Detailed-balance stationarity contract

`DetailedBalanceStationaritySubgoal` states the finite Markov-chain implication from
reversibility to stationarity. Its hypotheses include nonnegative reference weights summing to
one and a transition matrix. See [TemmeEtAl2011] for background.

## Main statements

* `DetailedBalanceStationaritySubgoal`: The proposition that every reversible finite transition
  matrix preserves its normalized nonnegative reference distribution.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.GibbsMetropolis.DetailedBalance

/-- The proposition that every reversible finite transition matrix preserves its normalized
nonnegative reference distribution. -/
def DetailedBalanceStationaritySubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ), IsTransitionMatrix P →
    ∀ (π : I → ℝ), (∀ x, 0 ≤ π x) → (∑ x, π x = 1) → IsReversible P π →
      IsStationary P π

end Qatlib.Concepts.GibbsMetropolis.DetailedBalance
