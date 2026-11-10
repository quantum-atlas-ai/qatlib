/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.GibbsMetropolis.DetailedBalance

def DetailedBalanceStationaritySubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : I → I → ℝ), IsTransitionMatrix P →
    ∀ (π : I → ℝ), (∀ x, 0 ≤ π x) → (∑ x, π x = 1) → IsReversible P π →
      IsStationary P π

end Qatlib.Concepts.GibbsMetropolis.DetailedBalance
