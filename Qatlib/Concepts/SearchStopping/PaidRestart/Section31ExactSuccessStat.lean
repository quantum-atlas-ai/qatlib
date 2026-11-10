/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalStat
import Qatlib.Concepts.SearchStopping.PaidRestart.QuarterDensitySearchAuxiliary

namespace Qatlib.Concepts.SearchStopping.PaidRestart

def Section3_1ExactSuccess : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ),
    0 < m → 4 * m = Fintype.card I → QuarterDensitySearchClaim I m

end Qatlib.Concepts.SearchStopping.PaidRestart
