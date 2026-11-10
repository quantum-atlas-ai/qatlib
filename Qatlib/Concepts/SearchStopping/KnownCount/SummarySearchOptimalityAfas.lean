/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.SummarySearchOptimalityStat
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LowerBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem summarySearchOptimality : SummarySearchOptimality := by
  intro I _ _ hN
  exact ⟨singleTarget_searchClaim hN, section6LowerBoundSubgoal I⟩

end Qatlib.Concepts.SearchStopping.KnownCount
