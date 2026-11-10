/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountDefs

namespace Qatlib.Concepts.SearchStopping.KnownCount

def Section3KnownCountSubgoal : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ),
    0 < m → 2 * m ≤ Fintype.card I → KnownCountSearchClaim I m

end Qatlib.Concepts.SearchStopping.KnownCount
