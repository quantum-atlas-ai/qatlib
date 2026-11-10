/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat

namespace Qatlib.Concepts.SearchStopping.KnownCount

def Corollary2_1Corrected : Prop :=
  ∀ (N : ℕ), 8 ≤ N → ∀ (k l : ℝ), k < 0 → 0 < l →
    |k / l| < Real.sqrt N →
      0 < distinguishedAfter N k l ∧ 0 < ordinaryAfter N k l

end Qatlib.Concepts.SearchStopping.KnownCount
