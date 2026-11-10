/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat

namespace Qatlib.Concepts.SearchStopping.KnownCount

def Theorem3Corrected : Prop :=
  ∀ (N : ℕ), 8 ≤ N → ∀ (k l : ℝ),
    0 < k → k < 1 / Real.sqrt 2 → 0 < l → twoAmplitudeMass N k l = 1 →
      1 / (2 * Real.sqrt (N : ℝ)) < distinguishedAfter N (-k) l - k ∧
      0 < ordinaryAfter N (-k) l

end Qatlib.Concepts.SearchStopping.KnownCount
