/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Theorem2Stat

namespace Qatlib.Concepts.SearchStopping.KnownCount

def Corollary2_2 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (k l : ℂ),
    (distinguishedAfterC N k l) ^ 2 + ((N : ℂ) - 1) * (ordinaryAfterC N k l) ^ 2 =
      k ^ 2 + ((N : ℂ) - 1) * l ^ 2

end Qatlib.Concepts.SearchStopping.KnownCount
