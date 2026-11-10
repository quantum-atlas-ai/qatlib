/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22Stat

namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem corollary2_2_complex : Corollary2_2 := by
  intro N hN k l
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold distinguishedAfterC ordinaryAfterC
  field_simp
  ring

end Qatlib.Concepts.SearchStopping.KnownCount
