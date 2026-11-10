/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem7CorrectedStat

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u v

theorem theorem7Corrected : Theorem7Corrected.{u, v} := by
  intro C Y _ _ _ _ _ U V f ψ hψ r hagree hsuccess
  apply floor_bound_of_quadratic (Fintype.card Y) r
  · exact fixed_query_quadratic_bound U V f ψ hψ r hagree hsuccess
  · intro hr
    subst r
    exact zero_query_card_le_two (f 0) ψ hψ hsuccess

end Qatlib.Concepts.SearchStopping.QueryLowerBound
