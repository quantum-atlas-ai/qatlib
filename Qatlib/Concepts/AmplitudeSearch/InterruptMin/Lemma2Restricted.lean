/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Lemma2Restricted
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.QueryLowerBound

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

universe u

theorem lemma2Restricted : Lemma2Restricted.{u} := by
  intro I _ _ hN A θ hθ h2 m hm
  have h := search_randomized_angle hN A θ hθ h2 m hm
  exact ⟨h.1, h.2.2⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
