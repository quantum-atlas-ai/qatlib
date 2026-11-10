/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Lemma2
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

theorem lemma2 : Lemma2 := by
  intro N hN α inst T
  let ranked := SortedRankedTable.ofTable T
  let law := sourceBBHTLaw ranked.indexOfRank hN
  refine ⟨(law.initialMass_normalized ranked.skip hN).1, ?_, ?_⟩
  · intro x hx
    exact positive_initial_run_is_minimum ranked law hN x hx
  · exact bbht_source_attainment_moment ranked hN

end Qatlib.Concepts.AmplitudeSearch.Amplification
