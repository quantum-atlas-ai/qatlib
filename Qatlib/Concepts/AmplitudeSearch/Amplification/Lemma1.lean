/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Lemma1
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

universe u

theorem lemma1 : Lemma1.{u} := by
  intro N hN α _ T
  let ranked := SortedRankedTable.ofTable T
  let law := sourceBBHTLaw ranked.indexOfRank hN
  refine ⟨(law.initialMass_normalized ranked.skip hN).1,
    fun y => law.runMass_normalized ranked.skip _
      (lt_of_le_of_lt (ranked.skip.le_rank _) (ranked.indexOfRank.symm y).isLt), ?_, ?_, ?_⟩
  · intro hd
    have hd' : Function.Injective ranked.value := hd
    constructor
    · intro t r htN
      exact ⟨distinct_prefix_is_original_marking ranked hd' t htN,
        bbht_visit_hasSum ranked hN hd' t r htN⟩
    · exact bbht_initial_visit_hasSum ranked hN hd'
  · intro y r
    constructor
    · have h := rankMarked_eq_strict_values ranked (ranked.indexOfRank.symm y)
      simpa only [Equiv.apply_symm_apply] using! h
    · exact bbht_threshold_visit_tied_bound ranked hN y r
  · exact bbht_initial_visit_tied_bound ranked hN

end Qatlib.Concepts.AmplitudeSearch.Amplification
