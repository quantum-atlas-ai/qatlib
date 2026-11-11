/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Lemma1

/-!
# The minimum-finding rank-visit lemma

`lemma1` establishes the shared rank-visit specification for the source BBHT ranked-call law.
Its proof combines run normalization, inverse-rank visit formulas for distinct values, and visit
bounds when values are tied.

This formalizes the rank-process reasoning of [DurrHoyer1996], including the distinction between
exact formulas for distinct values and bounds for ties.

## Main statements

* `lemma1`: establishes the shared `Lemma1` specification using ranked BBHT runs.

## References

* [Durr and Hoyer, 1996, Lemma 1][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

universe u

/-- The source BBHT ranked-call laws satisfy `Lemma1`, including inverse-rank visit formulas for
distinct values and the stated visit bounds for ties [Durr and Hoyer, Lemma
1][DurrHoyer1996]. -/
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
