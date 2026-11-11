/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Lemma2

/-!
# Expected time to attain a minimum

This module proves `lemma2` for the sorted-rank BBHT process underlying quantum minimum finding
[DurrHoyer1996]. The proof combines normalization of the initial run masses, minimum attainment
on positive-mass runs, and the source clock-moment estimate.

## Main statements

* `lemma2`: establishes the minimum-attainment specification `Lemma2`.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The sorted-rank BBHT process satisfies `Lemma2`, combining normalized initial run masses,
minimum attainment on positive-mass runs, and the expected clock bound of [Dürr and Høyer,
Lemma 2][DurrHoyer1996]. -/
theorem lemma2 : Lemma2 := by
  intro N hN α inst T
  let ranked := SortedRankedTable.ofTable T
  let law := sourceBBHTLaw ranked.indexOfRank hN
  refine ⟨(law.initialMass_normalized ranked.skip hN).1, ?_, ?_⟩
  · intro x hx
    exact positive_initial_run_is_minimum ranked law hN x hx
  · exact bbht_source_attainment_moment ranked hN

end Qatlib.Concepts.AmplitudeSearch.Amplification
