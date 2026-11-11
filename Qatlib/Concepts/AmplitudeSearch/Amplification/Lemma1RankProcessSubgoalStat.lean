/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.RankProcess

/-!
# Rank-process hitting probability specification

This module defines `Lemma1RankProcessSubgoal`, the reciprocal-rank hitting-probability
specification used in the analysis of quantum minimum finding [DurrHoyer1996]. The formula
assigns probability `1 / r` to ranks from `1` through the starting rank and zero outside that
range.

## Main statements

* `Lemma1RankProcessSubgoal`: specifies the hitting probability for every starting rank and
  target rank.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

open Qatlib.Concepts.AmplitudeSearch.Amplification.DistinctRankedTable

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The proposition that `hitProbability t r` equals `1 / r` when `1 ≤ r ≤ t`, and equals zero
otherwise, for all natural ranks `t` and `r`. -/
def Lemma1RankProcessSubgoal : Prop :=
  ∀ t r : ℕ, hitProbability t r =
    if 1 ≤ r ∧ r ≤ t then 1 / (r : ℚ) else 0

end Qatlib.Concepts.AmplitudeSearch.Amplification
