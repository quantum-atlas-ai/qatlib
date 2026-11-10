/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.RankProcess

open Qatlib.Concepts.AmplitudeSearch.Amplification.DistinctRankedTable

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

def Lemma1RankProcessSubgoal : Prop :=
  ∀ t r : ℕ, hitProbability t r =
    if 1 ≤ r ∧ r ≤ t then 1 / (r : ℚ) else 0

end Qatlib.Concepts.AmplitudeSearch.Amplification
