/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.MeasuredGenerationSubgoalStat
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.CompositeMeasurementNearUniformQuan
import Qatlib.Concepts.HspRecovery.AbelianSampling.WideGenerationSubgoalQuan
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.StabilizerAlg.NearUniformGen

namespace Qatlib.Concepts.HspRecovery.AbelianSampling
open scoped Classical BigOperators
open Qatlib

theorem abelianStabilizerMeasuredGenerationSubgoal :
    AbelianStabilizerMeasuredGenerationSubgoal := by
  intro n hn G _ _ _ H hcard μ cond hmix hacc
  have hnear : ∀ L : Finset ↥H,
      |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)|
        ≤ 1 / ((6 : ℝ) * ↑(n + 4)) :=
    compositeMeasurementNearUniformSubgoal G H μ cond
      (1 / ((6 : ℝ) * ↑(n + 4))) (by positivity) hmix hacc
  exact abelianStabilizerWideGenerationSubgoal n hn G H hcard μ hnear

end Qatlib.Concepts.HspRecovery.AbelianSampling
