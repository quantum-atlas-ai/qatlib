/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.MeasuredGenerationSubgoalStat
import Qatlib.Concepts.StabilizerAlg.NearUniformGen.CompositeMeasurementNearUniformQuan
import Qatlib.Concepts.HspRecovery.AbelianSampling.WideGenerationSubgoalQuan

/-!
# Generation from measured stabilizer samples

`abelianStabilizerMeasuredGenerationSubgoal` converts a uniform mixture of accurate conditional
measurements into samples that generate the target subgroup with high probability. It combines a
near uniformity estimate with the generation bound for `n + 4` independent samples and per label
error `1 / (6 * (n + 4))`. [Kitaev1995]

## Main statements

* `abelianStabilizerMeasuredGenerationSubgoal`: bounds subgroup generation failure by `1 / 3`.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.StabilizerAlg.NearUniformGen

namespace Qatlib.Concepts.HspRecovery.AbelianSampling
open scoped Classical BigOperators
open Qatlib

/-- If a subgroup has size at most `2 ^ n` with `n > 0`, a uniform mixture of conditional
distributions that each return their label with probability at least `1 - 1 / (6 * (n + 4))`
generates the subgroup from `n + 4` independent samples except with probability at most `1 /
3` [Kitaev1995]. -/
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
