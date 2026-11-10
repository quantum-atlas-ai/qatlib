/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroTheorem8FactorSubgoalStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroThm6RelativeTrialSubgoalMont
import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeSignedMeanConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.NativeNumerics.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib
open scoped Classical BigOperators

theorem montanaroTheorem8FactorSubgoal : MontanaroTheorem8FactorSubgoal := by
  intro I _ _ A j f B ε N k r hA hf hB hε hε1 hN hk hwindow μ hμ hv
  have htrial := montanaroTheorem6RelativeTrialSubgoal I A j f B ε N k
    hA hf hB hε hε1 hN hk hwindow hμ hv
  rw [theorem6_event_one_mass (theorem6TrialLaw A j f B N k hA hf)
    (fun ω => ε*μ < |theorem6Output f B N k ω-μ|)] at htrial
  rw [theorem6_event_one_mass (theorem6FactorLaw A j f B N k r hA hf)
    (fun ω => ε*μ < |theorem6FactorMedian f B N k r ω-μ|)]
  have hmedian := native_sorted_median_failure (theorem6TrialLaw A j f B N k hA hf)
    (theorem6Output f B N k) r μ (ε*μ) (mul_nonneg hε.le hμ.le)
    (htrial.trans (by norm_num : (1/4 : ℝ) ≤ 11/24))
  exact hmedian

end Qatlib.Concepts.EstimatorLaws.TvStability
