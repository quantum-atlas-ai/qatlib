/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroThm8SampleLedgerSubgoalStat

/-!
# Relative-estimator access ledger

Proves the concrete query and forward/backward access equalities for the layered
relative-estimation trial used with Theorem 8 of [Montanaro2015]. The proof sums the prepared
amplitude-estimation query count over layers and repetitions and retains the separate
access-word counts.

## Main statements

* `montanaroTheorem8SampleLedgerSubgoal` proves the layer-query total and the individual forward
  and backward amplitude-estimation access counts.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Qatlib
open scoped Classical BigOperators

/-- Proves the sample-ledger contract for the relative estimator used with Theorem 8 of
[Montanaro2015]. The layer-query total is `(k + 2) * (2 * layerRepetitions k + 1) *
(layerGrid k - 1)`, while one access word has `layerGrid k` forward and `layerGrid k - 1`
backward accesses. -/
theorem montanaroTheorem8SampleLedgerSubgoal : MontanaroTheorem8SampleLedgerSubgoal := by
  intro I _ _ A j f B N k _hA _hf ω
  have hquery (l : Fin (k+2)) := (prepared_ae_access_ledger (layerGrid k) (layerGrid_pos k)
    (payoffPreparation A (layerPayoff (theorem6ScaledPayoff f B N ω) l.val)) (j,false)).1
  have hsep := prepared_ae_separate_access_counts (I := I×Bool) (layerGrid k) (layerGrid_pos k)
  refine ⟨?_, hsep.1, hsep.2.1⟩
  simp only [hquery, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Qatlib.Concepts.EstimatorLaws.TvStability
