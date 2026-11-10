/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.LayeredMean.LayeredQuantumMean
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.EstimatorLaws.TvStability.Theorem8RelativeContracts
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

def MontanaroTheorem8SampleLedgerSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (B : ℝ) (N k : ℕ),
    ∀ (_hA : A ∈ Matrix.unitaryGroup I ℂ) (_hf : ∀ i, 0 ≤ f i),
    ∀ (_ω : Fin N → I),
    (∑ l : Fin (k + 2), ∑ _ : Fin (2 * layerRepetitions k + 1),
        QueryCount (countedAECircuit (layerGrid k)
          (payoffPreparation A
            (layerPayoff (theorem6ScaledPayoff f B N _ω) l.val))
          (j, false)))
      = (k + 2) * (2 * layerRepetitions k + 1) * (layerGrid k - 1)
    ∧ aeForwardAccesses (aeAccessWord (I := I × Bool) (layerGrid k)) = layerGrid k
    ∧ aeBackwardAccesses (aeAccessWord (I := I × Bool) (layerGrid k))
        = layerGrid k - 1

end Qatlib.Concepts.EstimatorLaws.TvStability
