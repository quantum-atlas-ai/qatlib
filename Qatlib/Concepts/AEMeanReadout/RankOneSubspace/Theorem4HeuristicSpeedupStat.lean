/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Corollary1ExpectedSearchStat
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib
open scoped ENNReal BigOperators

def Theorem4HeuristicSpeedup : Prop :=
  ∀ (ℱ : Type) [Fintype ℱ] [DecidableEq ℱ] (P : FinDist ℱ) (n : ℕ)
    (good : ℱ → Fin n → Bool),
    let marked : ℱ → Finset (Fin n) :=
      fun F' => Finset.univ.filter (fun y => (good F' y) = true)
    (hn : 0 < n) →
    (hpos : ∀ F', 0 < (marked F').card) →
    (hsparse : ∀ F', (marked F').card ≤ n / 2) →
      ∀ (ε : ℝ), (hε : 0 < ε) →
        ∃ (Mof Tof : ℱ → ℕ),
          (∀ F', Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule (QFTMatrix n)
                (qftMatrix_unitary hn) ⟨0, hn⟩ (marked F')
                (fun y => decide (y ∈ marked F'))
                (geometricSearchSchedule (Mof F') (Tof F')))
              (fun tr => tr.result = none) ≤ ENNReal.ofReal ε) ∧
          (∑ F' : ℱ, ENNReal.ofReal (P.prob F') *
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix n)
                (qftMatrix_unitary hn) ⟨0, hn⟩ (marked F')
                (fun y => decide (y ∈ marked F'))
                (geometricSearchSchedule (Mof F') (Tof F')))
                (fun tr => (tr.phaseQueries : ℝ≥0∞))) ≤
            ENNReal.ofReal (50 * Real.sqrt 2 *
              Real.sqrt (∑ F' : ℱ, P.prob F' * ((n : ℝ) / (marked F').card))) ∧
          ∀ F', ∀ tr ∈ (searchForSchedule (QFTMatrix n) (qftMatrix_unitary hn)
                ⟨0, hn⟩ (marked F') (fun y => decide (y ∈ marked F'))
                (geometricSearchSchedule (Mof F') (Tof F'))).support,
            ∀ y, tr.result = some y → y ∈ marked F'

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
