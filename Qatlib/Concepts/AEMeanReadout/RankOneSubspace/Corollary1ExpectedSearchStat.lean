/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem3QuadraticSpeedupUnknownAStat
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Expected-search corollary specification

`Corollary1ExpectedSearch` specifies a finite geometric search schedule with a chosen failure
tolerance and an inverse-square-root expected phase-query bound. It also requires every
successful supported output to be marked, in the setting of [BrassardHoyerTapp1998Counting].

## Main statements

* `Corollary1ExpectedSearch`: the finite-schedule failure, expected-cost, and output-correctness
  contract.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib
open scoped ENNReal

/-- Specifies finite geometric search with any positive failure tolerance and expected
phase-query cost at most `50 * sqrt 2 * sqrt (N / S.card)` for a nonempty marked set of size
at most `N / 2`, together with correctness of successful outputs. -/
def Corollary1ExpectedSearch : Prop :=
  ∀ (N : ℕ) (S : Finset (Fin N)),
    (hN : 0 < N) → (hS : 0 < S.card) → (hS2 : S.card ≤ N / 2) →
      ∀ (ε : ℝ), (hε : 0 < ε) →
        ∃ (M T : ℕ),
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN)
              ⟨0, hN⟩ S (fun y => decide (y ∈ S)) (geometricSearchSchedule M T))
              (fun tr => tr.result = none) ≤ ENNReal.ofReal ε ∧
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN)
              ⟨0, hN⟩ S (fun y => decide (y ∈ S)) (geometricSearchSchedule M T))
              (fun tr => (tr.phaseQueries : ℝ≥0∞)) ≤
            ENNReal.ofReal (50 * Real.sqrt 2 * Real.sqrt ((N : ℝ) / (S.card : ℝ))) ∧
          ∀ tr ∈ (searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN)
              ⟨0, hN⟩ S (fun y => decide (y ∈ S)) (geometricSearchSchedule M T)).support,
            ∀ y, tr.result = some y → y ∈ S

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
