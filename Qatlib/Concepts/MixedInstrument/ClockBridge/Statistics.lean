/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.StatisticsDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem clause33_peak_space :
    nativeSelectorCells
        { pilotRecords := 1, blockSize := 1, blockCount := 3,
          epsilon := 1 / 10, pilotFailure := 1 / 10, mainFailure := 1 / 10 } ≠
    confidencePeakSpace
        { pilotRecords := 1, blockSize := 1, blockCount := 3,
          epsilon := 1 / 10, pilotFailure := 1 / 10, mainFailure := 1 / 10 } := by
  simp [nativeSelectorCells, confidencePeakSpace]

theorem clause33_budget_charges (b : ConfidenceBudget) :
    b.totalRecords = b.pilotRecords + b.blockSize * b.blockCount ∧
    b.totalFailure = b.pilotFailure + b.mainFailure :=
  ⟨rfl, rfl⟩

theorem clause33_endpoint :
    (∀ {X : Type} [Fintype X] (q : FinDist X) (f : X → ℝ) (b : ConfidenceBudget)
      (tol : ℝ) (htol : 0 < tol)
      (hpos : 0 < b.pilotRecords ∧ 0 < b.blockSize ∧ 0 < b.blockCount)
      (hvar : 4 * q.variance f ≤ (b.blockSize : ℝ) * b.epsilon ^ 2)
      (hpilot : pilotFailureMass q f (n := b.pilotRecords) tol ≤ b.pilotFailure)
      (hmain : mainFailureMass q f (M := b.blockCount) (L := b.blockSize) b.epsilon
        ≤ b.mainFailure),
      (∀ {n : ℕ}, 0 < n →
        (∑ ω : Fin n → X, q.probOf ω * pilotVariance q f ω = q.variance f)) ∧
      (∀ {n : ℕ}, 0 < n → pilotFailureMass q f (n := n) tol ≤
        pilotFourthMoment q f / ((n : ℝ) * tol ^ 2)) ∧
      (∀ {M L : ℕ}, 0 < L → 0 < M → 0 < b.epsilon →
        4 * q.variance f ≤ (L : ℝ) * b.epsilon ^ 2 →
        mainFailureMass q f (M := M) (L := L) b.epsilon ≤ 3 ^ (M / 2) / 2 ^ M) ∧
      mergedFailureMass q f (n := b.pilotRecords) (M := b.blockCount) (L := b.blockSize)
        tol b.epsilon ≤ b.totalFailure ∧
      b.totalRecords = b.pilotRecords + b.blockSize * b.blockCount) ∧
    (nativeSelectorCells
        { pilotRecords := 1, blockSize := 1, blockCount := 3,
          epsilon := 1 / 10, pilotFailure := 1 / 10, mainFailure := 1 / 10 } ≠
    confidencePeakSpace
        { pilotRecords := 1, blockSize := 1, blockCount := 3,
          epsilon := 1 / 10, pilotFailure := 1 / 10, mainFailure := 1 / 10 }) ∧
    (∀ (b : ConfidenceBudget),
      b.totalRecords = b.pilotRecords + b.blockSize * b.blockCount ∧
      b.totalFailure = b.pilotFailure + b.mainFailure) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X inst q f b tol htol hpos hvar hpilot hmain
    exact Qatlib.Concepts.MixedInstrument.ClockBridge.clause33_complete q f b tol htol hpos hvar
      hpilot hmain
  · exact clause33_peak_space
  · intro b
    exact clause33_budget_charges b

end Qatlib.Concepts.MixedInstrument.ClockBridge
