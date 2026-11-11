/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.StatisticsDefs

/-!
# Confidence budget accounting

This module collects the statistical confidence bounds with exact record and failure budget
identities. The example `clause33_peak_space` shows that the total number of native selector
cells can differ from the maximum of the pilot size and one main block size. The Monte Carlo
setting is described in [Montanaro2015].

## Main statements

* `clause33_budget_charges`: states the additive budget identities.
* `clause33_endpoint`: collects confidence and resource accounting statements.

## References

* [Montanaro, 2015][Montanaro2015]
-/

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

/-- For the displayed budget with three one-record blocks, the native selector cell count
differs from `confidencePeakSpace`. -/
theorem clause33_peak_space :
    nativeSelectorCells
        { pilotRecords := 1, blockSize := 1, blockCount := 3,
          epsilon := 1 / 10, pilotFailure := 1 / 10, mainFailure := 1 / 10 } ≠
    confidencePeakSpace
        { pilotRecords := 1, blockSize := 1, blockCount := 3,
          epsilon := 1 / 10, pilotFailure := 1 / 10, mainFailure := 1 / 10 } := by
  simp [nativeSelectorCells, confidencePeakSpace]

/-- The total record count is the pilot count plus the main block record count, and the total
failure budget is the sum of the two phase budgets. -/
theorem clause33_budget_charges (b : ConfidenceBudget) :
    b.totalRecords = b.pilotRecords + b.blockSize * b.blockCount ∧
    b.totalFailure = b.pilotFailure + b.mainFailure :=
  ⟨rfl, rfl⟩

/-- Collects the confidence estimates and record identity under their hypotheses, an explicit
inequality between selector cells and peak-space accounting, and the additive record and
failure budget identities. -/
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
