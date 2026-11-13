/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
import Qatlib.Concepts.FairRandomBits.GeometricRetry
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall
import Qatlib.Concepts.AmplitudeSearch.Amplification.SortedTable
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds
import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockedPrefix
import Qatlib.Concepts.AmplitudeSearch.Amplification.Basic
import Qatlib.Concepts.AmplitudeSearch.Amplification.FinalRemarksAmplificationAqua
import Qatlib.Concepts.AmplitudeSearch.Amplification.ChargedBudgetSuccess
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability
import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma2
import Qatlib.Concepts.AmplitudeSearch.Amplification.TableRun

/-!
# Definitions for refined minimum-search runtime bounds

This module defines the cost ledgers, deadlines, and probability laws used to refine the runtime
analysis of quantum minimum finding [DurrHoyer1996]. The source cutoff functions restrict ranked
run masses to the printed deadline, and `independentRunsPMF` models repeated charged runs.

The real-valued failure expressions and their probability-law counterparts support comparisons
between independent repetition and a single extended budget.

## Main statements

* `RetryCostLedger`: records failed-attempt charges followed by a successful charge.
* `sourcePrintedDeadline`: defines the real-valued source deadline.
* `sourceCutoffMassFn`: retains only ranked runs within the chosen deadline.
* `independentRunsFailure`: defines the power of the single-run failure value.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Matrix
open scoped BigOperators Classical ENNReal Classical
open Qatlib RandomizedExecution

/-- The total charge `n * bad + good` for `n` failed attempts followed by a successful attempt. -/
def RetryCostLedger (good bad n : ℕ) : ℕ := n * bad + good

/-- The single-run budget defined by the retry cost ledger `n * bad + good`. -/
def SingleLongerRunBudget (good bad n : ℕ) : ℕ := RetryCostLedger good bad n

/-- The cutoff condition that `E / (b + 1)` is at most one half in the extended nonnegative
reals. -/
def CutoffContract (E : ℝ≥0∞) (b : ℕ) : Prop :=
  E / (b + 1 : ℝ≥0∞) ≤ 1 / 2

/-- The real source deadline `(45 / 2) * √N + (7 / 5) * (binaryLog N) ^ 2` for quantum minimum
finding [DurrHoyer1996]. -/
noncomputable def sourcePrintedDeadline (N : ℕ) : ℝ :=
  (45 / 2 : ℝ) * Real.sqrt N + (7 / 5 : ℝ) * (binaryLog N) ^ 2

/-- The natural ceiling of the printed real source deadline. -/
noncomputable def sourceIntegerDeadline (N : ℕ) : ℕ :=
  Nat.ceil (sourcePrintedDeadline N)

/-- One minus the charged minimum-search success value at `chargedBudget N`. -/
noncomputable def singleRunFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (_hN : 0 < N) : ℝ :=
  1 - chargedInitialSuccess T (chargedBudget N)

/-- The recursive law of repeated charged minimum-search runs, using `amplifiedStep` after the
first run. At zero runs it returns index zero with remaining-budget component zero. -/
noncomputable def independentRunsPMF {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) : PMF (Fin N × ℕ) :=
  match c with
  | 0 => PMF.pure (⟨0, hN⟩, 0)
  | 1 => chargedInitialPMF T hN (chargedBudget N)
  | c' + 2 => amplifiedStep T hN (independentRunsPMF T hN (c' + 1))

/-- The ranked BBHT call law associated with the sorted ranking of the table. -/
noncomputable def sourceProgramLaw {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) : RankedCallLaw N (SearchTrace N) :=
  sourceBBHTLaw ((SortedRankedTable.ofTable T).indexOfRank) hN

/-- The rank-skipping map associated with the sorted ranking of the table. -/
noncomputable def sourceProgramSkip {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) : RankSkip N := (SortedRankedTable.ofTable T).skip

/-- The initial ranked run mass restricted to runs whose clock is at most the chosen deadline. -/
noncomputable def sourceCutoffMassFn {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (deadline : ℝ) : Fin N × List (SearchTrace N) → ℝ :=
  fun x => if (sourceProgramLaw T hN).runClock x.2 ≤ deadline then
    (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x else 0

/-- The initial ranked run mass restricted to positive-mass runs whose clock is at most the
chosen deadline. -/
noncomputable def sourceCutoffSuccessFn {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (deadline : ℝ) : Fin N × List (SearchTrace N) → ℝ :=
  fun x => if (sourceProgramLaw T hN).runClock x.2 ≤ deadline ∧
      0 < (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x then
    (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x else 0

/-- The `c`th power of the single charged-run failure value. -/
noncomputable def independentRunsFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) : ℝ :=
  (singleRunFailure T hN) ^ c

end Qatlib.Concepts.AmplitudeSearch.Amplification
