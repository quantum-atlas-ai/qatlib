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
set_option warningAsError false
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

def RetryCostLedger (good bad n : ℕ) : ℕ := n * bad + good

def SingleLongerRunBudget (good bad n : ℕ) : ℕ := RetryCostLedger good bad n

def CutoffContract (E : ℝ≥0∞) (b : ℕ) : Prop :=
  E / (b + 1 : ℝ≥0∞) ≤ 1 / 2

noncomputable def sourcePrintedDeadline (N : ℕ) : ℝ :=
  (45 / 2 : ℝ) * Real.sqrt N + (7 / 5 : ℝ) * (binaryLog N) ^ 2

noncomputable def sourceIntegerDeadline (N : ℕ) : ℕ :=
  Nat.ceil (sourcePrintedDeadline N)

noncomputable def singleRunFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (_hN : 0 < N) : ℝ :=
  1 - chargedInitialSuccess T (chargedBudget N)

noncomputable def independentRunsPMF {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) : PMF (Fin N × ℕ) :=
  match c with
  | 0 => PMF.pure (⟨0, hN⟩, 0)
  | 1 => chargedInitialPMF T hN (chargedBudget N)
  | c' + 2 => amplifiedStep T hN (independentRunsPMF T hN (c' + 1))

noncomputable def sourceProgramLaw {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) : RankedCallLaw N (SearchTrace N) :=
  sourceBBHTLaw ((SortedRankedTable.ofTable T).indexOfRank) hN

noncomputable def sourceProgramSkip {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) : RankSkip N := (SortedRankedTable.ofTable T).skip

noncomputable def sourceCutoffMassFn {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (deadline : ℝ) : Fin N × List (SearchTrace N) → ℝ :=
  fun x => if (sourceProgramLaw T hN).runClock x.2 ≤ deadline then
    (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x else 0

noncomputable def sourceCutoffSuccessFn {N : ℕ} {α : Type} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (deadline : ℝ) : Fin N × List (SearchTrace N) → ℝ :=
  fun x => if (sourceProgramLaw T hN).runClock x.2 ≤ deadline ∧
      0 < (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x then
    (sourceProgramLaw T hN).initialMass (sourceProgramSkip T) x else 0

noncomputable def independentRunsFailure {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (c : ℕ) : ℝ :=
  (singleRunFailure T hN) ^ c

end Qatlib.Concepts.AmplitudeSearch.Amplification
