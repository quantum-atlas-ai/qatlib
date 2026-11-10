/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstruction
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open scoped ENNReal BigOperators Classical

noncomputable def fairWordListLaw (N : ℕ) : (r : ℕ) → PMF (List (Fin (thresholdWords N)))
  | 0 => PMF.pure []
  | r + 1 => (producerWordLaw N).bind fun w =>
      (fairWordListLaw N r).map fun ws => w :: ws

noncomputable def producerScanLaw (N : ℕ) : (r : ℕ) → PMF (Option (Fin N × ℕ))
  | 0 => PMF.pure none
  | r + 1 => (fairWordListLaw N (r + 1)).map (thresholdScan N)

def outcomeToOption {N r : ℕ} : ThresholdOutcome N r → Option (Fin N × ℕ)
  | .accepted i n => some (i, n.val)
  | .failed => none

def incScan {N : ℕ} : Option (Fin N × ℕ) → Option (Fin N × ℕ)
  | none => none
  | some (i, k) => some (i, k + 1)

def producerDraws {N r : ℕ} (o : ThresholdOutcome N r) : ℕ :=
  match o with
  | .accepted _ n => n.val + 1
  | .failed => r

def producerRemaining {N r : ℕ} (o : ThresholdOutcome N r) : ℕ :=
  r - producerDraws o

noncomputable def producerCostedLaw (N r : ℕ) : CostedLaw (ThresholdOutcome N r) :=
  (thresholdRunLaw N r).map fun o => (o, thresholdWidth N * producerDraws o)

def chargedSpend {N : ℕ} (budget : ℕ) (x : Fin N × ℕ) : ℕ := budget - x.2

noncomputable def chargedSpendLaw {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) (budget : ℕ) (current : Fin N) :
    PMF ((Fin N × ℕ) × ℕ) :=
  (minimumBudgetPMFWithInit T (initCharge N) hN budget current).map fun x =>
    (x, chargedSpend budget x)

def sourceWindowDepth (M : ℕ) (i : Fin M) : ℕ := i.val + 1

noncomputable def sourceWindowLaw (M : ℕ) (hM : 0 < M) : PMF (Fin M) := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact PMF.uniformOfFintype' _

noncomputable def qSearchSourceRound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) : PMF (Option I × ℕ × ℕ) :=
  PMF.bind (preparedAATrial A hA j₀ S ⟨0, Nat.zero_lt_one⟩) fun st =>
    if st.1.1 ∈ S then
      PMF.pure (some st.1.1, 1, 1)
    else
      PMF.bind (sourceWindowLaw M hM) fun i =>
        PMF.bind (preparedAATrial A hA j₀ S
          (⟨sourceWindowDepth M i, Nat.lt_succ_of_le (Nat.succ_le_of_lt i.isLt)⟩ : Fin (M + 1))) fun st2 =>
          PMF.pure (if st2.1.1 ∈ S then some st2.1.1 else none,
            2 + 2 * sourceWindowDepth M i, 2 + sourceWindowDepth M i)

noncomputable def qSearchSourceLoop {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (M : ℕ) (hM : 0 < M) : ℕ → ℕ → PMF (Option I × ℕ × ℕ)
  | 0, _ => PMF.pure (none, 0, 0)
  | T + 1, off =>
      (qSearchSourceRound A hA j₀ S M hM).bind fun out =>
        match out.1 with
        | some _ => PMF.pure out
        | none =>
            (qSearchSourceLoop A hA j₀ S M hM T (off + 1)).map fun r =>
              (r.1, r.2.1 + out.2.1, r.2.2 + out.2.2)

noncomputable def aaDepthMass {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ) : ℝ :=
  MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Ket j₀)) S

noncomputable def sourceWindowAvgSuccess {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (M : ℕ) : ℝ :=
  (∑ i : Fin M, aaDepthMass A j₀ S (sourceWindowDepth M i)) / (M : ℝ)

noncomputable def shiftedWindowAvgSuccess {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (M : ℕ) : ℝ :=
  (∑ i : Fin M, aaDepthMass A j₀ S i.val) / (M : ℝ)

end Qatlib.Concepts.AmplitudeSearch.Amplification
