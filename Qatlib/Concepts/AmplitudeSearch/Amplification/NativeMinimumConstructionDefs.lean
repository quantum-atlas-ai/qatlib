/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.AmplitudeSearch.Amplification.Results
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
open scoped ENNReal BigOperators Classical

noncomputable def fairBitLaw : PMF Bool := PMF.uniformOfFintype' Bool

noncomputable def fairWordLaw (k : ℕ) : PMF (Fin (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨by positivity⟩
  exact PMF.uniformOfFintype' _

noncomputable def thresholdWidth (N : ℕ) : ℕ := initCharge N

noncomputable def thresholdWords (N : ℕ) : ℕ := 2 ^ thresholdWidth N

noncomputable def producerWordLaw (N : ℕ) : PMF (Fin (thresholdWords N)) := by
  letI : Nonempty (Fin (thresholdWords N)) :=
    ⟨⟨0, by unfold thresholdWords; positivity⟩⟩
  exact PMF.uniformOfFintype' _

noncomputable def thresholdRejectProb (N : ℕ) : ℝ :=
  ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ)

noncomputable def thresholdAcceptProb (N : ℕ) : ℝ :=
  (N : ℝ) / (thresholdWords N : ℝ)

def acceptThreshold (N : ℕ) (w : Fin (thresholdWords N)) : Option (Fin N) :=
  if h : w.val < N then some ⟨w.val, h⟩ else none

def thresholdScan : (N : ℕ) → List (Fin (thresholdWords N)) → Option (Fin N × ℕ)
  | _, [] => none
  | N, w :: ws => match acceptThreshold N w with
      | some i => some (i, 0)
      | none => (thresholdScan N ws).map (fun p => (p.1, p.2 + 1))

inductive ThresholdOutcome (N r : ℕ) where

  | accepted (index : Fin N) (rejections : Fin r)

  | failed
  deriving DecidableEq, Repr, Fintype

def ThresholdOutcome.rejections {N r : ℕ} (o : ThresholdOutcome N r) : ℕ :=
  match o with
  | .accepted _ n => n.val
  | .failed => 0

def ThresholdOutcome.index {N r : ℕ} (o : ThresholdOutcome N r) : Option (Fin N) :=
  match o with
  | .accepted i _ => some i
  | .failed => none

noncomputable def thresholdRoundLaw (N : ℕ) : PMF (Option (Fin N)) :=
  (producerWordLaw N).map (acceptThreshold N)

def bumpOutcome {N r : ℕ} : ThresholdOutcome N r → ThresholdOutcome N (r + 1)
  | .accepted i n => .accepted i ⟨n.val + 1, by omega⟩
  | .failed => .failed

noncomputable def thresholdRunLaw (N : ℕ) : (r : ℕ) → PMF (ThresholdOutcome N r)
  | 0 => PMF.pure .failed
  | r + 1 => (thresholdRoundLaw N).bind fun o => match o with
      | some i => PMF.pure (.accepted i ⟨0, by omega⟩)
      | none => (thresholdRunLaw N r).map (bumpOutcome)

noncomputable def thresholdCostedLaw (N : ℕ) (r : ℕ) : CostedLaw (ThresholdOutcome N r) :=
  (thresholdRunLaw N r).map (fun o => (o, thresholdWidth N * (r + 1)))

structure ThresholdLedger (N r : ℕ) where

  bitsPerDraw : ℕ

  draws : ℕ

  rejections : ℕ

  workspaceBits : ℕ

  bitsPerDraw_eq : bitsPerDraw = thresholdWidth N

  rejections_le : rejections ≤ draws

def ThresholdLedger.totalBits {N r : ℕ} (l : ThresholdLedger N r) : ℕ :=
  l.bitsPerDraw * l.draws

noncomputable def ThresholdLedger.ofRun (N r : ℕ) (draws rejections : ℕ) (h : rejections ≤ draws) :
    ThresholdLedger N r where
  bitsPerDraw := thresholdWidth N
  draws := draws
  rejections := rejections
  workspaceBits := thresholdWidth N + thresholdWidth (rejections + 1)
  bitsPerDraw_eq := rfl
  rejections_le := h

structure PublicProgramLedger (N r : ℕ) where

  producer : ThresholdLedger N r

  chargedCost : ℕ

  workspaceBits : ℕ

  workspaceBits_eq : workspaceBits = producer.workspaceBits

def PublicProgramLedger.totalRandomness {N r : ℕ} (l : PublicProgramLedger N r) : ℕ :=
  l.producer.totalBits + l.workspaceBits

noncomputable def PublicProgramLedger.ofRun (N r : ℕ) (draws rejections : ℕ)
    (h : rejections ≤ draws) (chargedCost : ℕ) : PublicProgramLedger N r where
  producer := ThresholdLedger.ofRun N r draws rejections h
  chargedCost := chargedCost
  workspaceBits := (ThresholdLedger.ofRun N r draws rejections h).workspaceBits
  workspaceBits_eq := rfl

end Qatlib.Concepts.AmplitudeSearch.Amplification
