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

/-!
# Dyadic threshold laws and minimum-search ledgers

This module defines the probability laws and resource records for producing an initial threshold
index from a uniform dyadic word. `acceptThreshold` retains words below the table size, while
`thresholdScan` and `thresholdRunLaw` record the first accepted index and its preceding
rejections, with an explicit failed outcome when the available draws are exhausted.

`ThresholdLedger` records draws, rejections, and workspace; `PublicProgramLedger` combines that
producer record with charged search cost. These definitions provide a bookkeeping interface for
the minimum-finding setting of [DurrHoyer1996].

## Main statements

* `fairBitLaw`, `fairWordLaw`, and `producerWordLaw` specify uniform Boolean and dyadic-word
  laws.
* `thresholdWidth`, `thresholdWords`, `thresholdRejectProb`, and `thresholdAcceptProb` specify
  the word width and one-round proportions.
* `thresholdRunLaw` defines the law of at most `r` threshold draws, and `thresholdCostedLaw`
  attaches the fixed charge `thresholdWidth N * (r + 1)`.
* `ThresholdLedger.ofRun` and `PublicProgramLedger.ofRun` assemble resource records from
  supplied run counts and charged cost.

## References

- [Dürr and Høyer, 1996][DurrHoyer1996]. *A quantum algorithm for finding the minimum*. 1996.
-/

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

/-- The uniform PMF on Boolean values. -/
noncomputable def fairBitLaw : PMF Bool := PMF.uniformOfFintype' Bool

/-- The uniform PMF on the `2 ^ k` possible words represented by `Fin (2 ^ k)`. -/
noncomputable def fairWordLaw (k : ℕ) : PMF (Fin (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨by positivity⟩
  exact PMF.uniformOfFintype' _

/-- The dyadic producer's word width, defined as the initialization charge `initCharge N`. -/
noncomputable def thresholdWidth (N : ℕ) : ℕ := initCharge N

/-- The number `2 ^ thresholdWidth N` of words available to the threshold producer. -/
noncomputable def thresholdWords (N : ℕ) : ℕ := 2 ^ thresholdWidth N

/-- The uniform PMF on the dyadic word space `Fin (thresholdWords N)`. -/
noncomputable def producerWordLaw (N : ℕ) : PMF (Fin (thresholdWords N)) := by
  letI : Nonempty (Fin (thresholdWords N)) :=
    ⟨⟨0, by unfold thresholdWords; positivity⟩⟩
  exact PMF.uniformOfFintype' _

/-- The real ratio of the natural-number difference `thresholdWords N - N` to `thresholdWords
N`, used as the one-round rejection probability. -/
noncomputable def thresholdRejectProb (N : ℕ) : ℝ :=
  ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ)

/-- The real ratio `N / thresholdWords N`, used as the one-round acceptance probability. -/
noncomputable def thresholdAcceptProb (N : ℕ) : ℝ :=
  (N : ℝ) / (thresholdWords N : ℝ)

/-- Accepts a dyadic word as an index when its value is below `N`, and returns `none` otherwise. -/
def acceptThreshold (N : ℕ) (w : Fin (thresholdWords N)) : Option (Fin N) :=
  if h : w.val < N then some ⟨w.val, h⟩ else none

/-- Scans a list of dyadic words for the first accepted index, returning it with the number of
preceding rejected words. Returns `none` when every word is rejected. -/
def thresholdScan : (N : ℕ) → List (Fin (thresholdWords N)) → Option (Fin N × ℕ)
  | _, [] => none
  | N, w :: ws => match acceptThreshold N w with
      | some i => some (i, 0)
      | none => (thresholdScan N ws).map (fun p => (p.1, p.2 + 1))

/-- The outcome of a threshold producer with at most `r` draws: an accepted index with a
rejection count in `Fin r`, or explicit failure. -/
inductive ThresholdOutcome (N r : ℕ) where

  | accepted (index : Fin N) (rejections : Fin r)

  | failed
  deriving DecidableEq, Repr, Fintype

/-- Returns the rejection count stored in an accepted outcome, and returns zero for a failed
outcome. -/
def ThresholdOutcome.rejections {N r : ℕ} (o : ThresholdOutcome N r) : ℕ :=
  match o with
  | .accepted _ n => n.val
  | .failed => 0

/-- Returns the accepted index as an option, with `none` for a failed outcome. -/
def ThresholdOutcome.index {N r : ℕ} (o : ThresholdOutcome N r) : Option (Fin N) :=
  match o with
  | .accepted i _ => some i
  | .failed => none

/-- The law of accepting or rejecting one uniform producer word through `acceptThreshold`. -/
noncomputable def thresholdRoundLaw (N : ℕ) : PMF (Option (Fin N)) :=
  (producerWordLaw N).map (acceptThreshold N)

/-- Increments the rejection count of an accepted outcome when extending the draw bound from `r`
to `r + 1`, and preserves failure. -/
def bumpOutcome {N r : ℕ} : ThresholdOutcome N r → ThresholdOutcome N (r + 1)
  | .accepted i n => .accepted i ⟨n.val + 1, by omega⟩
  | .failed => .failed

/-- The law of threshold sampling with at most `r` draws, stopping at the first accepted index.
A rejected first draw recurses on the remaining draws and increments any accepted rejection
count. -/
noncomputable def thresholdRunLaw (N : ℕ) : (r : ℕ) → PMF (ThresholdOutcome N r)
  | 0 => PMF.pure .failed
  | r + 1 => (thresholdRoundLaw N).bind fun o => match o with
      | some i => PMF.pure (.accepted i ⟨0, by omega⟩)
      | none => (thresholdRunLaw N r).map (bumpOutcome)

/-- Attaches the fixed natural-number charge `thresholdWidth N * (r + 1)` to every outcome of
`thresholdRunLaw N r`. -/
noncomputable def thresholdCostedLaw (N : ℕ) (r : ℕ) : CostedLaw (ThresholdOutcome N r) :=
  (thresholdRunLaw N r).map (fun o => (o, thresholdWidth N * (r + 1)))

/-- A resource record for threshold production containing bits per draw, draw and rejection
counts, and workspace bits. Its constraints fix the word width and require no more
rejections than draws. -/
structure ThresholdLedger (N r : ℕ) where

  bitsPerDraw : ℕ

  draws : ℕ

  rejections : ℕ

  workspaceBits : ℕ

  bitsPerDraw_eq : bitsPerDraw = thresholdWidth N

  rejections_le : rejections ≤ draws

/-- The producer's recorded bit consumption, computed as bits per draw times the number of
draws. -/
def ThresholdLedger.totalBits {N r : ℕ} (l : ThresholdLedger N r) : ℕ :=
  l.bitsPerDraw * l.draws

/-- Builds a threshold ledger from draw and rejection counts satisfying `rejections ≤ draws`. It
records workspace as `thresholdWidth N + thresholdWidth (rejections + 1)`. -/
noncomputable def ThresholdLedger.ofRun (N r : ℕ) (draws rejections : ℕ) (h : rejections ≤ draws) :
    ThresholdLedger N r where
  bitsPerDraw := thresholdWidth N
  draws := draws
  rejections := rejections
  workspaceBits := thresholdWidth N + thresholdWidth (rejections + 1)
  bitsPerDraw_eq := rfl
  rejections_le := h

/-- A combined record containing a threshold producer ledger, charged search cost, and workspace
bits constrained to equal the producer's workspace. -/
structure PublicProgramLedger (N r : ℕ) where

  producer : ThresholdLedger N r

  chargedCost : ℕ

  workspaceBits : ℕ

  workspaceBits_eq : workspaceBits = producer.workspaceBits

/-- The combined ledger quantity obtained by adding the producer's total bits to the recorded
workspace bits. -/
def PublicProgramLedger.totalRandomness {N r : ℕ} (l : PublicProgramLedger N r) : ℕ :=
  l.producer.totalBits + l.workspaceBits

/-- Builds a combined ledger from valid producer counts and a supplied charged cost, copying the
producer's workspace count. -/
noncomputable def PublicProgramLedger.ofRun (N r : ℕ) (draws rejections : ℕ)
    (h : rejections ≤ draws) (chargedCost : ℕ) : PublicProgramLedger N r where
  producer := ThresholdLedger.ofRun N r draws rejections h
  chargedCost := chargedCost
  workspaceBits := (ThresholdLedger.ofRun N r draws rejections h).workspaceBits
  workspaceBits_eq := rfl

end Qatlib.Concepts.AmplitudeSearch.Amplification
