/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseExecutionDefs
import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AmpTransform.FullLayerCF.FullLayerCFDenoiseUniquePAmpl
import Qatlib.Concepts.AmpTransform.FullLayerCF.WrapUnknownMRecovery
import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarGeneralWNAmpl
import Qatlib.Concepts.QftPreparation.LocalQft
import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliZeroModeTransportAmpl

/-!
# Statements for amplified period-recovery completion

`aqFreshCompletionRecord` pairs candidates with a fresh observed set. The completion
propositions specify fixed-noise verification and ambiguity, cyclic verification, Haar and
fair-label sampling results, fresh-observation recovery, and Bernoulli zero-mode transport.

These definitions state the interfaces assembled by the proofs in `AmplifiedPeriod`.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `aqCompletionFixedNoiseEndpoint`: fixed-noise candidate and ambiguity requirements.
* `aqCompletionFreshAccessEndpoint`: fresh-observation probability and recovery requirements.
* `aqCompletionZeroModeEndpoint`: the zero-mode transport requirement.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

set_option autoImplicit false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib
open scoped Classical BigOperators ENNReal

/-- Finite sets of natural-number candidate periods. -/
abbrev aqCompletionCandidates := Finset ℕ

/-- A record pairing a finite candidate set with an observed subset of the register. -/
structure aqFreshCompletionRecord (N : ℕ) where

  candidates : Finset ℕ

  observation : Finset (Fin N)
  deriving DecidableEq

/-- The conjunction of candidate verification, the candidate-record query bound, the denoising
statement, and a fixed-noise example with two accepted periods. -/
def aqCompletionFixedNoiseEndpoint : Prop :=
  (∀ (N : ℕ) (h : Fin N → Bool) (s M B : ℕ) (xs : List (Fin N)) (p : ℕ),
      p ∈ aqCandidateRecord h s M B xs → (aqVerify h s M p).1 = true) ∧
  (∀ (N : ℕ) (h : Fin N → Bool) (s M B k : ℕ) (xs : List (Fin N)),
      aqCandidateRecordQueries h s M B k xs ≤ xs.length * (k + 3)) ∧
  FullLayerCFDenoiseUniqueP ∧
  ((aqProgressionSet 128 0 4 2 ∪ ({8, 12} : Finset (Fin 128))) =
      (aqProgressionSet 128 0 4 4 ∪ ({2, 6} : Finset (Fin 128)))) ∧
  ((aqVerify (fun x : Fin 128 =>
      decide (x ∈ (aqProgressionSet 128 0 4 2 ∪ ({8, 12} : Finset (Fin 128))))) 0 4 2).1
      = true) ∧
  ((aqVerify (fun x : Fin 128 =>
      decide (x ∈ (aqProgressionSet 128 0 4 2 ∪ ({8, 12} : Finset (Fin 128))))) 0 4 4).1
      = true)

/-- The planted cyclic-verification guarantee and the bound of three queries for any cyclic
verification call. -/
def aqCompletionWrapEndpoint : Prop :=
  (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ)
      (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N) (G : Finset (Fin N))
      (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
        (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)),
      aqCyclicVerify N hN h s M P = (true, 3)) ∧
  (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ),
      (aqCyclicVerify N hN h s M q).2 ≤ 3)

/-- The conjunction of the general Haar statement, the bounded fair-label sampler distribution,
and the local QFT gate count. -/
def aqCompletionHaarEndpoint : Prop :=
  HaarGeneralWN ∧
  (∀ (C fuel : ℕ) (hC : 0 < C),
      ∀ j : Fin C,
        CostedLaw.event (aqFairLabelSampler C fuel)
            (fun z => z.1 = Sum.inl j) =
          (1 - coinRejectMass (Nat.clog 2 C) C ^ fuel) / (C : ℝ≥0∞)) ∧
  (∀ n : ℕ,
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2)

/-- The Bernoulli site marginal and exact candidate-consistency probability, together with
recovery when all false candidates are inconsistent. -/
def aqCompletionFreshAccessEndpoint : Prop :=
  (∀ (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin N),
      (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        (if σ i then 1 else 0)) = p) ∧
  (∀ (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
        = p ^ (aqCandidateSeparation N s M P P')) ∧
  (∀ (N s M P : ℕ) (p : ℝ) (cands : Finset ℕ) (hP : P ∈ cands) (σ : Fin N → Bool)
      (hrefute : ∀ P' ∈ cands \ {P},
        ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)),
      aqFreshDisambiguate N s M cands p (aqFreshMarked N s M P σ) = some P)

/-- The Bernoulli error-stream zero-mode transport statement used in period-recovery completion. -/
def aqCompletionZeroModeEndpoint : Prop :=
  BernoulliErrorStreamZeroModeTransport

end Qatlib.Concepts.AmpTransform.ErrorStream
