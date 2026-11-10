/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry
import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
import Qatlib.Papers.QPowerSimon97.StandardModel.SimonMachineDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open Qatlib.Papers.QPowerSimon97.StandardDefs
open scoped Classical BigOperators ENNReal

def simonLocalExperiment (n : ℕ) : List (LocalQFTGate n) :=
  localHadamard n ++ localHadamard n

def simonLocalBlock (n m : ℕ) : List (LocalQFTGate n) :=
  List.flatten (List.replicate m (simonLocalExperiment n))

def simonLocalDecision (n m r : ℕ) : List (LocalQFTGate n) :=
  List.flatten (List.replicate r (simonLocalBlock n m))

structure SimonExactLedger where

  localGates : ℕ

  oracleQueries : ℕ

  measurements : ℕ

  recordConversion : ℕ

def simonExactLedger (n k r : ℕ) : SimonExactLedger where
  localGates := 2 * n * (n + k) * r
  oracleQueries := (n + k) * r
  measurements := (n + k) * r
  recordConversion := (n + k) * n * r

def simonRecordConversionCost {n m : ℕ} (rows : Fin m → Reg n) : ℕ :=
  simonSerializeSteps rows

def simonSchedule (n : ℕ) : ℕ × ℕ := (2 * n, n)

def simonScheduleSamples (n : ℕ) : ℕ := n + 2 * n

def simonNegligibleSchedule (n : ℕ) : ℕ × ℕ := (n * n, n * n)

def simonNegligibleScheduleSamples (n : ℕ) : ℕ := n + n * n

structure SimonTwoSidedError where

  falseReject : ℝ≥0∞

  falseAccept : ℝ≥0∞

def simonAmplifiedError (_n k r : ℕ) : SimonTwoSidedError where
  falseReject := ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)
  falseAccept := ENNReal.ofReal ((3 / 4 : ℝ) ^ r)

def simonNegligible (bound : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, 0 < c → ∃ N : ℕ, ∀ n ≥ N, bound n ≤ (1 / 2 : ℝ) ^ (c * n)

def simonCompletingFalseReject (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n * n)

def simonCompletingFalseAccept (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ (n * n)

def simonPaperFalseReject (n : ℕ) : ℝ :=
  (n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)

def simonPaperFalseAccept (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ n

def Clause19Separation (n q k r : ℕ) : Prop :=
  1 ≤ n ∧ 1 ≤ q ∧ 2 ≤ n + k ∧
  (∀ P : PMF (SimonQueryTree n), SimonQueryTree.bounded P q →
      simonOracleGuessMass P ≤
        (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹)
  ∧ (∀ f : BooleanVec n → BooleanVec n,
      (∃ s : BooleanVec n, s ≠ 0 ∧ ∀ x : BooleanVec n, f x = f (x + s)) →
        (simonAmplifiedReject f (n + k) r) true + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) ≥ 1)
  ∧ (8 * q * q ≤ 2 ^ n → (3 / 4 : ℝ) ^ r ≤ 1 / 8 →
      ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹ ≤ ENNReal.ofReal (1 / 8) ∧
      (1 / 2 : ENNReal) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
        ≤ ENNReal.ofReal (5 / 8) ∧
      ENNReal.ofReal (1 / 2) + ((q * q : ℕ) : ENNReal) * (2 ^ n : ENNReal)⁻¹
          + ENNReal.ofReal ((3 / 4 : ℝ) ^ r) < 1)

def Clause18LocalGateBridge : Prop :=
  (∀ n : ℕ,
      (simonLocalExperiment n).length = 2 * n ∧
      localProgramMatrix (simonLocalExperiment n) = HadamardN n * HadamardN n)
  ∧ (∀ n m : ℕ, (simonLocalBlock n m).length = 2 * n * m)
  ∧ (∀ n m r : ℕ, (simonLocalDecision n m r).length = 2 * n * m * r)
  ∧ (∀ (n m : ℕ) (rows : Fin m → Reg n), simonRecordConversionCost rows = m * n)
  ∧ (∀ n k r : ℕ,
      (simonLocalDecision n (n + k) r).length = (simonExactLedger n k r).localGates ∧
      (simonExactLedger n k r).oracleQueries = (n + k) * r ∧
      (simonExactLedger n k r).measurements = (n + k) * r ∧
      (simonExactLedger n k r).recordConversion = (n + k) * n * r)

def Clause19TwoSidedSeparation : Prop :=
  (∀ (n k r : ℕ) {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
      (f : BooleanVec n → R), 2 ≤ n + k →
    Function.Injective f →
      (simonAmplifiedReject f (n + k) r) true ≤ (simonAmplifiedError n k r).falseReject ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n →
        (simonAmplifiedReject f (n + k) r) false ≤ (simonAmplifiedError n k r).falseAccept))
  ∧ (∀ n k r : ℕ,
      (simonExactLedger n k r).oracleQueries = (n + k) * r ∧
      (simonExactLedger n k r).localGates = 2 * n * (n + k) * r)
  ∧ (simonNegligible simonCompletingFalseReject ∧
      simonNegligible simonCompletingFalseAccept)
  ∧ (∀ n : ℕ, 1 ≤ n → simonPaperFalseReject n ≤ (1 / 2 : ℝ) ^ n)
  ∧ (∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) ^ n < simonPaperFalseAccept n)
  ∧ (∀ n : ℕ, 64 ≤ n → 4 ∣ n →
      Clause19Separation n (2 ^ (n / 4)) (2 * n) n ∧
        n * (n + 2 * n) ≤ 2 ^ (n / 4) ∧
        8 * (2 ^ (n / 4)) * (2 ^ (n / 4)) ≤ 2 ^ n)

end Qatlib.Papers.QPowerSimon97.StandardDefs
