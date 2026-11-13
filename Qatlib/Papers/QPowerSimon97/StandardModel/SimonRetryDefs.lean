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

/-!
# Schedules and exact ledgers for Simon retries

This module defines the local Hadamard words, exact resource ledgers, and amplification
schedules used in the standard-model analysis of Simon's algorithm [Simon1997].
`simonAmplifiedError` records the two error expressions, and `simonNegligible` specifies decay
faster than every fixed exponential rate.

The propositions `Clause18LocalGateBridge`, `Clause19Separation`, and
`Clause19TwoSidedSeparation` collect the identities and inequalities established by the
subsequent retry analysis.

## Main statements

* `simonExactLedger`: The product-form resource ledger for `r` blocks with `n + k` samples each.
* `simonAmplifiedError`: The two-sided error pair with false-rejection expression `r * (1 / 2) ^
  k` and false-acceptance expression `(3 / 4) ^ r`.
* `Clause19TwoSidedSeparation`: The proposition collecting amplification errors, exact resource
  counts, decay properties of the quadratic schedule, error comparisons for the paper schedule,
  and its scheduled separation bounds.

## References

* [Simon, 1997][Simon1997]
-/

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

/-- The concatenation of two local Hadamard words on `n` wires. -/
def simonLocalExperiment (n : ℕ) : List (LocalQFTGate n) :=
  localHadamard n ++ localHadamard n

/-- The local gate word obtained by concatenating `m` copies of `simonLocalExperiment n`. -/
def simonLocalBlock (n m : ℕ) : List (LocalQFTGate n) :=
  List.flatten (List.replicate m (simonLocalExperiment n))

/-- The local gate word obtained by concatenating `r` blocks of `m` experiments. -/
def simonLocalDecision (n m r : ℕ) : List (LocalQFTGate n) :=
  List.flatten (List.replicate r (simonLocalBlock n m))

/-- An exact resource ledger for local gates, oracle queries, measurements, and record
conversion. -/
structure SimonExactLedger where

  localGates : ℕ

  oracleQueries : ℕ

  measurements : ℕ

  recordConversion : ℕ

/-- The product-form resource ledger for `r` blocks with `n + k` samples each. -/
def simonExactLedger (n k r : ℕ) : SimonExactLedger where
  localGates := 2 * n * (n + k) * r
  oracleQueries := (n + k) * r
  measurements := (n + k) * r
  recordConversion := (n + k) * n * r

/-- The serialization cost of an array of Boolean-register records. -/
def simonRecordConversionCost {n m : ℕ} (rows : Fin m → Reg n) : ℕ :=
  simonSerializeSteps rows

/-- The paper schedule with sample surplus `2 * n` and repetition count `n`. -/
def simonSchedule (n : ℕ) : ℕ × ℕ := (2 * n, n)

/-- The paper schedule's sample count `n + 2 * n` per block. -/
def simonScheduleSamples (n : ℕ) : ℕ := n + 2 * n

/-- The schedule with both sample surplus and repetition count equal to `n * n`. -/
def simonNegligibleSchedule (n : ℕ) : ℕ × ℕ := (n * n, n * n)

/-- The quadratic schedule's sample count `n + n * n` per block. -/
def simonNegligibleScheduleSamples (n : ℕ) : ℕ := n + n * n

/-- A pair of extended nonnegative real bounds for false rejection and false acceptance. -/
structure SimonTwoSidedError where

  falseReject : ℝ≥0∞

  falseAccept : ℝ≥0∞

/-- The two-sided error pair with false-rejection expression `r * (1 / 2) ^ k` and
false-acceptance expression `(3 / 4) ^ r`. -/
def simonAmplifiedError (_n k r : ℕ) : SimonTwoSidedError where
  falseReject := ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)
  falseAccept := ENNReal.ofReal ((3 / 4 : ℝ) ^ r)

/-- The predicate that a real-valued bound is eventually at most `(1 / 2) ^ (c * n)` for every
positive natural rate `c`. -/
def simonNegligible (bound : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, 0 < c → ∃ N : ℕ, ∀ n ≥ N, bound n ≤ (1 / 2 : ℝ) ^ (c * n)

/-- The quadratic-schedule false-rejection expression `n² * (1 / 2) ^ (n * n)`. -/
def simonCompletingFalseReject (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n * n)

/-- The quadratic-schedule false-acceptance expression `(3 / 4) ^ (n * n)`. -/
def simonCompletingFalseAccept (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ (n * n)

/-- The paper-schedule false-rejection expression `n * (1 / 2) ^ (2 * n)`. -/
def simonPaperFalseReject (n : ℕ) : ℝ :=
  (n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)

/-- The paper-schedule false-acceptance expression `(3 / 4) ^ n`. -/
def simonPaperFalseAccept (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ n

/-- The conjunction of parameter constraints, the classical birthday bound, the quantum
periodic-oracle bound, and a numerical gap under additional budget inequalities. -/
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

/-- The proposition collecting exact local-program lengths, the experiment matrix, conversion
costs, and resource-ledger identities. -/
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

/-- The proposition collecting amplification errors, exact resource counts, decay properties of
the quadratic schedule, error comparisons for the paper schedule, and its scheduled
separation bounds. -/
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
