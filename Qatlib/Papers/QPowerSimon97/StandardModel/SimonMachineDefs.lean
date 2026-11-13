/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution
import Mathlib.Data.Bool.Basic

/-!
# Oracle machines and cost ledgers for Simon's algorithm

This module defines a discrete oracle-machine interface and the costs attached to verified Simon
retries [Simon1997]. `SimonOracleRealizes` relates a machine to a function and a time budget,
while the attempt and history costs combine oracle evaluation, comparison, serialization, and
decoding.

The module also defines amplification record laws, a record-space ledger, and the propositions
`Clause4StandardModelBridge` and `Clause5MachineSeparation` used to collect the resulting
estimates.

## Main statements

* `SimonOracleRealizes`: The predicate that the machine halts with output `f x` at its selected
  spending time, within budget `Tf`, for every input.
* `simonStandardModelG`: Twice the per-attempt upper bound combining quantum queries, local
  gates, oracle running time, output comparison, serialization, and decoding.
* `Clause4StandardModelBridge`: The proposition collecting expected retry-count, bit-cost,
  quantum-query, and unified-cost bounds under the Simon promise and oracle realization
  hypotheses.
* `Clause5MachineSeparation`: The proposition collecting two-sided amplification bounds,
  decoded-run ledgers, fresh-run marginal laws, amplification bit costs, and the sequential
  record count.

## References

* [Simon, 1997][Simon1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open scoped Classical BigOperators ENNReal

/-- An oracle configuration consisting of an input vector, an output vector, and a Boolean halt
flag. -/
abbrev SimonOracleConfig (n m : ℕ) := BooleanVec n × BooleanVec m × Bool

/-- An oracle machine specified by an input-dependent initial configuration and a configuration
transition function. -/
structure SimonOracleMachine (n m : ℕ) where

  init : BooleanVec n → SimonOracleConfig n m

  step : SimonOracleConfig n m → SimonOracleConfig n m

/-- The oracle configuration after a given number of transitions from the machine's initial
configuration. -/
def simonOracleTrace {n m : ℕ} (M : SimonOracleMachine n m) (x : BooleanVec n) :
    ℕ → SimonOracleConfig n m
  | 0 => M.init x
  | k + 1 => M.step (simonOracleTrace M x k)

/-- The halt flag of the oracle-machine trace at time `k`. -/
def simonOracleHaltedB {n m : ℕ} (M : SimonOracleMachine n m) (x : BooleanVec n) (k : ℕ) : Bool :=
  (simonOracleTrace M x k).2.2

/-- The output vector of the oracle-machine trace at time `k`. -/
def simonOracleOutput {n m : ℕ} (M : SimonOracleMachine n m) (x : BooleanVec n) (k : ℕ) :
    BooleanVec m :=
  (simonOracleTrace M x k).2.1

/-- The first halted time between zero and `Tf`, with default value `Tf + 1` if no such time is
found. -/
def simonOracleSpend {n m : ℕ} (M : SimonOracleMachine n m) (x : BooleanVec n) (Tf : ℕ) : ℕ :=
  ((List.range (Tf + 1)).find? (simonOracleHaltedB M x)).getD (Tf + 1)

/-- The predicate that the machine halts with output `f x` at its selected spending time, within
budget `Tf`, for every input. -/
def SimonOracleRealizes {n m : ℕ} (f : BooleanVec n → BooleanVec m)
    (M : SimonOracleMachine n m) (Tf : ℕ) : Prop :=
  ∀ x : BooleanVec n,
    simonOracleHaltedB M x (simonOracleSpend M x Tf) = true ∧
    simonOracleOutput M x (simonOracleSpend M x Tf) = f x ∧
    simonOracleSpend M x Tf ≤ Tf

/-- Compares two registers at the listed positions and counts one comparison per position. -/
def simonComparePrefix {m : ℕ} (a b : Reg m) : List (Fin m) → Bool × ℕ
  | [] => (true, 0)
  | j :: rest =>
      let r := simonComparePrefix a b rest
      (r.1 && decide (a j = b j), r.2 + 1)

/-- Compares two full registers and returns the Boolean result together with its comparison
count. -/
def simonCompareCounted {m : ℕ} (a b : Reg m) : Bool × ℕ :=
  simonComparePrefix a b (List.finRange m)

/-- The optional secret obtained by decoding the bit representation of a Simon retry record. -/
def simonAttemptCandidate {n : ℕ} (xs : SimonRetryRecord n) : Option (Reg n) :=
  decodeSimonSecret (simonRecordBits xs)

/-- The verification query count: zero when decoding fails and two when it yields a candidate. -/
def simonAttemptOracleQueries {n : ℕ} (xs : SimonRetryRecord n) : ℕ :=
  match simonAttemptCandidate xs with
  | none => 0
  | some _ => 2

/-- The sum of sample serialization steps and counted decoder operations for one retry record. -/
def simonAttemptLocalWork {n : ℕ} (xs : SimonRetryRecord n) : ℕ :=
  simonSerializeSteps (simonRecordBits xs) + (decodeSimonWithCost (simonRecordBits xs)).2

/-- The local work of one retry record, augmented by two oracle running times and an
output-width comparison charge when a candidate is present. -/
def simonAttemptBitCost {n m : ℕ} (M : SimonOracleMachine n m) (Tf : ℕ)
    (xs : SimonRetryRecord n) : ℕ :=
  match simonAttemptCandidate xs with
  | none => simonAttemptLocalWork xs
  | some t =>
      simonAttemptLocalWork xs
        + simonOracleSpend M (regBooleanEquiv n t) Tf
        + simonOracleSpend M 0 Tf
        + m

/-- The per-attempt ledger of `n + 1` oracle queries, `2 * (n + 1)` local gates, and `n + 1`
measurements. -/
def simonAttemptQuantumSteps {n : ℕ} : ℕ × ℕ × ℕ := (n + 1, 2 * (n + 1), n + 1)

/-- The sum of one attempt's quantum query count, local quantum gate count, and classical bit
cost. -/
def simonAttemptUnifiedCost {n m : ℕ} (M : SimonOracleMachine n m) (Tf : ℕ)
    (xs : SimonRetryRecord n) : ℕ :=
  simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1 + simonAttemptBitCost M Tf xs

/-- The sum of the bit costs of all records in a retry history. -/
def simonHistoryBitCost {n m : ℕ} (M : SimonOracleMachine n m) (Tf : ℕ)
    (h : Option (Reg n) × List (SimonRetryRecord n)) : ℕ :=
  (h.2.map (simonAttemptBitCost M Tf)).sum

/-- The componentwise per-attempt quantum ledger multiplied by the number of history records. -/
def simonHistoryQuantumSteps {n : ℕ} (h : Option (Reg n) × List (SimonRetryRecord n)) :
    ℕ × ℕ × ℕ :=
  (h.2.length * simonAttemptQuantumSteps (n := n).1,
    h.2.length * simonAttemptQuantumSteps (n := n).2.1,
    h.2.length * simonAttemptQuantumSteps (n := n).2.2)

/-- The sum of unified costs over all records in a retry history. -/
def simonHistoryUnifiedCost {n m : ℕ} (M : SimonOracleMachine n m) (Tf : ℕ)
    (h : Option (Reg n) × List (SimonRetryRecord n)) : ℕ :=
  (h.2.map (simonAttemptUnifiedCost M Tf)).sum

/-- Twice the per-attempt upper bound combining quantum queries, local gates, oracle running
time, output comparison, serialization, and decoding. -/
def simonStandardModelG (n m : ℕ) (Tf : ℕ) : ℕ :=
  2 * (simonAttemptQuantumSteps (n := n).1 + simonAttemptQuantumSteps (n := n).2.1
    + 2 * Tf + m + (n + 1) * n + simonBlockOpsBound n)

/-- The joint law of `r` independent blocks of `m` hidden-subgroup character samples. -/
noncomputable def simonRecordRuns {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (m r : ℕ) :
    PMF (Fin r → (Fin m → AddChar (BooleanVec n) ℂ)) :=
  match r with
  | 0 => PMF.pure (fun _ => (fun _ => (0 : AddChar (BooleanVec n) ℂ)))
  | r + 1 =>
      PMF.bind (hiddenSubgroupFreshSamples f (booleanCharacterEquiv n).toEquiv m)
        (fun xs => PMF.map (Fin.cons xs) (simonRecordRuns f m r))

/-- The Boolean rejection result obtained from the decoded candidates of the recorded sample
blocks. -/
def simonRecordRunsReject {n m r : ℕ}
    (rs : Fin r → (Fin m → AddChar (BooleanVec n) ℂ)) : Bool :=
  simonAnyRejectBits (fun i => decodeSimonSecret (simonRecordBits (rs i)))

/-- The polynomial decoder bound `10 * (s * n² + n³ + s * n + n² + n + 1)`. -/
def simonEliminationBound (n s : ℕ) : ℕ := 10 * (s * n^2 + n^3 + s * n + n^2 + n + 1)

/-- The serialization and decoding cost of one amplification block, plus two oracle evaluation
times and output comparison when a candidate is decoded. -/
def simonAmplifiedRunCost {n w s : ℕ} (M : SimonOracleMachine n w) (Tf : ℕ)
    (rows : Fin s → AddChar (BooleanVec n) ℂ) : ℕ :=
  simonSerializeSteps (simonRecordBits rows)
    + (decodeSimonWithCost (simonRecordBits rows)).2
    + match decodeSimonSecret (simonRecordBits rows) with
      | none => 0
      | some t =>
          simonOracleSpend M (regBooleanEquiv n t) Tf + simonOracleSpend M 0 Tf + w

/-- The sum of the bit costs of all amplification blocks. -/
def simonAmplifiedBitCost {n w s r : ℕ} (M : SimonOracleMachine n w) (Tf : ℕ)
    (rs : Fin r → (Fin s → AddChar (BooleanVec n) ℂ)) : ℕ :=
  (Finset.univ : Finset (Fin r)).sum (fun i => simonAmplifiedRunCost M Tf (rs i))

/-- A ledger containing a record count and a qubit count. -/
structure SimonSpaceLedger where

  records : ℕ

  qubits : ℕ

/-- The block-space ledger with one record and `n + m` qubits. -/
def simonBlockSpace (n m : ℕ) : SimonSpaceLedger := ⟨1, n + m⟩

/-- Recursively runs decoded sample blocks until a result other than the zero candidate is
found, while tracking a peak record count. -/
noncomputable def simonSequentialAmplifiedAux {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (m : ℕ) : ℕ → PMF Bool × ℕ
  | 0 => (PMF.pure false, 0)
  | i + 1 =>
      let rest := simonSequentialAmplifiedAux f m i
      ((PMF.bind ((simonDecodedRun f m).1) fun out =>
          if out = some (ZeroStr n) then rest.1 else PMF.pure true),
        max 1 rest.2)

/-- The sequential amplification output law paired with its peak record count. -/
noncomputable def simonSequentialAmplified {n : ℕ} {R : Type} [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (m r : ℕ) : PMF Bool × ℕ :=
  simonSequentialAmplifiedAux f m r

/-- The average probability that the amplified Simon decision procedure guesses the label of an
oracle-construction draw correctly. -/
noncomputable def simonQuantumGuessMass {n : ℕ} (k r : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonOracleConstruction n)
    (fun ob =>
      if ob.1 then
        (simonAmplifiedReject (ob.2 : BooleanVec n → BooleanVec n) (n + k) r) true
      else
        1 - (simonAmplifiedReject (ob.2 : BooleanVec n → BooleanVec n) (n + k) r) true)

/-- The proposition collecting expected retry-count, bit-cost, quantum-query, and unified-cost
bounds under the Simon promise and oracle realization hypotheses. -/
def Clause4StandardModelBridge : Prop :=
  ∀ (n m : ℕ) (f : BooleanVec n → BooleanVec m) (s : Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    ∀ (M : SimonOracleMachine n m) (Tf : ℕ), SimonOracleRealizes f M Tf →
    ∀ (T : ℕ),

      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (simonVerifiedHistory f T)
          (fun h => (h.2.length : ℝ≥0∞)) ≤ 2 ∧

      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
          (PMF.map (fun h => (h.1, simonHistoryBitCost M Tf h)) (simonVerifiedHistory f T))
        ≤ 2 * (2 * Tf + m + (n + 1) * n + simonBlockOpsBound n) ∧

      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
          (PMF.map (fun h => (h.1, (simonHistoryQuantumSteps h).1)) (simonVerifiedHistory f T))
        ≤ 2 * simonAttemptQuantumSteps (n := n).1 ∧

      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
          (PMF.map (fun h => (h.1, simonHistoryUnifiedCost M Tf h)) (simonVerifiedHistory f T))
        ≤ simonStandardModelG n m Tf

/-- The proposition collecting two-sided amplification bounds, decoded-run ledgers, fresh-run
marginal laws, amplification bit costs, and the sequential record count. -/
def Clause5MachineSeparation : Prop :=

  (∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
      (f : BooleanVec n → R) (k r : ℕ), 2 ≤ n + k →
    (Function.Injective f →
      (simonAmplifiedReject f (n + k) r) true ≤ ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n →
        (simonAmplifiedReject f (n + k) r) false ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r)) ∧
    ((simonDecodedRun f (n + k)).2 = (n + k, 2 * (n + k), n + k) ∧
      (∀ (i : Fin r), PMF.map (fun v => v i) (simonFreshRuns f (n + k) r) =
        (simonDecodedRun f (n + k)).1)))
  ∧

    (∀ {n : ℕ} (k r : ℕ) (M : SimonOracleMachine n n) (Tf : ℕ)
      (f : BooleanVec n → BooleanVec n),
      SimonOracleRealizes f M Tf →
      ∀ rs : Fin r → (Fin (n + k) → AddChar (BooleanVec n) ℂ),
        simonAmplifiedBitCost M Tf rs
          ≤ r * ((n + k) * n + simonEliminationBound n (n + k) + 2 * Tf + n))
  ∧

    (∀ {n : ℕ} (m r : ℕ) (f : BooleanVec n → BooleanVec n),
      (simonSequentialAmplified f m r).2 = if r = 0 then 0 else 1)

  ∧ True

end Qatlib.Papers.QPowerSimon97.StandardDefs
