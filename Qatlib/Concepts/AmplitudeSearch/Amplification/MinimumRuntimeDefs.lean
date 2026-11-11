/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainderDefs
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainderDefs

/-!
# Runtime models for quantum minimum search

This module defines the classical, quantum, and hybrid runtime objects used to implement quantum
minimum search [DurrHoyer1996] with BBHT attempts [BoyerEtAl1998]. It includes binary table
comparison, encoded checked-search circuits, explicit state preparation and reset, capped depth
sampling, and growing retry schedules.

The retry reports distinguish a found index, exhaustion of the supplied schedule, and sampler
timeout. Cost moments and limiting expressions track queries, gates, measurements, and
random-bit reads; the `UniformTape` namespace supplies a native tape sampler and workspace
observables.

## Main statements

* `hybridRetry`: runs prepared checked attempts with capped depth sampling and resets after
  failure.
* `effectiveBBHTSize`: computes the integer BBHT search width at each stage.
* `retryCapLimitMoment`: defines the limiting cost recurrence for a fixed retry schedule.
* `UniformTape.program`: implements the uniform rejection sampler as a native tape program.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib

/-- The natural number represented by a Boolean list read with the most significant bit first. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + binaryValue bs

/-- The three-state lexicographic comparison update, recording the first unequal bit pair and
preserving any previously decided order. -/
def compareUpdate (q : Fin 3) (ab : Bool × Bool) : Fin 3 :=
  if q = 0 then
    if ab.1 = ab.2 then 0 else if ab.1 then 2 else 1
  else q

/-- A tape machine that scans bit pairs to the right using `compareUpdate` and halts at a blank
cell. -/
def compareMachine : Turing.TM0.Machine (Option (Bool × Bool)) (Fin 3)
  | _, none => none
  | q, some ab => some (compareUpdate q ab, .move .right)

/-- The Boolean test that the comparison state is `1`, representing strict less-than. -/
def compareAccept (q : Fin 3) : Bool := q == 1

/-- Strict lexicographic comparison of paired Boolean lists, returning false when all pairs are
equal. -/
def lexLess : List (Bool × Bool) → Bool
  | [] => false
  | (a,b) :: xs => if a = b then lexLess xs else !a

/-- The list of corresponding bit pairs from two registers of the same width. -/
def registerPairs {n : ℕ} (x y : Reg n) : List (Bool × Bool) :=
  List.ofFn fun i => (x i, y i)

/-- The optional comparison result obtained by running the paired-bit tape machine on two
registers with fuel equal to their width. -/
def compareRegisters {n : ℕ} (x y : Reg n) : Option Bool :=
  tapeDecision compareMachine compareAccept ((registerPairs x y).map some) n

/-- A table of `N` entries, each stored as a Boolean register of width `width`. -/
abbrev EncodedTable (N width : ℕ) := Fin N → Reg width

/-- The natural number represented by the register at a given encoded-table index. -/
def tableValue {N width : ℕ} (T : EncodedTable N width) (i : Fin N) : ℕ :=
  binaryValue (List.ofFn (T i))

/-- The optional tape-machine comparison result for two encoded-table entries. -/
def tableCompare {N width : ℕ} (T : EncodedTable N width) (i j : Fin N) : Option Bool :=
  compareRegisters (T i) (T j)

/-- A capped uniform rejection sampler on `Fin N` using blocks of `Nat.clog 2 N` random bits. -/
def initialIndexCode (N cap : ℕ) :=
  weightedSampler (fun _ : Fin N => 1) (Nat.clog 2 N) cap
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib

/-- The equivalence encoding an index and Boolean ancilla as an element of `Fin (N * 2)`. -/
def indexBitEquiv (N : ℕ) : Fin N × Bool ≃ Fin (N * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) boolEquivFin2).trans finProdFinEquiv

/-- A state on an index and Boolean ancilla reindexed along `indexBitEquiv`. -/
noncomputable def encodeState {N : ℕ} (ψ : QState (Fin N × Bool)) : QState (Fin (N * 2)) :=
  ψ ∘ (indexBitEquiv N).symm

/-- A matrix on index-ancilla pairs reindexed as an operator on `Fin (N * 2)`. -/
noncomputable def encodeGate {N : ℕ} (U : Matrix (Fin N × Bool) (Fin N × Bool) ℂ) :
    Operator (N * 2) := Matrix.reindex (indexBitEquiv N) (indexBitEquiv N) U

/-- The circuit-step encoding that reindexes gates and preserves oracle-query steps. -/
noncomputable def encodeStep {N : ℕ} : Step (Fin N × Bool) → Step (Fin (N * 2))
  | .gate U => .gate (encodeGate U)
  | .query => .query

/-- A circuit reindexed from index-ancilla pairs to `Fin (N * 2)` by encoding each step. -/
noncomputable def encodeCircuit {N : ℕ} (C : Circuit (Fin N × Bool)) : Circuit (Fin (N * 2)) :=
  C.map encodeStep

/-- The permutation that preserves the encoded index and XORs the encoded ancilla with the
supplied Boolean. -/
def resetFlip (N : ℕ) (b : Bool) (x : Fin (N * 2)) : Fin (N * 2) :=
  indexBitEquiv N (((indexBitEquiv N).symm x).1, ((indexBitEquiv N).symm x).2 ^^ b)

/-- The permutation operator associated with the ancilla flip `resetFlip N b`. -/
noncomputable def resetGate (N : ℕ) (b : Bool) : Operator (N * 2) := permMatrix (resetFlip N b)

/-- The encoded ancilla bit viewed as an element of `Fin 2`. -/
def bitLabel (N : ℕ) (x : Fin (N * 2)) : Fin 2 :=
  boolEquivFin2 ((indexBitEquiv N).symm x).2

/-- An observed circuit that measures the full basis index, resets its ancilla, queries the
oracle, and accepts exactly when the measured oracle bit is one. -/
noncomputable def checkedReadout (N : ℕ) : ObservedCircuit (Fin (N * 2)) :=
  .measure (N * 2) id fun x =>
    .step (.gate (resetGate N ((indexBitEquiv N).symm x).2))
      (.step .query (.measure 2 (bitLabel N) (fun b => .halt (b == 1))))

/-- The unnormalized leaf state for a full-basis outcome followed by an oracle-bit outcome, with
zero state when the bit disagrees with the oracle. -/
noncomputable def checkedLeafState {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) (b : Fin 2) : QState (Fin (N * 2)) :=
  if boolEquivFin2 (f ((indexBitEquiv N).symm x).1) = b then
    ψ x • Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1, f ((indexBitEquiv N).symm x).1))
  else 0

/-- The checked-readout branch trace with its leaf state, acceptance bit, one query, one gate,
two measurements, and measurement outcomes. -/
noncomputable def checkedTrace {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) (b : Fin 2) : BranchTrace (Fin (N * 2)) :=
  ⟨checkedLeafState f ψ x b, b == 1, 1, 1, 2, [(N * 2, x.val), (2, b.val)]⟩

/-- The observed program obtained by placing every step of a circuit before another observed
program. -/
noncomputable def prependCircuit {D : ℕ} : Circuit (Fin D) → ObservedCircuit (Fin D) → ObservedCircuit (Fin D)
  | [], P => P
  | s :: C, P => .step s (prependCircuit C P)

/-- A branch trace with the query and gate counts of a prepended circuit added to its counters. -/
def addCircuitCounts {D : ℕ} (C : Circuit (Fin D)) (t : BranchTrace (Fin D)) : BranchTrace (Fin D) :=
  {t with queries := t.queries + QueryCount C, gates := t.gates + GateCount C}

/-- An observed search attempt consisting of the encoded lifted search circuit at depth `j`
followed by checked readout. -/
noncomputable def checkedAttempt (N j : ℕ) : ObservedCircuit (Fin (N * 2)) :=
  prependCircuit (encodeCircuit (LiftCircuit (SearchCircuit (Fin N) j))) (checkedReadout N)

/-- The checked-search branch trace at depth `j`, including the search circuit's query and gate
counts. -/
noncomputable def attemptTrace {N : ℕ} (A : Finset (Fin N)) (j : ℕ)
    (x : Fin (N * 2)) (b : Fin 2) : BranchTrace (Fin (N * 2)) :=
  addCircuitCounts (encodeCircuit (LiftCircuit (SearchCircuit (Fin N) j)))
    (checkedTrace (fun i => decide (i ∈ A)) (encodeState (CheckedSearchState A j)) x b)

/-- A capped-feedback BBHT program that samples a depth uniformly, runs the checked attempt on a
returned depth, and rejects on sampler timeout. -/
noncomputable def bbhtProgram (N m : ℕ) : CappedFeedback (N * 2) m where
  first := .halt true
  weights _ _ := 1
  width _ := Nat.clog 2 m
  next _ a := match a.1 with
    | .inr _ => .halt false
    | .inl (j,_,_) => checkedAttempt N j.val

/-- The outer-product operator of the encoded uniform index state with a minus ancilla. -/
noncomputable def bbhtInput (N : ℕ) : Operator (N * 2) :=
  outerProduct (encodeState (WithMinus (Uniform (Fin N))))

/-- The weighted sum of `F` over successful depth-sampler paths, assigning zero to timeout
paths. -/
noncomputable def codeSuccess {m : ℕ} (p : CoinCode (SamplerRecord m))
    (F : Fin m → ℝ) : ℝ :=
  ∑ c : Fin p.paths.length, CoinCode.wordWeight (p.paths.get c).2 *
    match (p.paths.get c).1.1 with
    | .inr _ => 0
    | .inl (j,_,_) => F j

/-- The finite set of encoded-table indices whose native comparison with the current entry
returns `some true`. -/
def nativeMarked {N width : ℕ} (T : EncodedTable N width) (y : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => tableCompare T i y = some true)

/-- The finite gate-code word applying one Hadamard gate to every wire. -/
def hadamardWord (n : ℕ) : List FiniteGateCode :=
  (List.finRange n).map (fun i => .h i.val)

/-- The gate-code word that flips the last wire and then applies Hadamard gates to all `n + 1`
wires. -/
def uniformMinusWord (n : ℕ) : List FiniteGateCode := .x n :: hadamardWord (n + 1)

/-- The all-zero register of length `n + 1` with its last bit set to true. -/
def lastOne (n : ℕ) : Reg (n + 1) := Function.update (ZeroStr (n + 1)) (Fin.last n) true

/-- The equivalence from an `n + 1` bit register to an encoded `2 ^ n` index with Boolean
ancilla. -/
def prepLayout (n : ℕ) : Reg (n + 1) ≃ Fin (2 ^ n * 2) :=
  ((regSuccEquiv n).trans (Equiv.prodCongr (bitVecEquiv n) (Equiv.refl Bool))).trans
    (indexBitEquiv (2 ^ n))

/-- The preparation circuit obtained by relabeling `uniformMinusWord n` along `prepLayout n`. -/
noncomputable def prepPowCircuit (n : ℕ) : Circuit (Fin (2 ^ n * 2)) :=
  relabelCircuit (prepLayout n) (finiteCodeCircuit (n + 1) (uniformMinusWord n))

/-- A checked attempt on `2 ^ n` indices preceded by the explicit state-preparation circuit. -/
noncomputable def preparedAttempt (n j : ℕ) : ObservedCircuit (Fin (2 ^ n * 2)) :=
  prependCircuit (prepPowCircuit n) (checkedAttempt (2 ^ n) j)

/-- The encoded basis index corresponding to the all-zero register under `prepLayout n`. -/
def prepZero (n : ℕ) : Fin (2 ^ n * 2) := prepLayout n (ZeroStr (n + 1))

/-- The outer-product operator of the zero basis state used as input to explicit preparation. -/
noncomputable def preparedInput (n : ℕ) : Operator (2 ^ n * 2) := outerProduct (Ket (prepZero n))

/-- A capped-feedback BBHT program that runs an explicitly prepared attempt for each
successfully sampled depth and rejects on sampler timeout. -/
noncomputable def preparedBBHTProgram (n m : ℕ) : CappedFeedback (2 ^ n * 2) m where
  first := .halt true
  weights _ _ := 1
  width _ := Nat.clog 2 m
  next _ a := match a.1 with
    | .inr _ => .halt false
    | .inl (j,_,_) => preparedAttempt n j.val

/-- The list of bit-flip gates for the supplied wire list, retaining a wire exactly when its
mask bit is true. -/
def maskWord {n : ℕ} (ws : List (Fin n)) (mask : Reg n) : List FiniteGateCode :=
  ws.flatMap (fun w => if mask w then [.x w.val] else [])

/-- The register obtained by negating the bit at one wire. -/
def flipAt {n : ℕ} (x : Reg n) (w : Fin n) : Reg n := Function.update x w (!(x w))

/-- The register obtained by traversing the supplied wire list and flipping each listed bit
whose mask is true. -/
def flipRegister {n : ℕ} : List (Fin n) → Reg n → Reg n → Reg n
  | [], _, x => x
  | w :: ws, mask, x => flipRegister ws mask (if mask w then flipAt x w else x)

/-- The bit-flip word containing every wire at which the supplied register is true. -/
def basisResetWord (n : ℕ) (mask : Reg n) : List FiniteGateCode := maskWord (List.finRange n) mask

/-- The relabeled bit-flip circuit determined by the register encoding of a measured basis
index. -/
noncomputable def basisResetCircuit (n : ℕ) (x : Fin (2 ^ n * 2)) : Circuit (Fin (2 ^ n * 2)) :=
  relabelCircuit (prepLayout n) (finiteCodeCircuit (n + 1)
    (basisResetWord (n + 1) ((prepLayout n).symm x)))

/-- An observed program that measures the full basis index, applies its basis-reset circuit, and
accepts. -/
noncomputable def measuredBasisReset (n : ℕ) : ObservedCircuit (Fin (2 ^ n * 2)) :=
  .measure (2 ^ n * 2) id (fun x => prependCircuit (basisResetCircuit n x) (.halt true))

/-- The trace of a full-basis measurement followed by reset, with the original basis amplitude
on `prepZero n` and explicit gate and measurement counts. -/
noncomputable def measuredResetTrace (n : ℕ) (ψ : QState (Fin (2 ^ n * 2)))
    (x : Fin (2 ^ n * 2)) : BranchTrace (Fin (2 ^ n * 2)) :=
  ⟨ψ x • Ket (prepZero n),true,0,(basisResetWord (n + 1) ((prepLayout n).symm x)).length,
    1,[(2 ^ n * 2,x.val)]⟩

/-- The hybrid checked-readout program returning the measured index together with its queried
oracle bit. -/
noncomputable def hybridCheckedReadout (N : ℕ) : HybridProgram (N * 2) (Fin N × Bool) :=
  .measure (N * 2) id (fun x =>
    .step (.gate (resetGate N ((indexBitEquiv N).symm x).2))
      (.step .query (.measure 2 (bitLabel N)
        (fun b => .ret (((indexBitEquiv N).symm x).1,b == 1)))))

/-- The hybrid program that runs the encoded lifted search circuit and returns its checked index
and success bit. -/
noncomputable def hybridCheckedAttempt (N j : ℕ) : HybridProgram (N * 2) (Fin N × Bool) :=
  HybridProgram.prependCircuit (encodeCircuit (LiftCircuit (SearchCircuit (Fin N) j)))
    (hybridCheckedReadout N)

/-- A hybrid checked attempt on `2 ^ n` indices preceded by explicit uniform-minus preparation. -/
noncomputable def hybridPreparedAttempt (n j : ℕ) : HybridProgram (2 ^ n * 2) (Fin (2 ^ n) × Bool) :=
  HybridProgram.prependCircuit (prepPowCircuit n) (hybridCheckedAttempt (2 ^ n) j)

/-- A depth-sampling record containing the search width, optional sampled depth, and read,
comparison, and trial counters. -/
structure DepthDraw where
  width : ℕ
  depth : Option ℕ
  reads : ℕ
  comparisons : ℕ
  trials : ℕ
  deriving DecidableEq, Repr

/-- The depth-sampling record extracted from a sampler result, with no depth on timeout. -/
def depthDraw {m : ℕ} (a : SamplerRecord m) : DepthDraw :=
  match a.1 with
  | .inl (j,b,c) => ⟨m,some j.val,b,c,a.2⟩
  | .inr (b,c) => ⟨m,none,b,c,a.2⟩

/-- The terminal status of a retry sequence: a found index, schedule exhaustion, or
depth-sampler timeout. -/
inductive RetryStatus (N : ℕ) where
  | found : Fin N → RetryStatus N
  | exhausted
  | samplerTimeout
  deriving DecidableEq, Repr

/-- A retry status together with the list of depth-sampling records generated by the run. -/
structure RetryReport (N : ℕ) where
  status : RetryStatus N
  draws : List DepthDraw
  deriving DecidableEq, Repr

/-- The hybrid retry program for a finite list of search widths, using capped depth sampling and
explicit preparation. It stops on success or sampler timeout and resets the measured basis
state before continuing after a failed attempt. -/
noncomputable def hybridRetry (n cap : ℕ) : List ℕ → HybridProgram (2 ^ n * 2) (RetryReport (2 ^ n))
  | [] => .ret ⟨.exhausted,[]⟩
  | m :: ms => HybridProgram.ofCoins (weightedSampler (fun _ : Fin m => 1) (Nat.clog 2 m) cap)
      (fun a => match a.1 with
        | .inr _ => .ret ⟨.samplerTimeout,[depthDraw a]⟩
        | .inl (j,_,_) => (hybridPreparedAttempt n j.val).bind (fun z =>
            if z.2 then .ret ⟨.found z.1,[depthDraw a]⟩
            else HybridProgram.prependCircuit
              (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false)))
              ((hybridRetry n cap ms).bind (fun r => .ret {r with draws := depthDraw a :: r.draws}))))

/-- The encoded Boolean membership oracle for the marked set. -/
noncomputable def retryOracle {n : ℕ} (A : Finset (Fin (2 ^ n))) : Operator (2 ^ n * 2) :=
  encodeGate (BitOracleOn (fun i => decide (i ∈ A)))

/-- The real-valued indicator that a retry report has status `found`. -/
def foundUtility {N : ℕ} (r : RetryReport N) : ℝ := match r.status with
  | .found _ => 1
  | _ => 0

/-- The branch-mass-weighted success value of the hybrid retry program from the zero basis
input. -/
noncomputable def hybridRetrySuccess (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
    (fun r φ => branchMass φ * foundUtility r)

/-- The natural expression `0` for zero numerator and `(a - 1) / b + 1` otherwise, implementing
ceiling division when `b` is positive. -/
def ceilDivNat (a b : ℕ) : ℕ := if a = 0 then 0 else (a - 1) / b + 1

/-- The integer ceiling of the square root, computed as zero at zero and `Nat.sqrt (N - 1) + 1`
otherwise. -/
def ceilSqrtNat (N : ℕ) : ℕ := if N = 0 then 0 else Nat.sqrt (N - 1) + 1

/-- The computable BBHT width: for positive `N`, the smaller of ceiling `(6 / 5) ^ k` and
ceiling `√N`. At `N = 0` it is one at stage zero and zero thereafter. -/
def effectiveBBHTSize (N k : ℕ) : ℕ :=
  if N = 0 then if k = 0 then 1 else 0
  else min (ceilDivNat (6 ^ k) (5 ^ k)) (ceilSqrtNat N)

/-- The list of successive effective BBHT widths beginning at `start` and containing the
specified number of rounds. -/
def effectiveBBHTPrefix (N : ℕ) : ℕ → ℕ → List ℕ
  | _,0 => []
  | start,r + 1 => effectiveBBHTSize N start :: effectiveBBHTPrefix N (start + 1) r

/-- The hybrid retry program using a prefix of the effective BBHT width schedule. -/
noncomputable def growingRetry (n cap start rounds : ℕ) :
    HybridProgram (2 ^ n * 2) (RetryReport (2 ^ n)) :=
  hybridRetry n cap (effectiveBBHTPrefix (2 ^ n) start rounds)

/-- The hybrid success value for a prefix of the growing BBHT retry schedule. -/
noncomputable def growingRetrySuccess (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  hybridRetrySuccess n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A

/-- The expected reset-only statistic after an unsuccessful prepared attempt, assigning zero on
success. -/
noncomputable def hybridResetMoment (n j : ℕ) (A : Finset (Fin (2 ^ n))) (f : HybridCounts → ℝ) : ℝ :=
  (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
    (fun z φ => branchMass φ * (if z.2 then 0 else
      f ⟨0,GateCount (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))),0,0⟩))

/-- The branch-mass-weighted terminal value of a statistic on the hybrid retry operation
counters, starting with zero counters. -/
noncomputable def hybridRetryMoment (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) : ℝ :=
  (hybridRetry n cap sizes).evalCounts (retryOracle A) (Ket (prepZero n)) HybridCounts.zero
    (fun _ φ c => branchMass φ * f c)

/-- One minus the real value of the capped depth sampler's rejection probability raised to
`cap`. -/
noncomputable def depthReturnMass (m cap : ℕ) : ℝ :=
  1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal

/-- The depth sampler's block width multiplied by the finite geometric sum of rejection
probabilities through `cap` trials. -/
noncomputable def depthReadMean (m cap : ℕ) : ℝ :=
  (Nat.clog 2 m : ℝ) * ∑ t ∈ Finset.range cap,
    (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)).toReal ^ t

/-- The average reset-gate moment over depths below `m`, using real division by `m`. -/
noncomputable def meanResetGates (n m : ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (∑ j : Fin m, hybridResetMoment n j.val A (HybridCounts.charge 0 1 0 0)) / m

/-- The real-valued indicator that a retry report has status `exhausted`. -/
def exhaustedUtility {N : ℕ} (r : RetryReport N) : ℝ := match r.status with
  | .exhausted => 1
  | _ => 0

/-- The branch-mass-weighted probability of exhausting the finite retry schedule without success
or sampler timeout. -/
noncomputable def hybridRetryExhaustion (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
    (fun r φ => branchMass φ * exhaustedUtility r)

/-- The product, over the supplied widths, of depth-sampler return mass times checked-search
failure probability. -/
noncomputable def retryReach {N : ℕ} (cap : ℕ) (A : Finset (Fin N)) (sizes : List ℕ) : ℝ :=
  (sizes.map (fun m => depthReturnMass m cap * (1 - CheckedSuccess A m))).prod

open scoped ENNReal

/-- The supremum in the extended nonnegative reals of the charged moments over all finite
growing-schedule prefixes. -/
noncomputable def growingChargeSup (n cap start : ℕ) (A : Finset (Fin (2 ^ n)))
    (q g t r : ℝ) : ℝ≥0∞ :=
  ⨆ (rounds : ℕ), ENNReal.ofReal (hybridRetryMoment n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A
    (HybridCounts.charge q g t r))

/-- The infimum in the extended nonnegative reals of exhaustion probabilities over all finite
growing-schedule prefixes. -/
noncomputable def growingExhaustionInf (n cap start : ℕ) (A : Finset (Fin (2 ^ n))) : ℝ≥0∞ :=
  ⨅ (rounds : ℕ), ENNReal.ofReal (hybridRetryExhaustion n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A)

/-- The real-valued indicator that a retry report has status `samplerTimeout`. -/
def timeoutUtility {N : ℕ} (r : RetryReport N) : ℝ := match r.status with
  | .samplerTimeout => 1
  | _ => 0

/-- The branch-mass-weighted probability that the hybrid retry program terminates with a
depth-sampler timeout. -/
noncomputable def hybridRetryTimeout (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
    (fun r φ => branchMass φ * timeoutUtility r)

/-- The encoded found index with true ancilla for a successful status, and the zero preparation
basis index for all other statuses. -/
def retryFinalBasis (n : ℕ) : RetryStatus (2 ^ n) → Fin (2 ^ n * 2)
  | .found i => indexBitEquiv (2 ^ n) (i,true)
  | _ => prepZero n

/-- The real value of the infinite geometric read-cost expression: block width divided by one
minus rejection mass. -/
noncomputable def depthReadLimit (m : ℕ) : ℝ :=
  ((Nat.clog 2 m : ℝ≥0∞) / (1 - rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m))).toReal

/-- The product of checked-search failure probabilities over the supplied widths. -/
noncomputable def retryCapLimitExhaustion {N : ℕ} (A : Finset (Fin N)) (sizes : List ℕ) : ℝ :=
  (sizes.map (fun m => 1 - CheckedSuccess A m)).prod

/-- The recursive limiting charge for a finite retry schedule, combining random-bit reads,
queries, gates, measurements, resets, and failure-weighted continuation. -/
noncomputable def retryCapLimitMoment (n : ℕ) (A : Finset (Fin (2 ^ n))) (q g t r : ℝ) : List ℕ → ℝ
  | [] => 0
  | m :: ms => r * depthReadLimit m + (q+g)*((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A +
      (1 - CheckedSuccess A m) * retryCapLimitMoment n A q g t r ms

/-- The branch-mass-weighted mean of a real-valued function of the hybrid retry's terminal
status. -/
noncomputable def hybridRetryStatusMean (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : RetryStatus (2 ^ n) → ℝ) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n)) (fun r φ => branchMass φ * f r.status)

/-- The limiting terminal-status payoff recurrence, averaging over search depths and
Born-distributed indices and continuing on an unmarked index. -/
noncomputable def retryCapLimitStatusMean (n : ℕ) (A : Finset (Fin (2 ^ n)))
    (f : RetryStatus (2 ^ n) → ℝ) : List ℕ → ℝ
  | [] => f .exhausted
  | m :: ms => (∑ j : Fin m, ∑ i : Fin (2 ^ n), BornProb (SearchState A j.val) i *
      (if decide (i ∈ A) then f (.found i) else retryCapLimitStatusMean n A f ms)) / m

namespace UniformTape

/-- The native sampler's tape alphabet, consisting of a blank, a marker, and paired sampled and
threshold bits. -/
abbrev Symbol := Option (Unit ⊕ (Bool × Bool))
/-- The eight control states of the native uniform sampler. -/
abbrev Control := Fin 8

/-- The tape symbol marking the left boundary of the native sampler's data window. -/
def marker : Symbol := some (.inl ())
/-- A native sampler data cell storing a sampled bit and a threshold bit. -/
def cell (b t : Bool) : Symbol := some (.inr (b,t))
/-- The tape-cell encoding of a pair of sampled and threshold bits. -/
def data (p : Bool × Bool) : Symbol := cell p.1 p.2

/-- The read-phase control state associated with a three-state comparison result. -/
def readState (c : Fin 3) : Control := ⟨c.val, by omega⟩
/-- The move-phase control state associated with a three-state comparison result. -/
def moveState (c : Fin 3) : Control := ⟨c.val+3, by omega⟩

/-- The native sampler's read-phase command, drawing a fair bit at a data cell and updating the
threshold comparison. At a blank it initiates rewind after a greater-than result and
otherwise halts; a marker also halts. -/
def readCommand (c : Fin 3) : Symbol → NativeTape.Command Symbol Control
  | some (.inr (_,t)) => .coin (fun b => (moveState (compareUpdate c (b,t)), .write (cell b t)))
  | none => if c = 2 then .det 6 (.move .left) else .halt
  | some (.inl ()) => .halt

/-- The native uniform rejection-sampling tape program, with read, move, rewind, and
invalid-input looping states. -/
def program : NativeTape.Program Symbol Control := fun q a =>
  match q.val with
  | 0 => readCommand 0 a
  | 1 => readCommand 1 a
  | 2 => readCommand 2 a
  | 3 => .det 0 (.move .right)
  | 4 => .det 1 (.move .right)
  | 5 => .det 2 (.move .right)
  | 6 => if a = marker then .det 0 (.move .right) else .det 6 (.move .left)
  | _ => .det 7 (.write a)

/-- The initial native sampler configuration with a left marker, zero sampled bits, and the
supplied threshold bits, selecting the read state or invalid-input state according to
`positive`. -/
def start (threshold : List Bool) (positive : Bool) : Turing.TM0.Cfg Symbol Control :=
  ⟨if positive then 0 else 7,
    Turing.Tape.mk₂ [marker] (threshold.map (cell false))⟩

/-- The list of `b` binary digits obtained by successive tests against powers of two and
remainders, with the most significant digit first. -/
def encode : ℕ → ℕ → List Bool
  | 0, _ => []
  | b+1, v => decide (2^b ≤ v) :: encode b (v % 2^b)

/-- The native sampler input using the `b`-bit encoding of `bound - 1`, entering the read state
exactly when `0 < bound ≤ 2 ^ b`. -/
def input (b bound : ℕ) : Turing.TM0.Cfg Symbol Control :=
  start (encode b (bound-1)) (decide (0 < bound ∧ bound ≤ 2^b))

/-- The sampled bits in the `b` cells successively reached by moving left, using false at a
non-data cell. -/
def leftDigits : ℕ → Turing.Tape Symbol → List Bool
  | 0, _ => []
  | b+1, T =>
    let T' := T.move .left
    (match T'.head with | some (.inr (x,_)) => x | _ => false) :: leftDigits b T'

/-- The binary value obtained by reversing the sampled bits in the `b` cells to the left of the
tape head. -/
def output (b : ℕ) (T : Turing.Tape Symbol) : ℕ := binaryValue (leftDigits b T).reverse

/-- The native uniform sampler run for `2 * b` steps using a supplied `b`-bit random register. -/
def trial (b bound : ℕ) (ω : Reg b) : NativeTape.Result Symbol Control :=
  NativeTape.run program (2*b) (List.ofFn ω) (input b bound)

/-- The optional output value, executed step count, and consumed random-bit count of a native
sampler result, returning an output only on a halted result. -/
def trialObservation (b : ℕ) (r : NativeTape.Result Symbol Control) : Option ℕ × ℕ × ℕ :=
  (if r.stop = .halted then some (output b r.cfg.Tape) else none, r.steps, r.bits.length)

/-- The probability law of native trial observations induced by a uniform block of `b` random
bits. -/
noncomputable def trialLaw (b bound : ℕ) : PMF (Option ℕ × ℕ × ℕ) :=
  ((CoinCode.block b).law).map (fun z => trialObservation b (trial b bound z.1))

/-- The native sampler configuration in the initial read state with the supplied bit-pair cells
and a marker to their left. -/
def loaded (ys : List (Bool × Bool)) : Turing.TM0.Cfg Symbol Control :=
  ⟨readState 0, Turing.Tape.mk₂ [marker] (ys.map (fun p => cell p.1 p.2))⟩

/-- The paired-bit list obtained by replacing sampled bits from the supplied random list while
preserving threshold bits, stopping at the shorter list. -/
def overwrite (ω : List Bool) (ys : List (Bool × Bool)) : List (Bool × Bool) :=
  List.zipWith (fun b p => (b,p.2)) ω ys

/-- The native rejection-cycle step count `3 * b + 2`. -/
def cycleSteps (b : ℕ) : ℕ := 3*b+2

/-- The output and operation-count observation derived from a sampler record, subtracting the
final rewind cost on successful return. -/
def countedObservation {m : ℕ} (b : ℕ) (z : SamplerRecord m) : Option ℕ × ℕ × ℕ :=
  match z.1 with
  | .inl out => (some out.1.val, cycleSteps b*z.2-(b+2), b*z.2)
  | .inr _ => (none, cycleSteps b*z.2, b*z.2)

/-- The observation law of the native sampler run with the supplied step budget. -/
noncomputable def nativeLaw (b m budget : ℕ) : PMF (Option ℕ × ℕ × ℕ) :=
  (NativeTape.law program budget (input b m)).map (trialObservation b)

/-- The native observation law obtained by running for `cycleSteps b * cap` steps on each random
word of the capped weighted sampler. -/
noncomputable def nativeCapLaw (b m cap : ℕ) : PMF (Option ℕ × ℕ × ℕ) :=
  let p := weightedSampler (fun _ : Fin m => 1) b cap
  p.pathLaw.map (fun i => trialObservation b (NativeTape.run program (cycleSteps b*cap)
    (p.paths.get i).2 (input b m)))

/-- The extension of an output-and-count payoff to optional-output observations, assigning zero
when no output is present. -/
def haltedPayoff (F : ℕ × ℕ × ℕ → ℝ≥0∞) (z : Option ℕ × ℕ × ℕ) : ℝ≥0∞ :=
  match z.1 with | none => 0 | some j => F (j,z.2.1,z.2.2)

/-- The predicate that a tape consists of a marker and a window of `b` paired-bit cells, with
the specified cursor position at the marker or within the span representation. -/
inductive Window (b : ℕ) : ℤ → Turing.Tape Symbol → Prop
  | atMarker (ys : List (Bool × Bool)) (hlen : ys.length = b) :
      Window b 0 (Turing.Tape.mk₂ [] (marker::ys.map data))
  | span (xs ys : List (Bool × Bool)) (hlen : xs.length+ys.length = b) :
      Window b ((xs.length : ℤ)+1) (Turing.Tape.mk₂ (xs.map data++[marker]) (ys.map data))

/-- The native sampler workspace invariant: the tape has a valid window and each move-phase
state has a data cell under its head. -/
def Workspace (b : ℕ) (p : ℤ) (cfg : Turing.TM0.Cfg Symbol Control) : Prop :=
  Window b p cfg.Tape ∧ ((3 ≤ cfg.q.val ∧ cfg.q.val ≤ 5) → ∃ v : Bool × Bool, cfg.Tape.head = data v)

/-- The union of the initial marker-and-data cell positions with the cursor positions visited by
the supplied execution trace. -/
def workspaceCells (b : ℕ) (es : List (NativeTape.Tick Symbol Control)) : Finset ℤ :=
  (Finset.range (b+1)).image (fun i : ℕ => (i : ℤ)) ∪ (NativeTape.cursorTrace program 1 es).toFinset

/-- The encoding of native tape symbols into the first six elements of `Fin 8`. -/
def symbolCode : Symbol → Fin 8
  | none => 0
  | some (.inl ()) => 1
  | some (.inr (false,false)) => 2
  | some (.inr (false,true)) => 3
  | some (.inr (true,false)) => 4
  | some (.inr (true,true)) => 5

/-- The three-bit register encoding of a native sampler tape symbol. -/
def symbolBits (a : Symbol) : Reg 3 := (bitVecEquiv 3).symm (symbolCode a)

/-- The supremum of the number of workspace cells over all finite step budgets and random-bit
lists for the native sampler input. -/
noncomputable def peakWorkspaceCells (b m : ℕ) : ℝ≥0∞ :=
  ⨆ n, ⨆ raw : List Bool, ((workspaceCells b (NativeTape.run program n raw (input b m)).trace).card : ℝ≥0∞)

end UniformTape

end Qatlib.Concepts.AmplitudeSearch.Amplification
