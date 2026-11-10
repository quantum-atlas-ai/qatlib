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

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + binaryValue bs

def compareUpdate (q : Fin 3) (ab : Bool × Bool) : Fin 3 :=
  if q = 0 then
    if ab.1 = ab.2 then 0 else if ab.1 then 2 else 1
  else q

def compareMachine : Turing.TM0.Machine (Option (Bool × Bool)) (Fin 3)
  | _, none => none
  | q, some ab => some (compareUpdate q ab, .move .right)

def compareAccept (q : Fin 3) : Bool := q == 1

def lexLess : List (Bool × Bool) → Bool
  | [] => false
  | (a,b) :: xs => if a = b then lexLess xs else !a

def registerPairs {n : ℕ} (x y : Reg n) : List (Bool × Bool) :=
  List.ofFn fun i => (x i, y i)

def compareRegisters {n : ℕ} (x y : Reg n) : Option Bool :=
  tapeDecision compareMachine compareAccept ((registerPairs x y).map some) n

abbrev EncodedTable (N width : ℕ) := Fin N → Reg width

def tableValue {N width : ℕ} (T : EncodedTable N width) (i : Fin N) : ℕ :=
  binaryValue (List.ofFn (T i))

def tableCompare {N width : ℕ} (T : EncodedTable N width) (i j : Fin N) : Option Bool :=
  compareRegisters (T i) (T j)

def initialIndexCode (N cap : ℕ) :=
  weightedSampler (fun _ : Fin N => 1) (Nat.clog 2 N) cap
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib

def indexBitEquiv (N : ℕ) : Fin N × Bool ≃ Fin (N * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin N)) boolEquivFin2).trans finProdFinEquiv

noncomputable def encodeState {N : ℕ} (ψ : QState (Fin N × Bool)) : QState (Fin (N * 2)) :=
  ψ ∘ (indexBitEquiv N).symm

noncomputable def encodeGate {N : ℕ} (U : Matrix (Fin N × Bool) (Fin N × Bool) ℂ) :
    Operator (N * 2) := Matrix.reindex (indexBitEquiv N) (indexBitEquiv N) U

noncomputable def encodeStep {N : ℕ} : Step (Fin N × Bool) → Step (Fin (N * 2))
  | .gate U => .gate (encodeGate U)
  | .query => .query

noncomputable def encodeCircuit {N : ℕ} (C : Circuit (Fin N × Bool)) : Circuit (Fin (N * 2)) :=
  C.map encodeStep

def resetFlip (N : ℕ) (b : Bool) (x : Fin (N * 2)) : Fin (N * 2) :=
  indexBitEquiv N (((indexBitEquiv N).symm x).1, ((indexBitEquiv N).symm x).2 ^^ b)

noncomputable def resetGate (N : ℕ) (b : Bool) : Operator (N * 2) := permMatrix (resetFlip N b)

def bitLabel (N : ℕ) (x : Fin (N * 2)) : Fin 2 :=
  boolEquivFin2 ((indexBitEquiv N).symm x).2

noncomputable def checkedReadout (N : ℕ) : ObservedCircuit (Fin (N * 2)) :=
  .measure (N * 2) id fun x =>
    .step (.gate (resetGate N ((indexBitEquiv N).symm x).2))
      (.step .query (.measure 2 (bitLabel N) (fun b => .halt (b == 1))))

noncomputable def checkedLeafState {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) (b : Fin 2) : QState (Fin (N * 2)) :=
  if boolEquivFin2 (f ((indexBitEquiv N).symm x).1) = b then
    ψ x • Ket (indexBitEquiv N (((indexBitEquiv N).symm x).1, f ((indexBitEquiv N).symm x).1))
  else 0

noncomputable def checkedTrace {N : ℕ} (f : Fin N → Bool)
    (ψ : QState (Fin (N * 2))) (x : Fin (N * 2)) (b : Fin 2) : BranchTrace (Fin (N * 2)) :=
  ⟨checkedLeafState f ψ x b, b == 1, 1, 1, 2, [(N * 2, x.val), (2, b.val)]⟩

noncomputable def prependCircuit {D : ℕ} : Circuit (Fin D) → ObservedCircuit (Fin D) → ObservedCircuit (Fin D)
  | [], P => P
  | s :: C, P => .step s (prependCircuit C P)

def addCircuitCounts {D : ℕ} (C : Circuit (Fin D)) (t : BranchTrace (Fin D)) : BranchTrace (Fin D) :=
  {t with queries := t.queries + QueryCount C, gates := t.gates + GateCount C}

noncomputable def checkedAttempt (N j : ℕ) : ObservedCircuit (Fin (N * 2)) :=
  prependCircuit (encodeCircuit (LiftCircuit (SearchCircuit (Fin N) j))) (checkedReadout N)

noncomputable def attemptTrace {N : ℕ} (A : Finset (Fin N)) (j : ℕ)
    (x : Fin (N * 2)) (b : Fin 2) : BranchTrace (Fin (N * 2)) :=
  addCircuitCounts (encodeCircuit (LiftCircuit (SearchCircuit (Fin N) j)))
    (checkedTrace (fun i => decide (i ∈ A)) (encodeState (CheckedSearchState A j)) x b)

noncomputable def bbhtProgram (N m : ℕ) : CappedFeedback (N * 2) m where
  first := .halt true
  weights _ _ := 1
  width _ := Nat.clog 2 m
  next _ a := match a.1 with
    | .inr _ => .halt false
    | .inl (j,_,_) => checkedAttempt N j.val

noncomputable def bbhtInput (N : ℕ) : Operator (N * 2) :=
  outerProduct (encodeState (WithMinus (Uniform (Fin N))))

noncomputable def codeSuccess {m : ℕ} (p : CoinCode (SamplerRecord m))
    (F : Fin m → ℝ) : ℝ :=
  ∑ c : Fin p.paths.length, CoinCode.wordWeight (p.paths.get c).2 *
    match (p.paths.get c).1.1 with
    | .inr _ => 0
    | .inl (j,_,_) => F j

def nativeMarked {N width : ℕ} (T : EncodedTable N width) (y : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => tableCompare T i y = some true)

def hadamardWord (n : ℕ) : List FiniteGateCode :=
  (List.finRange n).map (fun i => .h i.val)

def uniformMinusWord (n : ℕ) : List FiniteGateCode := .x n :: hadamardWord (n + 1)

def lastOne (n : ℕ) : Reg (n + 1) := Function.update (ZeroStr (n + 1)) (Fin.last n) true

def prepLayout (n : ℕ) : Reg (n + 1) ≃ Fin (2 ^ n * 2) :=
  ((regSuccEquiv n).trans (Equiv.prodCongr (bitVecEquiv n) (Equiv.refl Bool))).trans
    (indexBitEquiv (2 ^ n))

noncomputable def prepPowCircuit (n : ℕ) : Circuit (Fin (2 ^ n * 2)) :=
  relabelCircuit (prepLayout n) (finiteCodeCircuit (n + 1) (uniformMinusWord n))

noncomputable def preparedAttempt (n j : ℕ) : ObservedCircuit (Fin (2 ^ n * 2)) :=
  prependCircuit (prepPowCircuit n) (checkedAttempt (2 ^ n) j)

def prepZero (n : ℕ) : Fin (2 ^ n * 2) := prepLayout n (ZeroStr (n + 1))

noncomputable def preparedInput (n : ℕ) : Operator (2 ^ n * 2) := outerProduct (Ket (prepZero n))

noncomputable def preparedBBHTProgram (n m : ℕ) : CappedFeedback (2 ^ n * 2) m where
  first := .halt true
  weights _ _ := 1
  width _ := Nat.clog 2 m
  next _ a := match a.1 with
    | .inr _ => .halt false
    | .inl (j,_,_) => preparedAttempt n j.val

def maskWord {n : ℕ} (ws : List (Fin n)) (mask : Reg n) : List FiniteGateCode :=
  ws.flatMap (fun w => if mask w then [.x w.val] else [])

def flipAt {n : ℕ} (x : Reg n) (w : Fin n) : Reg n := Function.update x w (!(x w))

def flipRegister {n : ℕ} : List (Fin n) → Reg n → Reg n → Reg n
  | [], _, x => x
  | w :: ws, mask, x => flipRegister ws mask (if mask w then flipAt x w else x)

def basisResetWord (n : ℕ) (mask : Reg n) : List FiniteGateCode := maskWord (List.finRange n) mask

noncomputable def basisResetCircuit (n : ℕ) (x : Fin (2 ^ n * 2)) : Circuit (Fin (2 ^ n * 2)) :=
  relabelCircuit (prepLayout n) (finiteCodeCircuit (n + 1)
    (basisResetWord (n + 1) ((prepLayout n).symm x)))

noncomputable def measuredBasisReset (n : ℕ) : ObservedCircuit (Fin (2 ^ n * 2)) :=
  .measure (2 ^ n * 2) id (fun x => prependCircuit (basisResetCircuit n x) (.halt true))

noncomputable def measuredResetTrace (n : ℕ) (ψ : QState (Fin (2 ^ n * 2)))
    (x : Fin (2 ^ n * 2)) : BranchTrace (Fin (2 ^ n * 2)) :=
  ⟨ψ x • Ket (prepZero n),true,0,(basisResetWord (n + 1) ((prepLayout n).symm x)).length,
    1,[(2 ^ n * 2,x.val)]⟩

noncomputable def hybridCheckedReadout (N : ℕ) : HybridProgram (N * 2) (Fin N × Bool) :=
  .measure (N * 2) id (fun x =>
    .step (.gate (resetGate N ((indexBitEquiv N).symm x).2))
      (.step .query (.measure 2 (bitLabel N)
        (fun b => .ret (((indexBitEquiv N).symm x).1,b == 1)))))

noncomputable def hybridCheckedAttempt (N j : ℕ) : HybridProgram (N * 2) (Fin N × Bool) :=
  HybridProgram.prependCircuit (encodeCircuit (LiftCircuit (SearchCircuit (Fin N) j)))
    (hybridCheckedReadout N)

noncomputable def hybridPreparedAttempt (n j : ℕ) : HybridProgram (2 ^ n * 2) (Fin (2 ^ n) × Bool) :=
  HybridProgram.prependCircuit (prepPowCircuit n) (hybridCheckedAttempt (2 ^ n) j)

structure DepthDraw where
  width : ℕ
  depth : Option ℕ
  reads : ℕ
  comparisons : ℕ
  trials : ℕ
  deriving DecidableEq, Repr

def depthDraw {m : ℕ} (a : SamplerRecord m) : DepthDraw :=
  match a.1 with
  | .inl (j,b,c) => ⟨m,some j.val,b,c,a.2⟩
  | .inr (b,c) => ⟨m,none,b,c,a.2⟩

inductive RetryStatus (N : ℕ) where
  | found : Fin N → RetryStatus N
  | exhausted
  | samplerTimeout
  deriving DecidableEq, Repr

structure RetryReport (N : ℕ) where
  status : RetryStatus N
  draws : List DepthDraw
  deriving DecidableEq, Repr

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

noncomputable def retryOracle {n : ℕ} (A : Finset (Fin (2 ^ n))) : Operator (2 ^ n * 2) :=
  encodeGate (BitOracleOn (fun i => decide (i ∈ A)))

def foundUtility {N : ℕ} (r : RetryReport N) : ℝ := match r.status with
  | .found _ => 1
  | _ => 0

noncomputable def hybridRetrySuccess (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
    (fun r φ => branchMass φ * foundUtility r)

def ceilDivNat (a b : ℕ) : ℕ := if a = 0 then 0 else (a - 1) / b + 1

def ceilSqrtNat (N : ℕ) : ℕ := if N = 0 then 0 else Nat.sqrt (N - 1) + 1

def effectiveBBHTSize (N k : ℕ) : ℕ :=
  if N = 0 then if k = 0 then 1 else 0
  else min (ceilDivNat (6 ^ k) (5 ^ k)) (ceilSqrtNat N)

def effectiveBBHTPrefix (N : ℕ) : ℕ → ℕ → List ℕ
  | _,0 => []
  | start,r + 1 => effectiveBBHTSize N start :: effectiveBBHTPrefix N (start + 1) r

noncomputable def growingRetry (n cap start rounds : ℕ) :
    HybridProgram (2 ^ n * 2) (RetryReport (2 ^ n)) :=
  hybridRetry n cap (effectiveBBHTPrefix (2 ^ n) start rounds)

noncomputable def growingRetrySuccess (n cap start rounds : ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  hybridRetrySuccess n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A

noncomputable def hybridResetMoment (n j : ℕ) (A : Finset (Fin (2 ^ n))) (f : HybridCounts → ℝ) : ℝ :=
  (hybridPreparedAttempt n j).eval (retryOracle A) (Ket (prepZero n))
    (fun z φ => branchMass φ * (if z.2 then 0 else
      f ⟨0,GateCount (basisResetCircuit n (indexBitEquiv (2 ^ n) (z.1,false))),0,0⟩))

noncomputable def hybridRetryMoment (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : HybridCounts → ℝ) : ℝ :=
  (hybridRetry n cap sizes).evalCounts (retryOracle A) (Ket (prepZero n)) HybridCounts.zero
    (fun _ φ c => branchMass φ * f c)

noncomputable def depthReturnMass (m cap : ℕ) : ℝ :=
  1 - (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m) ^ cap).toReal

noncomputable def depthReadMean (m cap : ℕ) : ℝ :=
  (Nat.clog 2 m : ℝ) * ∑ t ∈ Finset.range cap,
    (rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m)).toReal ^ t

noncomputable def meanResetGates (n m : ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (∑ j : Fin m, hybridResetMoment n j.val A (HybridCounts.charge 0 1 0 0)) / m

def exhaustedUtility {N : ℕ} (r : RetryReport N) : ℝ := match r.status with
  | .exhausted => 1
  | _ => 0

noncomputable def hybridRetryExhaustion (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
    (fun r φ => branchMass φ * exhaustedUtility r)

noncomputable def retryReach {N : ℕ} (cap : ℕ) (A : Finset (Fin N)) (sizes : List ℕ) : ℝ :=
  (sizes.map (fun m => depthReturnMass m cap * (1 - CheckedSuccess A m))).prod

open scoped ENNReal

noncomputable def growingChargeSup (n cap start : ℕ) (A : Finset (Fin (2 ^ n)))
    (q g t r : ℝ) : ℝ≥0∞ :=
  ⨆ (rounds : ℕ), ENNReal.ofReal (hybridRetryMoment n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A
    (HybridCounts.charge q g t r))

noncomputable def growingExhaustionInf (n cap start : ℕ) (A : Finset (Fin (2 ^ n))) : ℝ≥0∞ :=
  ⨅ (rounds : ℕ), ENNReal.ofReal (hybridRetryExhaustion n cap (effectiveBBHTPrefix (2 ^ n) start rounds) A)

def timeoutUtility {N : ℕ} (r : RetryReport N) : ℝ := match r.status with
  | .samplerTimeout => 1
  | _ => 0

noncomputable def hybridRetryTimeout (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n))) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n))
    (fun r φ => branchMass φ * timeoutUtility r)

def retryFinalBasis (n : ℕ) : RetryStatus (2 ^ n) → Fin (2 ^ n * 2)
  | .found i => indexBitEquiv (2 ^ n) (i,true)
  | _ => prepZero n

noncomputable def depthReadLimit (m : ℕ) : ℝ :=
  ((Nat.clog 2 m : ℝ≥0∞) / (1 - rationalRejectMass (fun _ : Fin m => 1) (Nat.clog 2 m))).toReal

noncomputable def retryCapLimitExhaustion {N : ℕ} (A : Finset (Fin N)) (sizes : List ℕ) : ℝ :=
  (sizes.map (fun m => 1 - CheckedSuccess A m)).prod

noncomputable def retryCapLimitMoment (n : ℕ) (A : Finset (Fin (2 ^ n))) (q g t r : ℝ) : List ℕ → ℝ
  | [] => 0
  | m :: ms => r * depthReadLimit m + (q+g)*((m : ℝ)+1)/2 + g*(n+2) + 2*t + g*meanResetGates n m A +
      (1 - CheckedSuccess A m) * retryCapLimitMoment n A q g t r ms

noncomputable def hybridRetryStatusMean (n cap : ℕ) (sizes : List ℕ) (A : Finset (Fin (2 ^ n)))
    (f : RetryStatus (2 ^ n) → ℝ) : ℝ :=
  (hybridRetry n cap sizes).eval (retryOracle A) (Ket (prepZero n)) (fun r φ => branchMass φ * f r.status)

noncomputable def retryCapLimitStatusMean (n : ℕ) (A : Finset (Fin (2 ^ n)))
    (f : RetryStatus (2 ^ n) → ℝ) : List ℕ → ℝ
  | [] => f .exhausted
  | m :: ms => (∑ j : Fin m, ∑ i : Fin (2 ^ n), BornProb (SearchState A j.val) i *
      (if decide (i ∈ A) then f (.found i) else retryCapLimitStatusMean n A f ms)) / m

namespace UniformTape

abbrev Symbol := Option (Unit ⊕ (Bool × Bool))
abbrev Control := Fin 8

def marker : Symbol := some (.inl ())
def cell (b t : Bool) : Symbol := some (.inr (b,t))
def data (p : Bool × Bool) : Symbol := cell p.1 p.2

def readState (c : Fin 3) : Control := ⟨c.val, by omega⟩
def moveState (c : Fin 3) : Control := ⟨c.val+3, by omega⟩

def readCommand (c : Fin 3) : Symbol → NativeTape.Command Symbol Control
  | some (.inr (_,t)) => .coin (fun b => (moveState (compareUpdate c (b,t)), .write (cell b t)))
  | none => if c = 2 then .det 6 (.move .left) else .halt
  | some (.inl ()) => .halt

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

def start (threshold : List Bool) (positive : Bool) : Turing.TM0.Cfg Symbol Control :=
  ⟨if positive then 0 else 7,
    Turing.Tape.mk₂ [marker] (threshold.map (cell false))⟩

def encode : ℕ → ℕ → List Bool
  | 0, _ => []
  | b+1, v => decide (2^b ≤ v) :: encode b (v % 2^b)

def input (b bound : ℕ) : Turing.TM0.Cfg Symbol Control :=
  start (encode b (bound-1)) (decide (0 < bound ∧ bound ≤ 2^b))

def leftDigits : ℕ → Turing.Tape Symbol → List Bool
  | 0, _ => []
  | b+1, T =>
    let T' := T.move .left
    (match T'.head with | some (.inr (x,_)) => x | _ => false) :: leftDigits b T'

def output (b : ℕ) (T : Turing.Tape Symbol) : ℕ := binaryValue (leftDigits b T).reverse

def trial (b bound : ℕ) (ω : Reg b) : NativeTape.Result Symbol Control :=
  NativeTape.run program (2*b) (List.ofFn ω) (input b bound)

def trialObservation (b : ℕ) (r : NativeTape.Result Symbol Control) : Option ℕ × ℕ × ℕ :=
  (if r.stop = .halted then some (output b r.cfg.Tape) else none, r.steps, r.bits.length)

noncomputable def trialLaw (b bound : ℕ) : PMF (Option ℕ × ℕ × ℕ) :=
  ((CoinCode.block b).law).map (fun z => trialObservation b (trial b bound z.1))

def loaded (ys : List (Bool × Bool)) : Turing.TM0.Cfg Symbol Control :=
  ⟨readState 0, Turing.Tape.mk₂ [marker] (ys.map (fun p => cell p.1 p.2))⟩

def overwrite (ω : List Bool) (ys : List (Bool × Bool)) : List (Bool × Bool) :=
  List.zipWith (fun b p => (b,p.2)) ω ys

def cycleSteps (b : ℕ) : ℕ := 3*b+2

def countedObservation {m : ℕ} (b : ℕ) (z : SamplerRecord m) : Option ℕ × ℕ × ℕ :=
  match z.1 with
  | .inl out => (some out.1.val, cycleSteps b*z.2-(b+2), b*z.2)
  | .inr _ => (none, cycleSteps b*z.2, b*z.2)

noncomputable def nativeLaw (b m budget : ℕ) : PMF (Option ℕ × ℕ × ℕ) :=
  (NativeTape.law program budget (input b m)).map (trialObservation b)

noncomputable def nativeCapLaw (b m cap : ℕ) : PMF (Option ℕ × ℕ × ℕ) :=
  let p := weightedSampler (fun _ : Fin m => 1) b cap
  p.pathLaw.map (fun i => trialObservation b (NativeTape.run program (cycleSteps b*cap)
    (p.paths.get i).2 (input b m)))

def haltedPayoff (F : ℕ × ℕ × ℕ → ℝ≥0∞) (z : Option ℕ × ℕ × ℕ) : ℝ≥0∞ :=
  match z.1 with | none => 0 | some j => F (j,z.2.1,z.2.2)

inductive Window (b : ℕ) : ℤ → Turing.Tape Symbol → Prop
  | atMarker (ys : List (Bool × Bool)) (hlen : ys.length = b) :
      Window b 0 (Turing.Tape.mk₂ [] (marker::ys.map data))
  | span (xs ys : List (Bool × Bool)) (hlen : xs.length+ys.length = b) :
      Window b ((xs.length : ℤ)+1) (Turing.Tape.mk₂ (xs.map data++[marker]) (ys.map data))

def Workspace (b : ℕ) (p : ℤ) (cfg : Turing.TM0.Cfg Symbol Control) : Prop :=
  Window b p cfg.Tape ∧ ((3 ≤ cfg.q.val ∧ cfg.q.val ≤ 5) → ∃ v : Bool × Bool, cfg.Tape.head = data v)

def workspaceCells (b : ℕ) (es : List (NativeTape.Tick Symbol Control)) : Finset ℤ :=
  (Finset.range (b+1)).image (fun i : ℕ => (i : ℤ)) ∪ (NativeTape.cursorTrace program 1 es).toFinset

def symbolCode : Symbol → Fin 8
  | none => 0
  | some (.inl ()) => 1
  | some (.inr (false,false)) => 2
  | some (.inr (false,true)) => 3
  | some (.inr (true,false)) => 4
  | some (.inr (true,true)) => 5

def symbolBits (a : Symbol) : Reg 3 := (bitVecEquiv 3).symm (symbolCode a)

noncomputable def peakWorkspaceCells (b m : ℕ) : ℝ≥0∞ :=
  ⨆ n, ⨆ raw : List Bool, ((workspaceCells b (NativeTape.run program n raw (input b m)).trace).card : ℝ≥0∞)

end UniformTape

end Qatlib.Concepts.AmplitudeSearch.Amplification
