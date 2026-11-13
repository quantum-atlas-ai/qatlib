/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkCorrectedContracts
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts
import Qatlib.Concepts.WalkSearch.Primitives.ScopedSearchInterface
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.StoredSubgraphVocabulary
import Qatlib.Concepts.WalkSearch.QuantumAccess.SafeGroverNative
import Qatlib.Concepts.WalkSearch.QuantumAccess.NoisySearchNative
import Qatlib.Concepts.WalkSearch.WalkAlgorithms.Th5NumericPolylogQuan
import Qatlib.Concepts.WalkSearch.CollisionSearch.RealExponentTransportQuan
import Qatlib.Concepts.WalkSearch.Primitives.DLoNonvacuityQuan
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Finite-resource specifications for triangle search

This module defines binary-tape emission machines, finite circuit and graph encodings, and
scoped search interfaces. It formulates native-capability, stored-checker, real-exponent,
finite-resource, and small-branch specifications for triangle and subgraph search.

The circuit vocabulary follows the finite-register model described in [NielsenChuang2010]; each
specification records the explicit operational or numerical conditions required here.

## Main statements

* `UniformlyEmits`: polynomially bounded emission of an output tape.
* `NativeCapabilitiesSpec` and `StoredCheckerNativeSpec`: search and stored-checker
  requirements.
* `TriangleFiniteResourceSpec`: a uniform finite-circuit resource and acceptance specification.
* `triangleScan`: exhaustive finite triangle scanning.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib
namespace Qatlib.Concepts.WalkSearch.Primitives

/-- A binary-tape instruction specifying the written bit, movement direction, and next state. -/
structure EmitAction where
  write : Bool
  moveRight : Bool
  nextState : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A finite instruction table with a positive initial state and bounds ensuring table entries
exist for the initial and specified next states. -/
structure EmitMachine where
  table : List EmitAction
  initialState : ℕ
  positiveInitial : 0 < initialState
  boundedInitial : 2*initialState+1 < table.length
  boundedStates : ∀ a ∈ table, 2*a.nextState+1 < table.length

/-- A tape-machine configuration recording the control state, head position, left and right tape
contents, and current bit. -/
structure EmitConfig where
  state : ℕ
  position : ℤ
  left : List Bool
  head : Bool
  right : List Bool
  deriving DecidableEq, Repr

/-- The initial configuration with the head at position zero, the machine's initial state, and
the input tape padded by false bits. -/
def emitInitial (A : EmitMachine) (input : List Bool) : EmitConfig :=
  ⟨A.initialState, 0, [], input.headD false, input.tail⟩

/-- Executes one indexed tape instruction, leaving state-zero configurations unchanged and
padding unrepresented tape cells by false bits. -/
def emitStep (A : EmitMachine) (q : EmitConfig) : EmitConfig :=
  if q.state = 0 then q else
    let instruction := A.table[2*q.state+(if q.head then 1 else 0)]!
    if instruction.moveRight then
      ⟨instruction.nextState, q.position+1, instruction.write :: q.left,
        q.right.headD false, q.right.tail⟩
    else
      ⟨instruction.nextState, q.position-1, q.left.tail, q.left.headD false,
        instruction.write :: q.right⟩

/-- The configuration obtained by iterating `emitStep` the specified number of times from
`emitInitial`. -/
def emitRun (A : EmitMachine) (input : List Bool) (steps : ℕ) : EmitConfig :=
  (emitStep A)^[steps] (emitInitial A input)

/-- The condition that the run halts at the origin with a blank left tape and the specified
output on the current and right cells. -/
def emitProduces (A : EmitMachine) (input output : List Bool) (steps : ℕ) : Prop :=
  let q := emitRun A input steps
  q.state = 0 ∧ q.position = 0 ∧ (∀ i : ℕ, q.left[i]?.getD false = false) ∧
    q.head = output.headD false ∧
    (∀ i : ℕ, q.right[i]?.getD false = output.tail[i]?.getD false)

/-- The little-endian binary digits of `t` in a list of length `Nat.clog 2 (t + 1)`. -/
def natTape (t : ℕ) : List Bool :=
  List.ofFn fun i : Fin (Nat.clog 2 (t+1)) => decide (t / 2^i.val % 2 = 1)

/-- Encodes `t` by a unary prefix for its binary width, a false separator, and the digits
`natTape t`. -/
def natBits (t : ℕ) : List Bool :=
  List.replicate (Nat.clog 2 (t+1)) true ++ [false] ++ natTape t

/-- Reads a unary-width prefix and that many little-endian payload bits, returning the decoded
natural and remaining tape when a separator exists. -/
def bitsHead (l : List Bool) : Option (ℕ × List Bool) :=
  let w := (l.takeWhile (fun b => b = true)).length
  if w < l.length then
    let rest := l.drop (w+1)
    some (((List.range w).foldl
      (fun acc i => if rest.getD i false then acc+2^i else acc) 0, rest.drop w))
  else none

/-- The condition that an emission machine produces `emit input` for every input within `c *
input.length ^ d + c` steps. -/
def UniformlyEmits (E : EmitMachine) (c d : ℕ) (emit : List Bool → List Bool) : Prop :=
  ∀ input : List Bool, ∃ steps : ℕ,
    steps ≤ c*input.length^d+c ∧ emitProduces E input (emit input) steps

/-- A family of scoped noisy-search procedures with finite nonempty seed spaces and soundness,
rejection, failure-count, and cost guarantees. -/
structure ScopedNoisyFamily where
  cExp : ℕ
  κ : ℕ
  seed : SearchCallScope → Type
  seedFin : ∀ scope, Fintype (seed scope)
  seedNe : ∀ scope, Nonempty (seed scope)
  run : (scope : SearchCallScope) → {N : ℕ} → (marked test : Fin N → Bool) →
    (tcost floor : ℕ) → scope.contains N tcost floor → seed scope → Option (Fin N)
  cost : (scope : SearchCallScope) → {N : ℕ} → (marked test : Fin N → Bool) →
    (tcost floor : ℕ) → scope.contains N tcost floor → seed scope → ℕ
  sound : ∀ scope {N : ℕ} (marked test : Fin N → Bool) (tcost floor : ℕ)
      (h : scope.contains N tcost floor) (ρ : seed scope) {v : Fin N},
    run scope marked test tcost floor h ρ = some v → marked v = true
  reject : ∀ scope {N : ℕ} (marked test : Fin N → Bool) (tcost floor : ℕ)
      (h : scope.contains N tcost floor) (ρ : seed scope),
    (∀ v, marked v = false) → run scope marked test tcost floor h ρ = none
  finds : ∀ scope {N : ℕ} (marked test : Fin N → Bool) (tcost floor : ℕ)
      (h : scope.contains N tcost floor),
    (∃ v, marked v = true) → (∀ v, test v = true → marked v = true) →
    letI := seedFin scope
    (Finset.univ.filter (fun ρ : seed scope =>
        run scope marked test tcost floor h ρ = none)).card*
      (floor+1)^cExp ≤ Fintype.card (seed scope)
  charges : ∀ scope {N : ℕ} (marked test : Fin N → Bool) (tcost floor : ℕ)
      (h : scope.contains N tcost floor) (ρ : seed scope),
    cost scope marked test tcost floor h ρ ≤
      κ*(Nat.log 2 (floor+1)+2)*(tcost+1)*(Nat.sqrt (floor+1)+1)

/-- Upper bounds for the tuple base, arity, subset size, setup cost, update cost, and checking
cost of collision calls. -/
structure CollisionCallScope where
  tupleBase : ℕ
  arityBound : ℕ
  subsetBound : ℕ
  setupBound : ℕ
  updateBound : ℕ
  checkBound : ℕ

/-- The condition that all six collision-call parameters lie within their corresponding scope
bounds. -/
def CollisionCallScope.contains (scope : CollisionCallScope) (n k r s u c : ℕ) : Prop :=
  n ≤ scope.tupleBase ∧ k ≤ scope.arityBound ∧ r ≤ scope.subsetBound ∧
    s ≤ scope.setupBound ∧ u ≤ scope.updateBound ∧ c ≤ scope.checkBound

/-- A family of collision procedures with scope-dependent finite seeds and soundness, rejection,
failure-count, and cost guarantees for supported calls. -/
structure ScopedCollisionFamily where
  cExp : ℕ
  κ : ℕ
  seed : CollisionCallScope → Type
  seedFin : ∀ scope, Fintype (seed scope)
  seedNe : ∀ scope, Nonempty (seed scope)
  run : (scope : CollisionCallScope) → {n k : ℕ} → (r : ℕ) →
    (R : (Fin k → Fin n) → Bool) → (s u c : ℕ) →
    scope.contains n k r s u c → seed scope → Option (Fin k → Fin n)
  cost : (scope : CollisionCallScope) → {n k : ℕ} → (r : ℕ) →
    (R : (Fin k → Fin n) → Bool) → (s u c : ℕ) →
    scope.contains n k r s u c → seed scope → ℕ
  sound : ∀ scope {n k : ℕ} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ)
      (h : scope.contains n k r s u c) (ρ : seed scope) {t : Fin k → Fin n},
    run scope r R s u c h ρ = some t → R t = true
  reject : ∀ scope {n k : ℕ} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ)
      (h : scope.contains n k r s u c) (ρ : seed scope),
    (∀ t, R t = false) → run scope r R s u c h ρ = none
  finds : ∀ scope {n k : ℕ} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ)
      (h : scope.contains n k r s u c),
    (∃ t, R t = true) →
    letI := seedFin scope
    (Finset.univ.filter (fun ρ : seed scope =>
        run scope r R s u c h ρ = none)).card*
      (n+1)^cExp ≤ Fintype.card (seed scope)
  charges : ∀ scope {n k : ℕ} (r : ℕ) (R : (Fin k → Fin n) → Bool) (s u c : ℕ)
      (h : scope.contains n k r s u c) (ρ : seed scope),
    cost scope r R s u c h ρ ≤
      κ*(Nat.log 2 (n+1)+2)*(s+(n/r)^(k/2)*(c+Nat.sqrt r*u))

/-- The least natural `r` for which `N ≤ r ^ k`, for a positive exponent `k`. -/
def leastPowerWindow (N k : ℕ) (hk : 0 < k) : ℕ :=
  Nat.find (p := fun r => N ≤ r ^ k) ⟨N, Nat.le_self_pow hk.ne' N⟩

/-- The existence of positive-parameter scoped search families and polynomially bounded emitters
satisfying the stated parameter, failure-probability, and coherent-amplification
requirements. -/
def NativeCapabilitiesSpec : Prop :=
  ∃ (c d : ℕ) (grover : ScopedGroverFamily) (noisy : ScopedNoisyFamily)
    (collide : ScopedCollisionFamily) (E₁ E₂ E₃ : EmitMachine),
    0 < c ∧ 0 < grover.κ ∧ 0 < grover.cExp ∧ 0 < noisy.κ ∧ 0 < noisy.cExp ∧
    0 < collide.κ ∧ 0 < collide.cExp ∧
    (grover.κ ≤ collide.κ ∧ noisy.κ ≤ collide.κ ∧
      grover.cExp ≤ collide.cExp ∧ noisy.cExp ≤ collide.cExp) ∧
    UniformlyEmits E₁ c d (fun input =>
      match bitsHead input with
      | none => []
      | some (N, rest) =>
        match bitsHead rest with
        | none => []
        | some (floor, rest') =>
          match bitsHead rest' with
          | none => []
          | some (cc, _) =>
            natBits (sourceSearchCap N) ++ natBits (sourceSearchWarmup N) ++
              natBits (sourceSearchTail N floor cc) ++
              natBits grover.κ ++ natBits grover.cExp) ∧
    UniformlyEmits E₂ c d (fun input =>
      match bitsHead input with
      | none => []
      | some (N, rest) =>
        match bitsHead rest with
        | none => []
        | some (floor, rest') =>
          match bitsHead rest' with
          | none => []
          | some (cc, _) =>
            natBits (sourceSearchCap N) ++ natBits (sourceSearchWarmup N) ++
              natBits (sourceSearchTail N floor cc) ++
              natBits noisy.κ ++ natBits noisy.cExp) ∧
    UniformlyEmits E₃ c d (fun input =>
      match bitsHead input with
      | none => []
      | some (m, rest) =>
        match bitsHead rest with
        | none => []
        | some (k, rest') =>
          match bitsHead rest' with
          | none => []
          | some (N, _) =>
            match k with
            | 0 => []
            | k'+1 =>
              natBits (leastPowerWindow N (k'+1) (by omega)) ++
                natBits collide.κ ++ natBits collide.cExp) ∧
    (∀ (scope : SearchCallScope) (N : ℕ) (marked : Fin N → Bool)
        (check floor : ℕ), scope.contains N check floor → (∃ x, marked x = true) →
      letI := grover.seedFin scope
      ((Finset.univ.filter (fun ρ : grover.seed scope =>
          (grover.execution scope).run marked check floor ρ = none)).card : ℝ) /
        Fintype.card (grover.seed scope) ≤
        ((max N floor+1 : ℕ) : ℝ)^(-(grover.cExp : ℝ))) ∧
    (∀ (scope : SearchCallScope) (N : ℕ) (marked test : Fin N → Bool)
        (tcost floor : ℕ), scope.contains N tcost floor →
      ∃ (body : List (AdjointStep (Fin N))) (k : ℕ) (O : Matrix (Fin N) (Fin N) ℂ)
        (j : Fin N) (accept : Finset (Fin N)) (θ : ℝ),
        O ∈ Matrix.unitaryGroup (Fin N) ℂ ∧ WellFormedAdjointCircuit body ∧
        0 < adjointQueryCount body ∧
        tcost = (2*k+1)*adjointQueryCount body ∧
        (∀ v ∈ accept, marked v = true) ∧ 0 < θ ∧ θ < Real.pi/2 ∧
        MeasureProb (preparedAAState O j) accept = (Real.sin θ)^2 ∧
        MeasureProb (ApplyGate (evaluate O (coherentTestAmplifier body j accept k))
          (Ket j)) accept = (Real.sin ((2*(k : ℝ)+1)*θ))^2)

/-- The specification of one-query stored setup and update words, exact replay identities, and a
fresh-validation checker charge bound for symmetric loopless adjacency. -/
def StoredCheckerNativeSpec : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
    (∀ a b : Fin n, adj a b = adj b a) → (∀ a : Fin n, adj a a = false) →
    ∀ (U : Finset (Fin n)),
      (∃ (setupWord updateWord : Circuit ((Fin n × Fin n) × Bool)),
        IsUnitaryCircuit setupWord ∧ QueryCount setupWord = 1 ∧
        IsUnitaryCircuit updateWord ∧ QueryCount updateWord = 1 ∧
        (∀ p ∈ storedSetupQueries U,
          Run (BitOracleOn (fun q => adj q.1 q.2)) setupWord (Ket (p, false)) =
            Ket (p, adj p.1 p.2)) ∧
        (∀ (v : Fin n), ∀ p ∈ storedUpdateQueries U v,
          Run (BitOracleOn (fun q => adj q.1 q.2)) updateWord (Ket (p, false)) =
            Ket (p, adj p.1 p.2))) ∧
      storedReplay (storedQueryAnswers adj (storedSetupQueries U)) =
        storedEdges adj U ∧
      (∀ v : Fin n, storedReplayInsert (storedEdges adj U)
        (storedQueryAnswers adj (storedUpdateQueries U v)) =
        storedEdges adj (insert v U)) ∧
      ∀ (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ),
        1 ≤ kcs.κ → 1 ≤ ncs.κ →
        ∀ (stape : ℕ → kcs.seed) (ntape : ncs.seed),
          (triCheckFresh adj U kcs ncs r' c₀ stape ntape).2 ≤
            2*cCOf kcs ncs n U.card r' c₀

/-- Tests whether an injective edge-preserving embedding sends `hv` to `v` and sends every other
pattern vertex to a value occurring in `K`. -/
def hWitnessComplete {n k : ℕ} (adj : Fin n → Fin n → Bool) (H : OGraph k) (hv : Fin k)
    (K : Fin (k-1) → Fin n) (v : Fin n) : Bool :=
  decide (∃ σ : Fin k → Fin n,
    (∀ i j : Fin k, i ≠ j → σ i ≠ σ j) ∧
    σ hv = v ∧
    (∀ i : Fin k, i ≠ hv → ∃ j : Fin (k-1), σ i = K j) ∧
    (∀ a b : Fin k, (a, b) ∈ H.edges → adj (σ a) (σ b) = true))

/-- The real-exponent transport and subgraph-search charge specification, requiring least-power
windows and sound checker traces with the stated resource bounds. -/
def RealExponentTh5Spec : Prop :=
  RealExponentTransport ∧
  ∀ (kcs : KCollisionSolver), 1 ≤ kcs.κ → ∃ (C : ℝ), 0 < C ∧
    ∀ (k : ℕ), 4 ≤ k → ∀ (n : ℕ), 0 < n →
      ∀ (H : OGraph k) (hv : Fin k) (adj : Fin n → Fin n → Bool),
        ∃ (r qH : ℕ)
          (checkLaw : (Fin (k-1) → Fin n) → PMF (CappedSearchTrace (Fin n))),
          1 ≤ r ∧ n^(k-1) ≤ r^k ∧ (r-1)^k < n^(k-1) ∧
          (∀ (K : Fin (k-1) → Fin n),
            ∀ tr ∈ (checkLaw K).support,
              (∀ w : Fin n, tr.result = some w → hWitnessComplete adj H hv K w = true) ∧
              tr.phaseQueries+tr.validationQueries ≤ qH) ∧
          ((qH : ℝ) ≤
            (n : ℝ)^((1 : ℝ)/2)*((r : ℝ)^((k : ℝ)/((k : ℝ)+1)))+1) ∧
          ∀ (stape : ℕ → kcs.seed),
            ((hAlg adj H hv kcs r qH stape).2 : ℝ) ≤
              C*((Nat.log 2 n+2 : ℕ) : ℝ)^3*((n : ℝ)^((2 : ℝ)-2/(k : ℝ)))

/-- The binary encoding of a finite gate code using a constructor tag followed by encoded wire
indices. -/
def gateTape : FiniteGateCode → List Bool
  | .h w => [false, false] ++ natBits w
  | .x w => [false, true] ++ natBits w
  | .t w => [true, false] ++ natBits w
  | .tdg w => [true, true, false] ++ natBits w
  | .cx a b => [true, true, true] ++ natBits a ++ natBits b

/-- Encodes the register width, word length, and concatenated gate encodings of a finite circuit
word. -/
def wordTape (b : ℕ) (word : List FiniteGateCode) : List Bool :=
  natBits b ++ natBits word.length ++ word.flatMap gateTape

/-- The row-major binary adjacency table with `n * n` entries. -/
def recordTape (n : ℕ) (adj : Fin n → Fin n → Bool) : List Bool :=
  (List.range (n*n)).map fun i =>
    if h : i/n < n ∧ i%n < n then adj ⟨i/n, h.1⟩ ⟨i%n, h.2⟩ else false

/-- The `b`-bit register initialized with the adjacency-table tape followed by false bits. -/
def recordStart (n : ℕ) (adj : Fin n → Fin n → Bool) (b : ℕ) : Reg b :=
  fun i => if i.val < n*n then (recordTape n adj).getD i.val false else false

/-- The probability that output bit `n * n` is true after running the encoded circuit on the
adjacency-record basis state with identity oracle. -/
def recordAcceptEvent (n : ℕ) (adj : Fin n → Fin n → Bool) (b : ℕ) (hb : n*n < b)
    (word : List FiniteGateCode) : ℝ :=
  MeasureProb (Run (1 : Matrix (Reg b) (Reg b) ℂ) (finiteCodeCircuit b word)
    (Ket (recordStart n adj b))) (Finset.univ.filter (fun z => z ⟨n*n, hb⟩))

/-- The existence of a polynomially bounded circuit emitter with the prescribed subset windows,
walk charges, register and gate bounds, and exact triangle-detection acceptance
probabilities. -/
def TriangleFiniteResourceSpec : Prop :=
  ∃ (E : EmitMachine) (c d : ℕ), 0 < c ∧
    ∀ (n : ℕ), 0 < n → ∀ (adj : Fin n → Fin n → Bool),
      (∀ a b : Fin n, adj a b = adj b a) → (∀ a : Fin n, adj a a = false) →
      ∀ (kcs : KCollisionSolver) (ncs : NoisySearch) (sgs : Qatlib.Concepts.WalkSearch.WalkAlgorithms.SafeGrover),
        1 ≤ kcs.κ → 1 ≤ ncs.κ → 1 ≤ sgs.κ →
        ∃ (r r' b : ℕ) (hb : n*n < b) (word : List FiniteGateCode),
          1 ≤ r ∧ n*n*n ≤ r^5 ∧ (r-1)^5 < n*n*n ∧
            1 ≤ r' ∧ r*r ≤ r'^3 ∧ (r'-1)^3 < r*r ∧
          (∀ (stape : ℕ → kcs.seed) (gtape : ℕ → sgs.seed),
            ((th4Alg adj kcs ncs sgs r r' 4 stape gtape).2 : ℝ) ≤
              (2^16 : ℕ)*(walkKappa kcs ncs sgs)^3*((Nat.log 2 n+2 : ℕ)^3)*
                ((n : ℝ)^(13/10 : ℝ))) ∧
          (n*n+1 ≤ b ∧ ((b : ℝ) ≤ (n : ℝ)^2+2^12*((n+2 : ℝ)^2)) ∧
            finiteWordLegal b word ∧
            ((word.length : ℝ) ≤ 2^40*((n+2 : ℝ)^20)) ∧
            (((word.length*(b+1) : ℕ) : ℝ) ≤ 2^52*((n+2 : ℝ)^22))) ∧
          (∃ steps : ℕ,
            steps ≤ c*(n*n+Nat.clog 2 (n+1)+1)^d+c ∧
            emitProduces E (natBits n ++ recordTape n adj) (wordTape b word) steps) ∧
          ((¬∃ t : Fin 2 → Fin n, triRel adj t = true) →
            recordAcceptEvent n adj b hb word = 0) ∧
          ((∃ t : Fin 2 → Fin n, triRel adj t = true) →
            recordAcceptEvent n adj b hb word = 1)

/-- Selects the first distinct triangle triple found by exhaustive finite enumeration and
records the charge `3 * n ^ 3 + 1`. -/
noncomputable def triangleScan {n : ℕ} (adj : Fin n → Fin n → Bool) :
    Option (Fin n × Fin n × Fin n) × ℕ :=
  ((Finset.univ.filter (fun t : Fin n × Fin n × Fin n =>
      decide (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
        adj t.1 t.2.1 ∧ adj t.1 t.2.2 ∧ adj t.2.1 t.2.2))).toList.head?,
    3*n^3+1)

/-- The specification that the finite scan has the stated cubic charge, returns only triangle
witnesses, and returns a result whenever a triangle relation holds in the small branch. -/
def FiniteSmallBranchSpec : Prop :=
  ∀ (δ : ℝ), 0 < δ → δ < 1 →
    ∃ (N₀ : ℕ), ∀ (n : ℕ), 0 < n → (n < N₀ ∨ Nat.floor ((n : ℝ)^(1-δ)/10) = 0) →
      ∀ (adj : Fin n → Fin n → Bool),
        (∀ a b : Fin n, adj a b = adj b a) → (∀ a : Fin n, adj a a = false) →
        ((triangleScan adj).2 ≤ 3*n^3+1) ∧
        (∀ t : Fin n × Fin n × Fin n, (triangleScan adj).1 = some t →
          t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
            adj t.1 t.2.1 = true ∧ adj t.1 t.2.2 = true ∧ adj t.2.1 t.2.2 = true) ∧
        ((∃ t : Fin 2 → Fin n, triRel adj t = true) → (triangleScan adj).1 ≠ none)

end Qatlib.Concepts.WalkSearch.Primitives
