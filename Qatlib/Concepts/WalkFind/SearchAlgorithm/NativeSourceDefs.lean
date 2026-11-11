/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.ElementDistinctnessAlgorithmQuan
import Qatlib.Concepts.WalkFind.UniqueCollision.QueryComplexityQuan
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetInterrogation
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.WalkFind.SearchAlgorithm.FiniteBasisPadding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Order.Field

/-!
# Native search contracts and source models

This module specifies the native quantum walk components and resource bounds used in collision
search following [Ambainis2007ElementDistinctness]. `NativeJohnsonWitness` records loaded-state
semantics and exact query counts, while `RandomQueryAlgorithm` records seeded unitary programs
with explicitly verified collision outputs.

The remaining definitions describe finite source instructions, bit and RAM machines, collision
data structures, recursive Algorithm 3 trees, and analytic contracts. The declarations named
`Contract` are propositions expressing the required implementation or analysis properties.

## Main statements

* `NativeJohnsonDataContract` and `NativeSingleSolutionContract` specify native Johnson walk
  components and single-collision search guarantees.
* `GeneralQueryMemoryContract` and `GeneralOptimizedQueriesContract` specify query and workspace
  bounds for correct randomized search.
* `QRAMImplementationContract` and `EffectiveQRAMImplementationContract` specify finite source
  programs and effective generation requirements.
* `Algorithm3NativeContract` and `Algorithm3SuccessContract` specify valid recursive search
  trees, their resource bounds, and their success guarantees.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open Matrix Qatlib.Concepts.WalkFind.UniqueCollision
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- States that `S` has exactly `k` indices whose input values are all equal. -/
def IsCollision {N M : ℕ} (k : ℕ) (x : Fin N → ZMod M) (S : Finset (Fin N)) : Prop :=
  S.card = k ∧ ∃ v : ZMod M, ∀ i ∈ S, x i = v

/-- States that the input contains a set of exactly `k` indices with a common value. -/
def HasCollision {N M : ℕ} (k : ℕ) (x : Fin N → ZMod M) : Prop :=
  ∃ S : Finset (Fin N), IsCollision k x S

/-- The basis type combining an address-value query register, a Johnson walk state, and a table
of stored input values. -/
abbrev LoadedSpace (N M r : ℕ) :=
  (Fin N × ZMod M) × (JRState N r × (Fin N → ZMod M))

/-- Encodes a Johnson basis state with its distinguished address, a zero query answer, and input
values stored precisely on its subset. -/
def loadedBasis {N M r : ℕ} (x : Fin N → ZMod M) (p : JRState N r) : LoadedSpace N M r :=
  ((p.val.2, 0), (p, fun i => if i ∈ p.val.1 then x i else 0))

/-- Lifts a Johnson walk state into the loaded basis by summing amplitudes over the encodings
given by `loadedBasis`. -/
def loadedState {N M r : ℕ} [NeZero M] (x : Fin N → ZMod M)
    (ψ : QState (JRState N r)) : QState (LoadedSpace N M r) :=
  fun q => ∑ p, if q = loadedBasis x p then ψ p else 0

/-- States that the subset recorded in a loaded basis state contains a `k`-collision in its
stored value table. -/
def storedCollision {N M r : ℕ} (k : ℕ) (q : LoadedSpace N M r) : Prop :=
  ∃ S : Finset (Fin N), S ⊆ q.2.1.val.1 ∧ IsCollision k q.2.2 S

/-- States that the subset of a Johnson basis state contains a `k`-collision of the input. -/
def markedInput {N M r : ℕ} (k : ℕ) (x : Fin N → ZMod M)
    (p : JRState N r) : Prop :=
  ∃ S : Finset (Fin N), S ⊆ p.val.1 ∧ IsCollision k x S

/-- The diagonal phase operator that negates marked Johnson basis states and fixes unmarked
basis states. -/
def inputFlip {N M r : ℕ} [NeZero M] (k : ℕ) (x : Fin N → ZMod M) :
    Matrix (JRState N r) (JRState N r) ℂ :=
  Matrix.diagonal (fun p => if markedInput k x p then -1 else 1)

/-- Packages unitary setup, walk, and marking circuits with loaded-state semantics and exact
query counts `r`, `2`, and `0`, respectively. -/
structure NativeJohnsonWitness (N M r k : ℕ) [NeZero M] where
  init : LoadedSpace N M r
  setup : Circuit (LoadedSpace N M r)
  walk : Circuit (LoadedSpace N M r)
  flip : Circuit (LoadedSpace N M r)
  unitarySetup : IsUnitaryCircuit setup
  unitaryWalk : IsUnitaryCircuit walk
  unitaryFlip : IsUnitaryCircuit flip
  setupQueries : QueryCount setup = r
  walkQueries : QueryCount walk = 2
  flipQueries : QueryCount flip = 0
  setupSemantics : ∀ x : Fin N → ZMod M,
    Run (alphabetOracle x) setup (Qatlib.Foundations.PureStateMath.Ket init) = loadedState x (jwStartBig N r)
  walkSemantics : ∀ (x : Fin N → ZMod M) (ψ : QState (JRState N r)),
    Run (alphabetOracle x) walk (loadedState x ψ) =
      loadedState x (jwWalkBig N r *ᵥ ψ)
  flipSemantics : ∀ (x : Fin N → ZMod M) (ψ : QState (JRState N r)),
    Run (alphabetOracle x) flip (loadedState x ψ) =
      loadedState x (inputFlip k x *ᵥ ψ)

/-- Specifies the existence of a native Johnson witness whenever `k ≤ r < N` and the alphabet
modulus is positive. -/
def NativeJohnsonDataContract : Prop :=
  ∀ (N M r k : ℕ) [NeZero M], 0 < M → k ≤ r → r < N →
    Nonempty (NativeJohnsonWitness N M r k)

/-- Builds the native search circuit from setup followed by `t` repetitions of a marking flip
and `jwT2 k r` walk steps. -/
def nativeAlgorithm2 {N M r k : ℕ} [NeZero M]
    (A : NativeJohnsonWitness N M r k) (t : ℕ) : Circuit (LoadedSpace N M r) :=
  A.setup ++ RepeatCircuit (A.flip ++ RepeatCircuit A.walk (jwT2 k r)) t

/-- Specifies native single-collision search under the stated parameter bounds, with exact query
accounting, a bounded iteration count, and the stated success lower bound. It also requires
zero stored-collision probability when the input has no collision. -/
def NativeSingleSolutionContract : Prop :=
  ∀ (k N M r : ℕ) [NeZero M], 0 < M → 1 ≤ k → k ≤ r → 2*k ≤ r+1 →
    (8*Real.pi^2*(k^3)*(r+1)*(2^(k+4))*(k+1)*k : ℝ) ≤ N-r →
  ∃ (t : ℕ) (A : NativeJohnsonWitness N M r k),
    QueryCount (nativeAlgorithm2 A t) = r + 2*t*jwT2 k r ∧
    (t : ℝ) ≤ 8/(jwEpsArc k r*jwAlpha k N r) ∧
    ∀ x : Fin N → ZMod M,
      (∀ I : Finset (Fin N), IsCollision k x I →
        (∀ J : Finset (Fin N), IsCollision k x J → J = I) →
        jwEpsArc k r^6/1000000 ≤
          MeasureProb (Run (alphabetOracle x) (nativeAlgorithm2 A t) (Qatlib.Foundations.PureStateMath.Ket A.init))
            (Finset.univ.filter (storedCollision k))) ∧
      (¬HasCollision k x →
        MeasureProb (Run (alphabetOracle x) (nativeAlgorithm2 A t) (Qatlib.Foundations.PureStateMath.Ket A.init))
          (Finset.univ.filter (storedCollision k)) = 0)

/-- The basis type combining a query register, `w` workspace bits, an acceptance flag, and `k`
output indices. -/
abbrev OutputSpace (N M k w : ℕ) :=
  (Fin N × ZMod M) × (Reg w × Bool × (Fin k → Fin N))

/-- States that the acceptance flag is true and the `k` output indices are distinct and carry a
common input value. -/
def verifiedOutput {N M k w : ℕ} (x : Fin N → ZMod M)
    (q : OutputSpace N M k w) : Prop :=
  q.2.2.1 = true ∧ Function.Injective q.2.2.2 ∧
    ∃ v : ZMod M, ∀ i, x (q.2.2.2 i) = v

/-- States that the output acceptance flag is true. -/
def yesOutput {N M k w : ℕ} (q : OutputSpace N M k w) : Prop := q.2.2.1 = true

/-- The real-valued query scale `r + N^(k/2) / r^((k-1)/2)` used in the search resource
contracts. -/
def queryScale (k N r : ℕ) : ℝ :=
  r + (N : ℝ)^((k : ℝ)/2)/(r : ℝ)^(((k : ℝ)-1)/2)

/-- The bit-size parameter `1 + clog 2 (N+1) + clog 2 (M+1)` for addressing input indices and
alphabet values. -/
def dataBits (N M : ℕ) : ℕ := 1 + Nat.clog 2 (N+1) + Nat.clog 2 (M+1)

/-- Packages a positive finite seed space, a workspace size, and a unitary query circuit with an
initial basis state for each seed. -/
structure RandomQueryAlgorithm (N M k : ℕ) [NeZero M] where
  seeds : ℕ
  positiveSeeds : 0 < seeds
  workBits : ℕ
  program : Fin seeds → Circuit (OutputSpace N M k workBits)
  start : Fin seeds → OutputSpace N M k workBits
  unitary : ∀ s, IsUnitaryCircuit (program s)

/-- The uniform average over seeds of the probability of observing a verified collision output. -/
def averageSuccess {N M k : ℕ} [NeZero M] (A : RandomQueryAlgorithm N M k)
    (x : Fin N → ZMod M) : ℝ :=
  (∑ s, MeasureProb (Run (alphabetOracle x) (A.program s) (Qatlib.Foundations.PureStateMath.Ket (A.start s)))
    (Finset.univ.filter (verifiedOutput x))) / A.seeds

/-- Requires zero probability of an unverified positive output for every seed and average
success at least `2/3` on collision inputs. On inputs without collisions, every seed must
have zero acceptance probability. -/
def algorithmCorrect {N M k : ℕ} [NeZero M] (A : RandomQueryAlgorithm N M k) : Prop :=
  ∀ x : Fin N → ZMod M,
    (∀ s, MeasureProb (Run (alphabetOracle x) (A.program s) (Qatlib.Foundations.PureStateMath.Ket (A.start s)))
      (Finset.univ.filter (fun q => yesOutput q ∧ ¬verifiedOutput x q)) = 0) ∧
    (HasCollision k x → 2/3 ≤ averageSuccess A x) ∧
    (¬HasCollision k x → ∀ s,
      MeasureProb (Run (alphabetOracle x) (A.program s) (Qatlib.Foundations.PureStateMath.Ket (A.start s)))
        (Finset.univ.filter yesOutput) = 0)

/-- Specifies correct seeded search for each fixed `k ≥ 2`, with per-seed query cost bounded by
a constant times `queryScale` and workspace bounded by a constant times `r * dataBits`. -/
def GeneralQueryMemoryContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ Ck : ℝ, 0 < Ck ∧
  ∀ (N M r : ℕ) [NeZero M], 0 < M → k ≤ r → r ≤ N →
  ∃ A : RandomQueryAlgorithm N M k,
    algorithmCorrect A ∧
    (∀ s, (QueryCount (A.program s) : ℝ) ≤ Ck*queryScale k N r) ∧
    (A.workBits : ℝ) ≤ Ck*r*dataBits N M

/-- Specifies correct seeded search with query cost bounded by a constant times `N^(k/(k+1))`
and workspace bounded by the same scale times `dataBits`, for each fixed `k ≥ 2`. -/
def GeneralOptimizedQueriesContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ Ck : ℝ, 0 < Ck ∧
  ∀ (N M : ℕ) [NeZero M], 0 < N → 0 < M →
  ∃ A : RandomQueryAlgorithm N M k,
    algorithmCorrect A ∧
    (∀ s, (QueryCount (A.program s) : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))) ∧
    (A.workBits : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))*dataBits N M

/-- The fraction of seeds satisfying a predicate, expressed as a real number. -/
def eventProbability {R : ℕ} (P : Fin R → Prop) : ℝ :=
  (Finset.univ.filter P).card / (R : ℝ)

/-- Requires every injective assignment on at most `d` points to occur with probability between
`(1-η)` and `(1+η)` times the uniform permutation probability. -/
def ApproxIndependent {q R : ℕ} (d : ℕ) (η : ℝ)
    (π : Fin R → Equiv.Perm (Fin q)) : Prop :=
  ∀ m : ℕ, m ≤ d → m ≤ q → ∀ i j : Fin m → Fin q,
    Function.Injective i → Function.Injective j →
    (1-η)/(q.descFactorial m : ℝ) ≤
      eventProbability (fun s => ∀ z, π s (i z) = j z) ∧
    eventProbability (fun s => ∀ z, π s (i z) = j z) ≤
      (1+η)/(q.descFactorial m : ℝ)

/-- Filters `T` to indices whose seeded permutation images lie below `ceil ((2*k)/(2*k+1) * q)`. -/
def retained {q R : ℕ} (k : ℕ) (T : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (s : Fin R) : Finset (Fin q) :=
  T.filter (fun i => (π s i).val < Nat.ceil ((2*k : ℝ)/(2*k+1)*q))

/-- States that `S` is a `k`-collision contained in the index set `T`. -/
def CollisionIn {q M : ℕ} (k : ℕ) (x : Fin q → ZMod M) (T : Finset (Fin q))
    (S : Finset (Fin q)) : Prop := S ⊆ T ∧ IsCollision k x S

/-- Specifies that, for sufficiently large parameters and the stated approximate independence,
the probability that retention removes all collisions is at most the unique-collision
probability plus the stated error term. -/
def Algorithm3IsolationContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
  ∀ N q R M : ℕ, N0 ≤ N → 0 < R → 0 < M →
  ∀ (x : Fin q → ZMod M) (T : Finset (Fin q)) (π : Fin R → Equiv.Perm (Fin q)),
    Real.sqrt N ≤ T.card → T.card ≤ N → T.card ≤ q →
    (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*T.card →
    ApproxIndependent (Nat.ceil (2*(k : ℝ)*Real.log N)) (1/(N : ℝ)) π →
    (∃ S, CollisionIn k x T S) →
    eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) ≤
      eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S) +
        ε/(1+(k : ℝ)*Real.log N)

/-- The angle `arccos (1 - 2*j*(N+1-j)/((r+1)*(N-r)))` used to specify Johnson walk eigenvalues. -/
def johnsonPhase (j N r : ℕ) : ℝ :=
  Real.arccos (1-2*(j : ℝ)*(N+1-j)/((r+1)*(N-r)))

/-- Specifies a unitary eigenbasis with distinct eigenvalues for the reduced Johnson walk,
consisting of `1` and the conjugate phase pairs determined by `johnsonPhase`. -/
def JohnsonFullSpectrumContract : Prop :=
  ∀ k N r : ℕ, 1 ≤ k → k ≤ r → k < N-r →
  ∃ (B : Matrix (Fin (2*k+1)) (Fin (2*k+1)) ℂ)
    (eigenvalues : Fin (2*k+1) → ℂ),
    B ∈ Matrix.unitaryGroup (Fin (2*k+1)) ℂ ∧ Function.Injective eigenvalues ∧
    jwWalk k N r * B = B * Matrix.diagonal eigenvalues ∧ eigenvalues ⟨0, by omega⟩ = 1 ∧
    ∀ j : Fin k,
      eigenvalues ⟨2*j.val+1, by omega⟩ = Complex.exp (Complex.I*johnsonPhase (j.val+1) N r) ∧
      eigenvalues ⟨2*j.val+2, by omega⟩ = Complex.exp (-Complex.I*johnsonPhase (j.val+1) N r)

/-- Specifies that, for fixed positive `j`, `johnsonPhase j N r` is asymptotic to `2 * sqrt
(j/r)` when `N` and `r` tend to infinity and `r/N` tends to zero. -/
def JohnsonPhaseAsymptoticContract : Prop :=
  ∀ j : ℕ, 0 < j → ∀ N r : ℕ → ℕ,
    Filter.Tendsto (fun n => (N n : ℝ)) Filter.atTop Filter.atTop →
    Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop Filter.atTop →
    Filter.Tendsto (fun n => (r n : ℝ)/(N n : ℝ)) Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => johnsonPhase j (N n) (r n) /
      (2*Real.sqrt ((j : ℝ)/(r n : ℝ)))) Filter.atTop (nhds 1)

/-- Source instructions consisting of a finite local gate, a QRAM instruction with five
natural-number parameters, or an oracle query. -/
inductive SourceCode where
  | local : FiniteGateCode → SourceCode
  | qram : ℕ → ℕ → ℕ → ℕ → ℕ → SourceCode
  | query : SourceCode
  deriving DecidableEq, Repr

/-- Reads a register bit at a natural-number index, returning false when the index is out of
range. -/
def readBit {b : ℕ} (ψ : Reg b) (i : ℕ) : Bool :=
  if h : i < b then ψ ⟨i,h⟩ else false

/-- Decodes a little-endian block of register bits as a natural number, using `readBit` for each
position. -/
def addressValue {b : ℕ} (ψ : Reg b) (start width : ℕ) : ℕ :=
  ∑ i ∈ Finset.range width, if readBit ψ (start+i) then 2^i else 0

/-- Checks local-gate legality and QRAM register bounds, memory capacity, and disjointness
conditions; oracle queries are always legal. -/
def sourceCodeLegal (b : ℕ) : SourceCode → Bool
  | .local g => finiteCodeLegal b g
  | .query => true
  | .qram a aw t m ml => decide (a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧
      0 < ml ∧ 2^aw ≤ ml ∧ (t < m ∨ m+ml ≤ t) ∧
      (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a))

/-- Forms the QRAM register action using the selected memory position `m + addressValue ψ a aw`,
replacing the target and selected memory positions by each other's zero-padded bit values. -/
def qramAction (b a aw t m : ℕ) (ψ : Reg b) : Reg b :=
  let j := m+addressValue ψ a aw
  fun i => if i.val = t then readBit ψ j
    else if i.val = j then readBit ψ t else ψ i

/-- Assigns a matrix to each source instruction, using local-gate matrices, the QRAM action
matrix, and the identity for the query placeholder. -/
def sourceCodeMatrix (b : ℕ) : SourceCode → Matrix (Reg b) (Reg b) ℂ
  | .local g => finiteCodeMatrix b g
  | .query => 1
  | .qram a aw t m _ => fun y x => if y = qramAction b a aw t m x then 1 else 0

/-- Translates a source word into a query circuit, preserving query instructions and replacing
other instructions by their matrices. -/
def sourceCircuit (b : ℕ) (cs : List SourceCode) : Circuit (Reg b) :=
  cs.map (fun c => match c with | .query => .query | g => .gate (sourceCodeMatrix b g))

/-- Requires every instruction in a source word to pass `sourceCodeLegal` for the given register
width. -/
def sourceWordLegal (b : ℕ) (cs : List SourceCode) : Prop :=
  ∀ c ∈ cs, sourceCodeLegal b c = true

/-- The assigned description-size cost of a source instruction, using logarithmic costs for its
natural-number parameters. -/
def codeBits : SourceCode → ℕ
  | .query => 1
  | .local (.h w) | .local (.x w) | .local (.t w) | .local (.tdg w) => 4+Nat.clog 2 (w+1)
  | .local (.cx c t) => 4+Nat.clog 2 (c+1)+Nat.clog 2 (t+1)
  | .qram a aw t m ml =>
      4+Nat.clog 2 (a+1)+Nat.clog 2 (aw+1)+Nat.clog 2 (t+1)+Nat.clog 2 (m+1)+Nat.clog 2 (ml+1)

/-- The total bit width allocated to the input address, answer, workspace, acceptance flag, and
`k` output addresses. -/
def nativeWidth (N M k w : ℕ) : ℕ :=
  Nat.clog 2 (N+1) + Nat.clog 2 (M+1) + w + 1 + k*Nat.clog 2 (N+1)

/-- Tests whether the `i`th binary digit of the natural number `n` is one. -/
def naturalBit (n i : ℕ) : Bool := decide (n / 2^i % 2 = 1)

/-- Adds the addressed input value modulo `M` into a valid encoded answer register. It fixes
registers with an invalid address or answer and preserves all bits outside the answer block. -/
def sourceValueAction {N M k w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (nativeWidth N M k w)) : Reg (nativeWidth N M k w) :=
  let ab := Nat.clog 2 (N+1)
  let mb := Nat.clog 2 (M+1)
  let address := addressValue ψ 0 ab
  let answer := addressValue ψ ab mb
  if ha : address < N then
    if answer < M then
      let result := (answer + (x ⟨address,ha⟩).val) % M
      fun i => if ab ≤ i.val ∧ i.val < ab+mb then naturalBit result (i.val-ab) else ψ i
    else ψ
  else ψ

/-- The matrix induced by the encoded modular-addition action `sourceValueAction`. -/
def sourceValueOracle {N M k w : ℕ} (x : Fin N → ZMod M) :
    Matrix (Reg (nativeWidth N M k w)) (Reg (nativeWidth N M k w)) ℂ :=
  fun y z => if y = sourceValueAction x z then 1 else 0

/-- States that the acceptance bit in the native bit-register layout is true. -/
def sourceYes {N M k w : ℕ} (ψ : Reg (nativeWidth N M k w)) : Prop :=
  readBit ψ (Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+w) = true

/-- Decodes the `i`th output address from the native bit-register layout. -/
def outputAddress {N M k w : ℕ} (ψ : Reg (nativeWidth N M k w)) (i : Fin k) : ℕ :=
  addressValue ψ (Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+w+1+
    i.val*Nat.clog 2 (N+1)) (Nat.clog 2 (N+1))

/-- States that a native bit register accepts and encodes `k` distinct valid input addresses
with equal input values. -/
def sourceVerified {N M k w : ℕ} (x : Fin N → ZMod M)
    (ψ : Reg (nativeWidth N M k w)) : Prop :=
  sourceYes ψ ∧ ∃ addresses : Fin k → Fin N,
    (∀ i, outputAddress ψ i = (addresses i).val) ∧ Function.Injective addresses ∧
    ∃ v : ZMod M, ∀ i, x (addresses i) = v

/-- Specifies legal unitary source programs with optimized query bounds, bounded register and
description sizes, and average success at least `2/3 - 2^(-precision)`. It also requires
unitary value oracles and zero probability of unverified positive outputs. -/
def QRAMImplementationContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ (Ck : ℝ) (c : ℕ), 0 < Ck ∧
  ∀ (N M precision : ℕ) [NeZero M], 0 < N → 0 < M → 1 ≤ precision →
  ∃ (seedBits w : ℕ) (program : Fin (2^seedBits) → List SourceCode),
    let b := nativeWidth N M k w
    (b : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))*(dataBits N M+precision)^3 ∧
    (seedBits : ℝ) ≤ Ck*(dataBits N M+precision)^c ∧
    (∀ x : Fin N → ZMod M,
      sourceValueOracle (k:=k) (w:=w) x ∈ Matrix.unitaryGroup (Reg b) ℂ) ∧
    (∀ s, sourceWordLegal b (program s) ∧
      IsUnitaryCircuit (sourceCircuit b (program s)) ∧
      (QueryCount (sourceCircuit b (program s)) : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1)) ∧
      ((program s).length : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))*(dataBits N M+precision)^c ∧
      (((program s).map codeBits).sum : ℝ) ≤
        Ck*(N : ℝ)^((k : ℝ)/(k+1))*(dataBits N M+precision)^c) ∧
    (∀ x : Fin N → ZMod M,
      let out := fun s => Run (sourceValueOracle (k:=k) (w:=w) x)
        (sourceCircuit b (program s)) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr b))
      (∀ s, MeasureProb (out s)
        (Finset.univ.filter (fun z => sourceYes z ∧ ¬sourceVerified x z)) = 0) ∧
      (HasCollision k x →
        2/3-(2 : ℝ)^(-(precision : ℤ)) ≤
          (∑ s, MeasureProb (out s) (Finset.univ.filter (sourceVerified x)))/(2^seedBits : ℝ)) ∧
      (¬HasCollision k x → ∀ s,
        MeasureProb (out s) (Finset.univ.filter sourceYes) = 0))

/-- Specifies a hybrid bound on the Euclidean distance between two unitary evolutions that agree
on each ideal prefix state after subtracting its designated bad component. -/
def TruncationHybridContract : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H],
  ∀ (T : ℕ) (U V : Fin T → Matrix H H ℂ) (bad : Fin T → QState H)
    (ψ : QState H),
    (∀ i, U i ∈ Matrix.unitaryGroup H ℂ) →
    (∀ i, V i ∈ Matrix.unitaryGroup H ℂ) →
    (∀ i, let ideal := Run 1 ((List.ofFn U).take i.val |>.map Step.gate) ψ
      U i *ᵥ (ideal-bad i) = V i *ᵥ (ideal-bad i)) →
    ‖toEuclidean_fromVec (Run 1 ((List.ofFn U).map Step.gate) ψ -
      Run 1 ((List.ofFn V).map Step.gate) ψ)‖ ≤
      ∑ i, 2*‖toEuclidean_fromVec (bad i)‖

/-- Specifies exact finite-gate simulation of every legal nonquery source instruction using at
most `2*b` clean auxiliary bits and a uniform cubic word-length bound. -/
def OrdinaryGateQRAMFallbackContract : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (b : ℕ) (g : SourceCode),
    sourceCodeLegal b g = true → g ≠ .query →
    ∃ (a : ℕ) (word : List FiniteGateCode),
      a ≤ 2*b ∧ finiteWordLegal (b+a) word = true ∧
      word.length ≤ C*(b+1)^3 ∧
      ∀ ψ : QState (Reg b),
        Run 1 (finiteCodeCircuit (b+a) word)
          (fun z => TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr a)) ((regAppendEquiv b a) z)) =
        (fun z => TensorState (sourceCodeMatrix b g *ᵥ ψ) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr a))
          ((regAppendEquiv b a) z))

/-- Specifies an amplitude-amplification bound for a marked-state reflection and a real unitary
walk satisfying the stated spectral gap assumptions, including possible eigenvalue `-1`. It
requires a bounded iteration count achieving the stated marked-state overlap. -/
def GroverIncludingMinusOneContract : Prop :=
  ∀ (m : ℕ) (ε α : ℝ), 0 < ε → ε ≤ 1 → 0 < α → α ≤ 1 →
    ∀ (Uf Uw : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ),
      (star Uf * Uf) = 1 →
      (star Uw * Uw) = 1 →
      (∀ i j, (Uw i j).im = 0) →
      (∀ i, (start i).im = 0) →
      (∀ i, (good i).im = 0) →
      (∑ i, ‖start i‖ ^ 2) = 1 →
      (∑ i, ‖good i‖ ^ 2) = 1 →
      (∑ i, star (good i) * start i) = (α : ℂ) →
      Uf *ᵥ good = -good →
      (∀ v : Fin m → ℂ, (∑ i, star (v i) * good i) = 0 → Uf *ᵥ v = v) →
      Uw *ᵥ start = start →
      (∀ (ν : ℂ) (v : Fin m → ℂ), Uw *ᵥ v = ν • v →
          (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
          ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ ν = Complex.exp (Complex.I * θ)) →
      ∃ t : ℕ, (t : ℝ) ≤ 8 / (ε * α) ∧
        ε ^ 3 / 1000 ≤
          ‖∑ i, star (good i) * ((Uw * Uf) ^ t *ᵥ start) i‖

/-- Encodes a natural number by a unary length prefix, a false delimiter, and its little-endian
binary digits. -/
def natDescription (n : ℕ) : List Bool :=
  let width := Nat.clog 2 (n+1)
  List.replicate width true ++ [false] ++ List.ofFn (fun i : Fin width => naturalBit n i.val)

/-- Encodes a finite gate by a natural-number tag followed by descriptions of its wire indices. -/
def gateDescription : FiniteGateCode → List Bool
  | .h w => natDescription 0 ++ natDescription w
  | .x w => natDescription 1 ++ natDescription w
  | .t w => natDescription 2 ++ natDescription w
  | .tdg w => natDescription 3 ++ natDescription w
  | .cx c t => natDescription 4 ++ natDescription c ++ natDescription t

/-- Encodes a source instruction by its constructor tag and the descriptions of its gate or QRAM
parameters. -/
def sourceDescription : SourceCode → List Bool
  | .query => natDescription 0
  | .local g => natDescription 1 ++ gateDescription g
  | .qram a aw t m ml => natDescription 2 ++ natDescription a ++ natDescription aw ++
      natDescription t ++ natDescription m ++ natDescription ml

/-- Encodes a workspace size and a source word by recording the size, word length, and
concatenated instruction descriptions. -/
def wordDescription (w : ℕ) (cs : List SourceCode) : List Bool :=
  natDescription w ++ natDescription cs.length ++ cs.flatMap sourceDescription

/-- A bit-machine instruction recording the bit to write, the direction of head movement, and
the next control state. -/
structure BitAction where
  write : Bool
  moveRight : Bool
  nextState : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A finite bit-machine transition table with a positive initial state and bounds ensuring
table coverage for the initial and transition states. -/
structure BitMachine where
  table : List BitAction
  initialState : ℕ
  positiveInitial : 0 < initialState
  boundedInitial : 2*initialState+1 < table.length
  boundedStates : ∀ a ∈ table, 2*a.nextState+1 < table.length

/-- A bit-machine configuration containing the control state, integer head position, current
bit, and lists of bits to the left and right. -/
structure BitConfiguration where
  state : ℕ
  position : ℤ
  left : List Bool
  head : Bool
  right : List Bool
  deriving DecidableEq, Repr

/-- Initializes a bit machine at position zero with the input at and to the right of the head
and an empty left tape. -/
def bitInitial (A : BitMachine) (input : List Bool) : BitConfiguration :=
  ⟨A.initialState, 0, [], input.headD false, input.tail⟩

/-- Executes one table instruction, writing a bit and moving the head left or right; control
state zero remains fixed. -/
def bitMachineStep (A : BitMachine) (q : BitConfiguration) : BitConfiguration :=
  if q.state = 0 then q else
  let instruction := A.table[2*q.state+(if q.head then 1 else 0)]!
  if instruction.moveRight then
    ⟨instruction.nextState, q.position+1, instruction.write :: q.left, q.right.headD false, q.right.tail⟩
  else
    ⟨instruction.nextState, q.position-1, q.left.tail, q.left.headD false, instruction.write :: q.right⟩

/-- Iterates the bit-machine transition function for a specified number of steps from the
initial input configuration. -/
def bitMachineRun (A : BitMachine) (input : List Bool) (steps : ℕ) : BitConfiguration :=
  (bitMachineStep A)^[steps] (bitInitial A input)

/-- Requires a run to halt at position zero with a blank left tape and the requested output on
the current and right tape cells. -/
def bitMachineProduces (A : BitMachine) (input output : List Bool) (steps : ℕ) : Prop :=
  let q := bitMachineRun A input steps
  q.state = 0 ∧ q.position = 0 ∧ (∀ i : ℕ, q.left[i]?.getD false = false) ∧
    q.head = output.headD false ∧ (∀ i : ℕ, q.right[i]?.getD false = output.tail[i]?.getD false)

/-- Specifies source-program search guarantees together with generation by two fixed bit
machines for each `k`. It bounds seed generation, program generation, query cost, register
width, and the stated description-processing costs. -/
def EffectiveQRAMImplementationContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ (Ck : ℝ) (c : ℕ) (seeds words : BitMachine), 0 < Ck ∧
  ∀ (N M precision : ℕ) [NeZero M], 0 < N → 0 < M → 1 ≤ precision →
  ∃ (seedBits w : ℕ) (program : Fin (2^seedBits) → List SourceCode),
    let b := nativeWidth N M k w
    (b : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1))*(dataBits N M+precision)^3 ∧
    (∃ steps : ℕ,
      bitMachineProduces seeds (natDescription N ++ natDescription M ++ natDescription precision)
        (natDescription seedBits) steps ∧
      (steps+seedBits : ℝ) ≤ Ck*(dataBits N M+precision)^c) ∧
    (∀ s, sourceWordLegal b (program s) ∧
      IsUnitaryCircuit (sourceCircuit b (program s)) ∧
      (QueryCount (sourceCircuit b (program s)) : ℝ) ≤ Ck*(N : ℝ)^((k : ℝ)/(k+1)) ∧
      ∃ steps : ℕ,
        bitMachineProduces words
          (natDescription N ++ natDescription M ++ natDescription precision ++ natDescription s.val)
          (wordDescription w (program s)) steps ∧
        (steps + seedBits + ((program s).map (fun g => (sourceDescription g).length^2)).sum + (program s).length : ℝ) ≤
          Ck*(N : ℝ)^((k : ℝ)/(k+1))*(dataBits N M+precision)^c) ∧
    (∀ x : Fin N → ZMod M,
      sourceValueOracle (k:=k) (w:=w) x ∈ Matrix.unitaryGroup (Reg b) ℂ ∧
      let out := fun s => Run (sourceValueOracle (k:=k) (w:=w) x)
        (sourceCircuit b (program s)) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr b))
      (∀ s, MeasureProb (out s)
        (Finset.univ.filter (fun z => sourceYes z ∧ ¬sourceVerified x z)) = 0) ∧
      (HasCollision k x → 2/3-(2 : ℝ)^(-(precision : ℤ)) ≤
        (∑ s, MeasureProb (out s) (Finset.univ.filter (sourceVerified x)))/(2^seedBits : ℝ)) ∧
      (¬HasCollision k x → ∀ s, MeasureProb (out s) (Finset.univ.filter sourceYes) = 0))

/-- The sum of squared entry norms of a finite complex matrix. -/
def frobeniusSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖^2

/-- Collects unitary invariance of squared Frobenius norm, a matched-eigenvalue perturbation
bound for normal matrices, and the corresponding product bound for unitary matrices. -/
def NormalSpectralPerturbationContract : Prop :=
  (∀ m n : ℕ, ∀ (U : Matrix (Fin m) (Fin m) ℂ) (A : Matrix (Fin m) (Fin n) ℂ),
    U ∈ Matrix.unitaryGroup (Fin m) ℂ → frobeniusSq (U*A) = frobeniusSq A) ∧
  (∀ n : ℕ, ∀ C D : Matrix (Fin n) (Fin n) ℂ,
    Cᴴ*C = C*Cᴴ → Dᴴ*D = D*Dᴴ →
    ∃ (E F : Matrix (Fin n) (Fin n) ℂ) (eigenC eigenD : Fin n → ℂ) (σ : Equiv.Perm (Fin n)),
      E ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ F ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      C*E = E*Matrix.diagonal eigenC ∧ D*F = F*Matrix.diagonal eigenD ∧
      (∑ i, ‖eigenC i-eigenD (σ i)‖^2) ≤ frobeniusSq (C-D)) ∧
  (∀ n : ℕ, ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A ∈ Matrix.unitaryGroup (Fin n) ℂ → B ∈ Matrix.unitaryGroup (Fin n) ℂ →
    ∃ (E F G : Matrix (Fin n) (Fin n) ℂ) (eigenA eigenB eigenAB : Fin n → ℂ)
      (σ : Equiv.Perm (Fin n)),
      E ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ F ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      G ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      A*E = E*Matrix.diagonal eigenA ∧ B*F = F*Matrix.diagonal eigenB ∧
      (A*B)*G = G*Matrix.diagonal eigenAB ∧
      (∑ i, ‖eigenB i-eigenAB (σ i)‖^2) ≤ ∑ i, ‖eigenA i-1‖^2)

/-- Specifies two explicit `2 × 2` matrices whose characteristic polynomials and Frobenius
distance violate the analogous matched-eigenvalue bound without normality. -/
def UnrestrictedPerturbationCounterexampleContract : Prop :=
  let C : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
  let D : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
  C.charpoly = Polynomial.X^2 ∧ D.charpoly = Polynomial.X^2-1 ∧
  frobeniusSq (C-D) = 1 ∧
  ∀ σ : Equiv.Perm (Fin 2),
    frobeniusSq (C-D) < ∑ i : Fin 2, ‖(0 : ℂ)-(if (σ i).val = 0 then 1 else -1)‖^2

/-- Instructions for a bit RAM machine, including halting, address manipulation, memory access,
input consumption, and output writing. -/
inductive RAMAction where
  | halt
  | pushAddress : Bool → ℕ → RAMAction
  | popAddress : ℕ → ℕ → ℕ → RAMAction
  | readMemory : ℕ → ℕ → RAMAction
  | writeMemory : Bool → ℕ → RAMAction
  | readInput : ℕ → ℕ → ℕ → RAMAction
  | writeOutput : Bool → ℕ → RAMAction
  deriving Inhabited

/-- A finite list of RAM instructions together with an initial control state. -/
structure BitRAMMachine where
  table : List RAMAction
  initialState : ℕ

/-- A RAM configuration recording its control state, address bits, Boolean memory, remaining
input, and accumulated output. -/
structure RAMConfiguration where
  state : ℕ
  address : List Bool
  memory : ℕ → Bool
  input : List Bool
  output : List Bool

/-- Decodes a list of address bits in most-significant-bit-first order. -/
def binaryAddress (bits : List Bool) : ℕ :=
  bits.foldl (fun n b => 2*n+(if b then 1 else 0)) 0

/-- Initializes a RAM machine with an empty address and output, the supplied input, and memory
given by the record with false padding. -/
def ramInitial (A : BitRAMMachine) (record input : List Bool) : RAMConfiguration :=
  ⟨A.initialState, [], fun i => record[i]?.getD false, input, []⟩

/-- Executes one RAM instruction, interpreting missing table entries as halting instructions. -/
def ramStep (A : BitRAMMachine) (q : RAMConfiguration) : RAMConfiguration :=
  match A.table[q.state]?.getD .halt with
  | .halt => q
  | .pushAddress b n => { q with state := n, address := q.address ++ [b] }
  | .popAddress z f t => match q.address.getLast? with
      | none => { q with state := z }
      | some b => { q with state := if b then t else f, address := q.address.dropLast }
  | .readMemory f t => { q with state := if q.memory (binaryAddress q.address) then t else f }
  | .writeMemory b n =>
      { q with state := n, memory := Function.update q.memory (binaryAddress q.address) b }
  | .readInput z f t => match q.input with
      | [] => { q with state := z }
      | b :: bs => { q with state := if b then t else f, input := bs }
  | .writeOutput b n => { q with state := n, output := q.output ++ [b] }

/-- Assigns a step cost from the control-table size and, where relevant, the current address or
output length. -/
def ramStepBits (A : BitRAMMachine) (q : RAMConfiguration) : ℕ :=
  match A.table[q.state]?.getD .halt with
  | .pushAddress _ _ | .popAddress _ _ _ | .readMemory _ _ | .writeMemory _ _ =>
      1+q.address.length+Nat.clog 2 (A.table.length+1)
  | .writeOutput _ _ => 1+q.output.length+Nat.clog 2 (A.table.length+1)
  | _ => 1+Nat.clog 2 (A.table.length+1)

/-- Runs a RAM machine for a given number of transitions and accumulates the costs assigned by
`ramStepBits`. -/
def ramRun (A : BitRAMMachine) (q : RAMConfiguration) : ℕ → RAMConfiguration × ℕ
  | 0 => (q, 0)
  | n+1 => let result := ramRun A (ramStep A q) n
           (result.1, ramStepBits A q+result.2)

/-- Requires some RAM run to halt within the supplied cost bound, leave the expected
false-padded memory record, and produce the requested output. -/
def ramProduces (A : BitRAMMachine) (record input expected output : List Bool)
    (clock : ℕ) : Prop :=
  ∃ steps : ℕ,
    let run := ramRun A (ramInitial A record input) steps
    (A.table[run.1.state]?.getD .halt = .halt) ∧ run.2 ≤ clock ∧
      (∀ i, run.1.memory i = expected[i]?.getD false) ∧ run.1.output = output

/-- Packages seeded encodings of indexed input values with empty-record correctness, value
locality, and faithfulness. It also supplies RAM machines for insertion, erasure, and
lookup. -/
structure CollisionDataStructure (N M r : ℕ) where
  seedBits : ℕ
  encode : Finset (Fin N) → (Fin N → ZMod M) → Fin (2^seedBits) → List Bool
  empty : Fin (2^seedBits) → List Bool
  emptyCorrect : ∀ x h, encode ∅ x h = empty h
  valueLocal : ∀ S x y h, (∀ i ∈ S, x i = y i) → encode S x h = encode S y h
  faithful : ∀ S T x y h h', encode S x h = encode T y h' →
    S = T ∧ h = h' ∧ ∀ i ∈ S, x i = y i
  insert : BitRAMMachine
  erase : BitRAMMachine
  lookup : BitRAMMachine

/-- Requires insertion, erasure, and lookup on the given encoded set to produce their specified
records and outputs within the supplied RAM cost bound. -/
def dataOperationsFast {N M r : ℕ} (D : CollisionDataStructure N M r)
    (x : Fin N → ZMod M) (S : Finset (Fin N)) (h : Fin (2^D.seedBits)) (clock : ℕ) : Prop :=
  ∀ i : Fin N,
    (i ∉ S → ramProduces D.insert (D.encode S x h)
      (natDescription i.val ++ natDescription (x i).val)
      (D.encode (insert i S) x h) [] clock) ∧
    (i ∈ S → ramProduces D.erase (D.encode S x h) (natDescription i.val)
      (D.encode (S.erase i) x h) [] clock) ∧
    (i ∈ S → ramProduces D.lookup (D.encode S x h) (natDescription i.val)
      (D.encode S x h) (natDescription (x i).val) clock)

/-- Copies the distinguished Johnson address and the first `w` bits of the seeded data-structure
record into the native register layout, setting all remaining bits to false. -/
def dataBasis {N M r : ℕ} (D : CollisionDataStructure N M r) (k w : ℕ)
    (x : Fin N → ZMod M) (h : Fin (2^D.seedBits)) (p : JRState N r) :
    Reg (nativeWidth N M k w) :=
  let ab := Nat.clog 2 (N+1)
  let mb := Nat.clog 2 (M+1)
  fun i => if i.val < ab then naturalBit p.val.2.val i.val
    else if ab+mb ≤ i.val ∧ i.val < ab+mb+w then
      (D.encode p.val.1 x h)[i.val-(ab+mb)]?.getD false else false

/-- Lifts amplitudes on Johnson states and data-structure seeds into their native bit-register
encodings by summing over matching basis encodings. -/
def dataLift {N M r : ℕ} [NeZero M] (D : CollisionDataStructure N M r) (k w : ℕ)
    (x : Fin N → ZMod M) (ψ : QState (JRState N r × Fin (2^D.seedBits))) :
    QState (Reg (nativeWidth N M k w)) :=
  fun z => ∑ p, if z = dataBasis D k w x p.2 p.1 then ψ p else 0

/-- A search frame with a finite size and an optional original input index for each local
position. -/
structure Algorithm3Frame (N : ℕ) where
  size : ℕ
  origin : Fin size → Option (Fin N)

/-- The full input frame, mapping every local index to the same original index. -/
def initialFrame (N : ℕ) : Algorithm3Frame N := ⟨N, some⟩

/-- Requires each original input index to occur at most once among a frame's nonempty origins. -/
def frameWellFormed {N : ℕ} (f : Algorithm3Frame N) : Prop :=
  ∀ i j v, f.origin i = some v → f.origin j = some v → i = j

/-- The finite set of original input indices represented by a frame. -/
def frameSet {N : ℕ} (f : Algorithm3Frame N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ j, f.origin j = some i)

/-- Builds the local input in an enlarged alphabet, using original values at represented indices
and distinct padding values at empty origins. -/
def frameInput {N M : ℕ} (f : Algorithm3Frame N) (x : Fin N → ZMod M) :
    Fin f.size → ZMod (M+f.size+1) :=
  fun j => match f.origin j with
    | some i => (x i).val
    | none => M+j.val

/-- Packages the near-size even-prime-power permutation domain, approximate independence, and a
strictly smaller retained size used by a recursive search stage. -/
structure Algorithm3Plan (k N : ℕ) (f : Algorithm3Frame N) where
  q : ℕ
  seeds : ℕ
  positiveSeeds : 0 < seeds
  enough : f.size ≤ q
  near : (q : ℝ) ≤ (1+1/(2*(k : ℝ)^2))*f.size
  evenPrimePower : ∃ p a : ℕ, Nat.Prime p ∧ 0 < a ∧ q = p^(2*a)
  permutation : Fin seeds → Equiv.Perm (Fin q)
  independent : ApproxIndependent (Nat.ceil (2*(k : ℝ)*Real.log N))
    (1/(N : ℝ)) permutation
  kept : ℕ
  kept_eq : kept = Nat.ceil ((2*(k : ℝ)/(2*k+1))*q)
  kept_le : kept ≤ q
  decreases : kept < f.size

/-- Constructs a retained child frame by applying the inverse seeded permutation to the retained
positions and inheriting any origins in the parent frame. -/
def nextFrame {k N : ℕ} {f : Algorithm3Frame N} (P : Algorithm3Plan k N f)
    (s : Fin P.seeds) : Algorithm3Frame N :=
  ⟨P.kept, fun i =>
    let j := (P.permutation s).symm (Fin.castLE P.kept_le i)
    if h : j.val < f.size then f.origin ⟨j.val,h⟩ else none⟩

/-- The stage workspace parameter `min (n-1) (max k (ceil (r*n/N)))`. -/
def stageMemory (k N r n : ℕ) : ℕ :=
  min (n-1) (max k (Nat.ceil ((r : ℝ)*n/N)))

/-- States that an output is a verified collision and every reported index belongs to the frame. -/
def verifiedInFrame {N M k w : ℕ} (f : Algorithm3Frame N) (x : Fin N → ZMod M)
    (z : OutputSpace N M k w) : Prop :=
  verifiedOutput x z ∧ ∀ j, z.2.2.2 j ∈ frameSet f

/-- The uniform average over seeds of the probability that a query algorithm returns a verified
collision inside the frame. -/
def frameCallProbability {N M k : ℕ} [NeZero M]
    (A : RandomQueryAlgorithm N M k) (f : Algorithm3Frame N) (x : Fin N → ZMod M) : ℝ :=
  (∑ s, MeasureProb (Run (alphabetOracle x) (A.program s) (Qatlib.Foundations.PureStateMath.Ket (A.start s)))
    (Finset.univ.filter (verifiedInFrame f x)))/A.seeds

/-- Requires every seed to have zero probability of accepting an output that fails verification
inside the frame. -/
def frameCallSound {N M k : ℕ} [NeZero M]
    (A : RandomQueryAlgorithm N M k) (f : Algorithm3Frame N) : Prop :=
  ∀ x s, MeasureProb (Run (alphabetOracle x) (A.program s) (Qatlib.Foundations.PureStateMath.Ket (A.start s)))
    (Finset.univ.filter (fun z => yesOutput z ∧ ¬verifiedInFrame f x z)) = 0

/-- Packages a local Johnson search witness and an actual input-level call with matching framed
success probability, frame soundness, and the stated per-seed query bound. -/
structure Algorithm3NativeCall {N M : ℕ} [NeZero M]
    (k : ℕ) (f : Algorithm3Frame N) (memory : ℕ) where
  localWitness : NativeJohnsonWitness f.size (M+f.size+1) memory k
  clock : ℕ
  actual : RandomQueryAlgorithm N M k
  sound : frameCallSound actual f
  distribution : ∀ x,
    frameCallProbability actual f x =
      MeasureProb (Run (alphabetOracle (frameInput f x))
        (nativeAlgorithm2 localWitness clock) (Qatlib.Foundations.PureStateMath.Ket localWitness.init))
        (Finset.univ.filter (storedCollision k))
  paidQueries : ∀ s, QueryCount (actual.program s) ≤
    2*(memory+2*clock*jwT2 k memory)+2*k

/-- A recursive search tree with read-all leaves, Grover leaves, and native-walk stages followed
by seeded child trees. -/
inductive Algorithm3Tree (N M k : ℕ) [NeZero M] where
  | readAll : Algorithm3Frame N → RandomQueryAlgorithm N M k → Algorithm3Tree N M k
  | grover : Algorithm3Frame N → RandomQueryAlgorithm N M k → Algorithm3Tree N M k
  | walk : (f : Algorithm3Frame N) → (memory : ℕ) →
      Algorithm3NativeCall (M:=M) k f memory → (P : Algorithm3Plan k N f) →
      (Fin P.seeds → Algorithm3Tree N M k) → Algorithm3Tree N M k

/-- Returns the frame attached to the root of a search tree. -/
def treeFrame {N M k : ℕ} [NeZero M] : Algorithm3Tree N M k → Algorithm3Frame N
  | .readAll f _ | .grover f _ | .walk f _ _ _ _ => f

/-- The supremum of a natural-valued function over `Fin R`, equal to zero when the index type is
empty. -/
def maximumFinite (R : ℕ) (f : Fin R → ℕ) : ℕ := Finset.univ.sup f

/-- The maximum query count of a randomized query algorithm over its seeds. -/
def callQueries {N M k : ℕ} [NeZero M] (A : RandomQueryAlgorithm N M k) : ℕ :=
  maximumFinite A.seeds (fun s => QueryCount (A.program s))

/-- The workspace size plus the bit widths assigned to the query register, acceptance flag, and
output addresses. -/
def callQubits {N M k : ℕ} [NeZero M] (A : RandomQueryAlgorithm N M k) : ℕ :=
  A.workBits+Nat.clog 2 (N+1)+Nat.clog 2 (M+1)+1+k*Nat.clog 2 (N+1)

/-- Computes tree query cost by adding each native call's cost to the maximum child cost, using
the leaf call cost at leaves. -/
def treeQueries {N M k : ℕ} [NeZero M] : Algorithm3Tree N M k → ℕ
  | .readAll _ A | .grover _ A => callQueries A
  | .walk _ _ A P children => callQueries A.actual+
      maximumFinite P.seeds (fun s => treeQueries (children s))

/-- Computes tree space cost as the maximum call space along any branch. -/
def treeQubits {N M k : ℕ} [NeZero M] : Algorithm3Tree N M k → ℕ
  | .readAll _ A | .grover _ A => callQubits A
  | .walk _ _ A P children => max (callQubits A.actual)
      (maximumFinite P.seeds (fun s => treeQubits (children s)))

/-- Computes recursive success probability, accepting on the current walk call or, after
failure, averaging the child success probabilities over seeds. -/
def treeProbability {N M k : ℕ} [NeZero M] (x : Fin N → ZMod M) :
    Algorithm3Tree N M k → ℝ
  | .readAll f A | .grover f A => frameCallProbability A f x
  | .walk f _ A P children =>
      let accepted := frameCallProbability A.actual f x
      accepted+(1-accepted)*((∑ s, treeProbability x (children s))/P.seeds)

/-- States that the original indices represented by a frame contain a `k`-collision. -/
def frameHasCollision {N M : ℕ} (k : ℕ) (x : Fin N → ZMod M)
    (f : Algorithm3Frame N) : Prop := ∃ S, S ⊆ frameSet f ∧ IsCollision k x S

/-- Defines validity by branch-specific frame and size conditions, exact read-all behavior, and
Grover cost and success bounds. Walk stages must use `stageMemory` and have valid children
with the frames prescribed by `nextFrame`. -/
def algorithm3Valid {N M k : ℕ} [NeZero M] (r : ℕ) (C : ℝ) :
    Algorithm3Tree N M k → Prop
  | .readAll f A => frameWellFormed f ∧ f.size ≤ r ∧ frameCallSound A f ∧
      callQueries A ≤ f.size ∧
      ∀ x, frameCallProbability A f x = if frameHasCollision k x f then 1 else 0
  | .grover f A => frameWellFormed f ∧ r < f.size ∧ (f.size : ℝ) ≤ Real.sqrt N ∧
      frameCallSound A f ∧
      (callQueries A : ℝ) ≤ C*(f.size : ℝ)^((k : ℝ)/2)*(1+Real.log (N+1)) ∧
      ∀ x, (frameHasCollision k x f → 1-1/(N : ℝ) ≤ frameCallProbability A f x) ∧
        (¬frameHasCollision k x f → frameCallProbability A f x = 0)
  | .walk f memory _ P children => frameWellFormed f ∧ r < f.size ∧
      Real.sqrt N < f.size ∧ memory = stageMemory k N r f.size ∧
      k ≤ memory ∧ memory < f.size ∧
      ∀ s, treeFrame (children s) = nextFrame P s ∧ algorithm3Valid r C (children s)

/-- Requires every native-walk call in a tree to have success at least `p` whenever its frame
contains exactly one collision set. -/
def uniqueCallProbability {N M k : ℕ} [NeZero M] (p : ℝ) :
    Algorithm3Tree N M k → Prop
  | .readAll _ _ | .grover _ _ => True
  | .walk f _ A _ children =>
      (∀ x, (∃! S, S ⊆ frameSet f ∧ IsCollision k x S) →
        p ≤ frameCallProbability A.actual f x) ∧ ∀ s, uniqueCallProbability p (children s)

/-- Specifies valid full-input search trees for sufficiently large inputs, with a uniform
positive unique-collision call guarantee and the stated query and qubit bounds. -/
def Algorithm3NativeContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ (C p : ℝ) (N0 : ℕ), 0 < C ∧ 0 < p ∧ p ≤ 1 ∧
  ∀ (N M r : ℕ) [NeZero M], N0 ≤ N → 0 < M → k ≤ r → r ≤ N →
  ∃ P : Algorithm3Tree N M k,
    treeFrame P = initialFrame N ∧ algorithm3Valid r C P ∧ uniqueCallProbability p P ∧
    (treeQueries P : ℝ) ≤ C*queryScale k N r ∧
    (treeQubits P : ℝ) ≤ C*r*dataBits N M

/-- Specifies that valid full-input trees with unique-collision call guarantee `p` succeed with
probability at least `(1-ε)*p/2` on collision inputs for sufficiently large `N`. It also
requires zero success probability on inputs without collisions. -/
def Algorithm3SuccessContract : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
  ∀ (N M r : ℕ) [NeZero M], N0 ≤ N → 0 < M → k ≤ r → r ≤ N →
  ∀ (C p : ℝ) (P : Algorithm3Tree N M k), 0 < C → 0 ≤ p → p ≤ 1 →
    treeFrame P = initialFrame N → algorithm3Valid r C P → uniqueCallProbability p P →
    ∀ x : Fin N → ZMod M,
      (HasCollision k x → (1-ε)*p/2 ≤ treeProbability x P) ∧
      (¬HasCollision k x → treeProbability x P = 0)

end Qatlib.Concepts.WalkFind.SearchAlgorithm
