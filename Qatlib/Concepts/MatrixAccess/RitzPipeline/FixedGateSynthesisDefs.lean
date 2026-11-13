/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Basic
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordEmitterDefs
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Fixed-gate synthesis contracts and paid circuit words

This module defines the request encoding, fixed primitive predicate `IsFixedPrim`, clean
embedding `cleanEmbed`, and operator-norm acceptance condition `Accepts`. `Compiler` packages
ancilla allocation and gate emission, while `UniformLedger` records polynomial bounds in the
encoded request size. These circuit and approximation conventions fit the standard quantum
computation framework [NielsenChuang2010].

`PaidStep` and `CallForm` distinguish known gates from paid oracle calls. `compileWord`
substitutes only known gates, and `Clause1Claim`, `Clause2Claim`, and `Clause3Claim` state
synthesis, uniform emission, and mixed-circuit compilation contracts without supplying their
witnesses.

## Main statements

* `Accepts` requires fixed primitives, no synthesis oracle calls, approximation up to phase, and
  restoration of clean ancillas.
- `UniformLedger` bounds emitted length and ancilla count by a common polynomial.
- `wordMatrix` interprets mixed words, and `compileWord` expands their known gates.
* `Clause1Claim`, `Clause2Claim`, and `Clause3Claim` specify the successive compilation
  guarantees.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum (LocalQFTGate localGateMatrix localProgramMatrix localGateAdjoint
  localProgramAdjoint dyadicPhaseAngle)
open Qatlib.Foundations.PureStateMath (Reg QState Normalized ZeroStr)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open scoped Matrix.Norms.L2Operator
open scoped Classical

/-- Convert a local Hadamard, controlled phase, or swap into its canonical opcode using
natural-valued wire indices. -/
def opcodeOf {w : ℕ} : LocalQFTGate w → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Opcode
  | .h a => .hadamard a.val
  | .cp a c e neg => .phase a.val c.val e neg
  | .swap a c => .swap a.val c.val

/-- The natural-number fields of a local gate's canonical opcode. -/
def gateFields {w : ℕ} (g : LocalQFTGate w) : List ℕ :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields (opcodeOf g)

/-- Encode a synthesis request by concatenating the canonical natural-number encodings of width,
precision, and gate fields. -/
def synthInput (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : List Bool :=
  ([w, k] ++ gateFields g).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits

/-- The bit length of the encoded synthesis request. -/
def synthInputBits (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : ℕ :=
  (synthInput w g k).length

/-- The synthesis resource parameter `1 + synthInputBits w g k + k`. -/
def requestSize (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : ℕ :=
  1 + synthInputBits w g k + k

/-- A local gate is a fixed primitive if it is a Hadamard, a swap, or a controlled dyadic phase
with exponent at most three. -/
def IsFixedPrim {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ e _ => e ≤ 3
  | _ => True

instance {w : ℕ} (g : LocalQFTGate w) : Decidable (IsFixedPrim g) := by
  cases g with
  | h a => exact isTrue trivial
  | swap a c => exact isTrue trivial
  | cp a c e neg => exact inferInstanceAs (Decidable (e ≤ 3))

/-- The Boolean decision procedure for the fixed-primitive predicate `IsFixedPrim`. -/
def isFixedPrim {w : ℕ} (g : LocalQFTGate w) : Bool := decide (IsFixedPrim g)

/-- The Boolean primitive test returns true exactly when `IsFixedPrim` holds. -/
theorem isFixedPrim_eq_true_iff {w : ℕ} (g : LocalQFTGate w) :
    isFixedPrim g = true ↔ IsFixedPrim g :=
  decide_eq_true_iff

/-- Restrict an `n`-bit register to its first `w` bits, given `w ≤ n`. -/
def dataBits {n : ℕ} (w : ℕ) (hw : w ≤ n) (z : Reg n) : Reg w :=
  fun i => z ⟨i.val, by omega⟩

/-- Extract the auxiliary suffix of a register after the first `w` data bits. -/
def auxBits {width : ℕ} (w : ℕ) (z : Reg width) : Reg (width - w) :=
  fun i => z ⟨w + i.val, by omega⟩

/-- The matrix mapping a data basis register to the output register with the same available
initial data bits and zero bits beyond the data width. -/
def cleanEmbed (w width : ℕ) : Matrix (Reg width) (Reg w) ℂ :=
  fun p t => if p = (fun i : Fin width => if h : i.val < w then t ⟨i.val, h⟩ else false)
    then 1 else 0

/-- The Euclidean operator norm of the difference between two matrices of the same dimensions. -/
noncomputable def opError {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) : ℝ :=
  ‖A - B‖

/-- Two matrices agree within `tol` in Euclidean operator norm after multiplying the second by
some complex global phase. -/
def approxUpToPhase {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (tol : ℝ) : Prop :=
  ∃ θ : ℝ, ‖A - (Complex.exp (θ * Complex.I)) • B‖ ≤ tol

/-- The dyadic error tolerance `(1 / 2) ^ k` at precision `k`. -/
noncomputable def tolerance (k : ℕ) : ℝ := ((2 : ℝ) ⁻¹) ^ k

/-- For every normalized data input, the norm of the output component with a nonzero auxiliary
register is at most `tol`. -/
def ancillaRestored {width : ℕ} (w : ℕ) (M : Matrix (Reg width) (Reg w) ℂ) (tol : ℝ) :
    Prop :=
  ∀ ψ : QState (Reg w), Normalized ψ →
    ‖toEuclidean_fromVec (fun z : Reg width =>
      if auxBits w z = ZeroStr (width - w) then 0 else (M *ᵥ ψ) z)‖ ≤ tol

/-- A synthesis answer consisting of an output width and a list of local gates at that width. -/
structure SynthAnswer where

  width : ℕ

  word : List (LocalQFTGate width)

/-- The synthesis answer's oracle-call ledger, defined to be zero for these local gate words. -/
def answerOracleCalls (_ans : SynthAnswer) : ℕ := 0

/-- Serialize a synthesis answer as a canonical word containing its width and the opcodes of its
gates. -/
def answerBits (ans : SynthAnswer) : List Bool :=
  Qatlib.Concepts.BitWordCompiler.CanonicalCodec.wordBits ⟨ans.width, ans.word.map opcodeOf⟩

/-- A synthesis answer is accepted when its width extends the data width, its gates are fixed
primitives, and it uses no synthesis oracle calls. Its clean-input action must approximate
the requested gate up to phase within `tolerance k` and restore the auxiliary register to
that tolerance. -/
def Accepts (w : ℕ) (g : LocalQFTGate w) (k : ℕ) (ans : SynthAnswer) : Prop :=
  (∃ a : ℕ, ans.width = w + a) ∧
  (∀ h ∈ ans.word, IsFixedPrim h) ∧
  answerOracleCalls ans = 0 ∧
  approxUpToPhase (localProgramMatrix ans.word * cleanEmbed w ans.width)
    (cleanEmbed w ans.width * localGateMatrix g) (tolerance k) ∧
  ancillaRestored w (localProgramMatrix ans.word * cleanEmbed w ans.width) (tolerance k)

/-- A compiler assigns an ancilla count to each synthesis request and emits a local gate word at
the resulting extended width. -/
structure Compiler where

  anc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ

  emit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) → List (LocalQFTGate (w + anc w g k))

/-- Package a compiler's allocated output width and emitted gate word as a synthesis answer. -/
def Compiler.Segment (c : Compiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : SynthAnswer :=
  ⟨w + c.anc w g k, c.emit w g k⟩

/-- The acceptance contract for the answer produced by a compiler on a specified request. -/
def AcceptsAt (c : Compiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : Prop :=
  Accepts w g k (c.Segment w g k)

/-- A compiler has a uniform ledger if one polynomial in `requestSize` bounds both emitted
length and ancilla count for every request. -/
def UniformLedger (c : Compiler) : Prop :=
  ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
    (c.emit w g k).length ≤ C * (requestSize w g k) ^ D ∧
    c.anc w g k ≤ C * (requestSize w g k) ^ D

/-- For a controlled phase, a valid rational angle can be written with denominator `2 ^ bits`
and approximates its signed angle within `tolerance bits`. Other local gates impose no
condition. -/
def angleInputOK {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) (q : ℚ) : Prop :=
  match g with
  | .cp _ _ e neg =>
      |((q : ℝ) - dyadicPhaseAngle e neg)| ≤ tolerance bits ∧
        ∃ m : ℤ, q = m / ((2 : ℚ) ^ bits)
  | _ => True

/-- An emission plan that outputs each natural-number field literally in list order. -/
def fieldsPlan (fs : List ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Plan :=
  fs.foldr (fun j acc => .append (.emitNat (.literal j)) acc) (.literal [])

/-- An emission plan for an answer's width, gate count, and concatenated canonical opcode
fields. -/
def answerPlan (ans : SynthAnswer) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Plan :=
  let ops := ans.word.map opcodeOf
  .append (.emitNat (.literal ans.width))
    (.append (.emitNat (.literal ops.length))
      (fieldsPlan (ops.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields)))

/-- A paid oracle-call form specified by its slot and Boolean adjoint and control flags. -/
structure CallForm (S : Type) where

  slot : S

  adj : Bool

  ctrl : Bool

/-- A mixed circuit step, either a known local gate or a paid oracle call with a specified call
form. -/
inductive PaidStep (n : ℕ) (S : Type) where
  | known (g : LocalQFTGate n)
  | call (φ : CallForm S)

/-- Return a step's call form when it is a paid call, and `none` when it is a known gate. -/
def PaidStep.form {n : ℕ} {S : Type} : PaidStep n S → Option (CallForm S)
  | .known _ => none
  | .call φ => some φ

/-- Every paid call in the mixed word uses a form belonging to the supplied allowed list. -/
def paidLegal {n : ℕ} {S : Type} (W : List (PaidStep n S)) (paid : List (CallForm S)) :
    Prop :=
  ∀ s ∈ W, match s.form with | some φ => φ ∈ paid | none => True

/-- Count all paid oracle-call steps in a mixed word, ignoring known gates. -/
def callCount {n : ℕ} {S : Type} : List (PaidStep n S) → ℕ
  | [] => 0
  | .call _ :: rest => callCount rest + 1
  | .known _ :: rest => callCount rest

/-- Count occurrences of one specified oracle-call form in a mixed word. -/
def formCount {n : ℕ} {S : Type} (φ : CallForm S) : List (PaidStep n S) → ℕ
  | [] => 0
  | .call ψ :: rest => formCount φ rest + if ψ = φ then 1 else 0
  | .known _ :: rest => formCount φ rest

/-- Extract the known local gates of a mixed word in order, discarding paid calls. -/
def knownGates {n : ℕ} {S : Type} : List (PaidStep n S) → List (LocalQFTGate n)
  | [] => []
  | .known g :: rest => g :: knownGates rest
  | .call _ :: rest => knownGates rest

/-- Interpret a known step by its gate matrix and a paid call by the matrix assigned to its call
form. -/
noncomputable def stepMatrix {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ) :
    PaidStep n S → Matrix (Reg n) (Reg n) ℂ
  | .known g => localGateMatrix g
  | .call φ => O φ

/-- The matrix of a mixed word, multiplying successive step matrices in execution order with the
first step acting first. -/
noncomputable def wordMatrix {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ) :
    List (PaidStep n S) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | s :: rest => wordMatrix O rest * stepMatrix O s

/-- Replace each known gate by its supplied local program and retain every paid call with its
original form. -/
def compileWord {n m : ℕ} {S : Type} (f : LocalQFTGate n → List (LocalQFTGate m)) :
    List (PaidStep n S) → List (PaidStep m S)
  | [] => []
  | .known g :: rest => (f g).map PaidStep.known ++ compileWord f rest
  | .call φ :: rest => .call φ :: compileWord f rest

/-- The per-slot error budget `ε / (count + 1)` associated with a total allowance `ε`. -/
noncomputable def uniformBudget (ε : ℝ) (count : ℕ) : ℝ := ε / ((count : ℝ) + 1)

/-- The existence of a compiler with a uniform polynomial ledger that satisfies acceptance for
every gate and every precision `k ≥ 1`. -/
def Clause1Claim : Prop :=
  ∃ c : Compiler, UniformLedger c ∧
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k → AcceptsAt c w g k

/-- The existence of a uniformly bounded accepting compiler, valid rational angle inputs, and
one Turing-machine emitter whose time and space are polynomial in request size. The emitter
receives the encoded answer plan and outputs the canonical answer bits. -/
def Clause2Claim : Prop :=
  ∃ (c : Compiler) (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
      (C D : ℕ) (angleInput : (w : ℕ) → LocalQFTGate w → ℕ → ℚ),
    UniformLedger c ∧
    (∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k → AcceptsAt c w g k) ∧
    (∀ (w : ℕ) (g : LocalQFTGate w) (bits : ℕ), angleInputOK g bits (angleInput w g bits)) ∧
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      let ans := c.Segment w g k
      let p := answerPlan ans
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] p = answerBits ans ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput p [] k) (answerBits ans)
        (C * requestSize w g k ^ D) (C * requestSize w g k ^ D)

/-- The mixed-circuit compilation contract: known gates receive accepted approximations on a
common extended register with total tolerance at most `ε`, while unitary lifted oracle calls
act exactly up to phase on clean inputs. The compiled word approximates the original within
`ε`, preserves each paid call count and legality, and satisfies the stated length, bit-time,
and peak-space bounds. -/
def Clause3Claim : Prop :=
  ∀ (n : ℕ) (S : Type) (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (paid : List (CallForm S)) (W : List (PaidStep n S)) (L : ℕ) (ε : ℝ),
    (∀ φ, O φ ∈ Matrix.unitaryGroup (Reg n) ℂ) →
    paidLegal W paid → callCount W = L → 0 < ε →
    ∃ (A : ℕ) (f : LocalQFTGate n → List (LocalQFTGate (n + A))) (ks : List ℕ)
      (O' : CallForm S → Matrix (Reg (n + A)) (Reg (n + A)) ℂ)
      (bitTime peakSpace C D : ℕ),
      ks.length = (knownGates W).length ∧
      (∀ φ, O' φ ∈ Matrix.unitaryGroup (Reg (n + A)) ℂ) ∧
      (∀ φ, approxUpToPhase (O' φ * cleanEmbed n (n + A))
        (cleanEmbed n (n + A) * O φ) 0) ∧
      List.Forall₂ (fun (g : LocalQFTGate n) (k : ℕ) => Accepts n g k ⟨n + A, f g⟩)
        (knownGates W) ks ∧
      (ks.map tolerance).sum ≤ ε ∧
      approxUpToPhase
        (wordMatrix O' (compileWord f W) * cleanEmbed n (n + A))
        (cleanEmbed n (n + A) * wordMatrix O W) ε ∧
      (∀ φ : CallForm S, formCount φ (compileWord f W) = formCount φ W) ∧
      callCount (compileWord f W) = L ∧
      paidLegal (compileWord f W) paid ∧
      (compileWord f W).length ≤ L +
        (((knownGates W).zip ks).map
          (fun gk => C * (1 + requestSize n gk.1 gk.2) ^ D)).sum ∧
      bitTime ≤ (((knownGates W).zip ks).map
          (fun gk => C * (1 + requestSize n gk.1 gk.2) ^ D)).sum ∧
      peakSpace ≤ (((knownGates W).zip ks).map
          (fun gk => C * (1 + requestSize n gk.1 gk.2) ^ D)).foldl max 0

end Qatlib.Concepts.MatrixAccess.RitzPipeline
