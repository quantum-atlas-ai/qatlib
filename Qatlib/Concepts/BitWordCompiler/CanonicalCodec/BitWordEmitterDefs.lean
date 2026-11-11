/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Mathlib.Data.Nat.Bits

/-!
# Canonical bit-word encodings and emission plans

`Word` records a register width and a list of gate or oracle instructions, with address
constraints expressed by `Legal`. The encodings `natBits`, `wordBits`, and `planBits` serialize
natural numbers, words, and parameterized emission plans.

`emit` evaluates plans and `work` assigns a recursive cost. The predicates `Runs` and
`ComputesAt` specify clean binary Turing-machine output with explicit time and head-position
bounds.

The computational background is described in [KitaevShenVyalyi2002].

## Main statements

* `wordBits`: serializes a word through its natural-number fields.
* `emit`: interprets literals, parameter copies, scans, concatenations, and bounded repetitions.
* `Runs`: specifies halting at the origin with clean output and bounded head displacement.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.BitWordCompiler.CanonicalCodec

/-- Finite binary strings, represented as lists of Boolean values. -/
abbrev Bits := List Bool
/-- Encodes `n` by a unary prefix for its binary length, a false separator, and its
least-significant-bit-first binary expansion. -/
def natBits (n : ℕ) : Bits := List.replicate n.bits.length true ++ [false] ++ n.bits
/-- Prefixes a bit string with the `natBits` encoding of its length. -/
def framed (b : Bits) : Bits := natBits b.length ++ b

/-- Instructions for Hadamard, phase, swap, and oracle operations, carrying natural-number
addresses and optional control data. -/
inductive Opcode where
  | hadamard (address : ℕ)
  | phase (first second precision : ℕ) (adjoint : Bool)
  | swap (first second : ℕ)
  | oracle (slot : ℕ) (control : Option ℕ) (adjoint : Bool) (wires : List ℕ)
  deriving DecidableEq, Repr

/-- Serializes an opcode as a tagged list of natural-number fields. -/
def fields : Opcode → List ℕ
  | .hadamard a => [0,a]
  | .phase a b k adj => [1,a,b,k,if adj then 1 else 0]
  | .swap a b => [2,a,b]
  | .oracle slot control adj ws =>
    [3,slot,match control with | none => 0 | some a => a+1,if adj then 1 else 0,ws.length] ++ ws
/-- A finite instruction word together with its declared register width. -/
structure Word where
  width : ℕ
  ops : List Opcode
  deriving DecidableEq, Repr

/-- Requires opcode addresses to lie below `width`, with distinct oracle wires and any control
wire disjoint from them. -/
def legalOpcode (width : ℕ) : Opcode → Prop
  | .hadamard a => a < width
  | .phase a b _ _ => a < width ∧ b < width
  | .swap a b => a < width ∧ b < width
  | .oracle _ c _ ws => (∀ a ∈ ws, a < width) ∧ ws.Nodup ∧
      (∀ a ∈ c, a < width ∧ a ∉ ws)
/-- A word is legal when each of its opcodes satisfies `legalOpcode` at the declared width. -/
def Legal (w : Word) : Prop := ∀ op ∈ w.ops, legalOpcode w.width op
/-- Encodes a word by concatenating the natural-number encodings of its width, instruction
count, and opcode fields. -/
def wordBits (w : Word) : Bits :=
  ([w.width,w.ops.length] ++ w.ops.flatMap fields).flatMap natBits

/-- Natural-number expressions given by literals, binary parameters, precision, or loop
counters. -/
inductive Scalar where
  | literal (value : ℕ)
  | parameter (index : ℕ)
  | precision
  | counter (depth : ℕ)
  deriving DecidableEq, Repr

/-- Encodes a scalar expression by a constructor tag followed by any associated natural-number
argument. -/
def scalarBits : Scalar → Bits
  | .literal n => natBits 0 ++ natBits n
  | .parameter i => natBits 1 ++ natBits i
  | .precision => natBits 2
  | .counter i => natBits 3 ++ natBits i

/-- Interprets a bit string as a natural number with the least significant bit first. -/
def binaryValue (b : Bits) : ℕ := b.foldr (fun bit n => 2*n + if bit then 1 else 0) 0

/-- Evaluates a scalar using the supplied parameters, precision, and counter stack, defaulting
missing entries to zero. -/
def value (params : List Bits) (k : ℕ) (counters : List ℕ) : Scalar → ℕ
  | .literal n => n
  | .parameter i => binaryValue (params.getD i [])
  | .precision => k
  | .counter i => counters.getD i 0

/-- Emission plans built from literal strings, parameter copies, scalar encodings, fixed-width
outputs, pair scans, concatenation, and bounded repetition. -/
inductive Plan where
  | literal (bits : Bits)
  | copy (parameter : ℕ)
  | emitNat (arg : Scalar)
  | fixedCount (width : ℕ) (arg : Scalar)
  | pairScan (first second : ℕ)
  | append (first second : Plan)
  | repeat (bound : Scalar) (body : Plan)
  deriving DecidableEq, Repr

/-- Serializes an emission plan recursively using natural-number constructor tags. -/
def planBits : Plan → Bits
  | .literal b => natBits 0 ++ framed b
  | .copy i => natBits 1 ++ natBits i
  | .emitNat a => natBits 2 ++ scalarBits a
  | .fixedCount w a => natBits 3 ++ natBits w ++ scalarBits a
  | .pairScan i j => natBits 4 ++ natBits i ++ natBits j
  | .append a b => natBits 5 ++ planBits a ++ planBits b
  | .repeat n b => natBits 6 ++ scalarBits n ++ planBits b

/-- Evaluates an emission plan to a bit string, pushing each repetition index onto the counter
stack. -/
def emit (params : List Bits) (k : ℕ) (counters : List ℕ) : Plan → Bits
  | .literal b => b
  | .copy i => params.getD i []
  | .emitNat a => natBits (value params k counters a)
  | .fixedCount w a => List.ofFn (fun i : Fin w => (value params k counters a).testBit i.val)
  | .pairScan i j => ((params.getD i []).zip (params.getD j [])).flatMap (fun p => [p.1,p.2])
  | .append a b => emit params k counters a ++ emit params k counters b
  | .repeat n body => (List.range (value params k counters n)).flatMap
      (fun i => emit params k (i::counters) body)

/-- Assigns a recursive work count to an emission plan, including output processing and
plan-constructor overhead. -/
def work (params : List Bits) (k : ℕ) (counters : List ℕ) : Plan → ℕ
  | .literal b => b.length+1
  | .copy i => (params.getD i []).length+1
  | .emitNat a => (natBits (value params k counters a)).length+1
  | .fixedCount w _ => w+1
  | .pairScan i j => (params.getD i []).length+(params.getD j []).length+1
  | .append a b => work params k counters a+work params k counters b+1
  | .repeat n body => 1+(List.range (value params k counters n)).foldl
      (fun sum i => sum + work params k (i::counters) body) 0

/-- Encodes an emission plan, its framed parameters, and its precision as one machine input. -/
def emitterInput (p : Plan) (params : List Bits) (k : ℕ) : Bits :=
  planBits p ++ natBits params.length ++ params.flatMap framed ++ natBits k

/-- Tracks the signed displacement of the machine head after each number of transitions,
starting at zero. -/
def headPosition {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))) (input : Bits) : ℕ → ℤ
  | 0 => 0
  | t+1 => headPosition M input t +
    match BitMachineAfter M (input.map some) t with
    | none => 0
    | some cfg => match M cfg.q cfg.Tape.head with
      | some (_, .move .left) => -1
      | some (_, .move .right) => 1
      | _ => 0

/-- Specifies halting within the time bound at the origin with the given output, a blank left
tape, and head displacement bounded by `space` throughout. -/
def Runs {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (input output : Bits) (time space : ℕ) : Prop :=
  input.length ≤ space ∧ ∃ t cfg,
    t ≤ time ∧ BitMachineAfter M (input.map some) t = some cfg ∧ Turing.TM0.step M cfg = none ∧
    headPosition M input t = 0 ∧
    (∀ i, cfg.Tape.right₀.nth i = (output.map some).getD i none) ∧
    (∀ i, cfg.Tape.left.nth i = none) ∧
    (∀ u ≤ t, -(space : ℤ) ≤ headPosition M input u ∧ headPosition M input u ≤ (space : ℤ))

/-- States that one finite-state binary Turing machine computes `f` on every input under the
supplied time and space bounds. -/
def ComputesAt (f : Bits → Bits) (time space : Bits → ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ input, Runs M input (f input) (time input) (space input)
end Qatlib.Concepts.BitWordCompiler.CanonicalCodec
