/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Mathlib.Data.Nat.Bits
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.BitWordCompiler.CanonicalCodec

abbrev Bits := List Bool
def natBits (n : ℕ) : Bits := List.replicate n.bits.length true ++ [false] ++ n.bits
def framed (b : Bits) : Bits := natBits b.length ++ b

inductive Opcode where
  | hadamard (address : ℕ)
  | phase (first second precision : ℕ) (adjoint : Bool)
  | swap (first second : ℕ)
  | oracle (slot : ℕ) (control : Option ℕ) (adjoint : Bool) (wires : List ℕ)
  deriving DecidableEq, Repr

def fields : Opcode → List ℕ
  | .hadamard a => [0,a]
  | .phase a b k adj => [1,a,b,k,if adj then 1 else 0]
  | .swap a b => [2,a,b]
  | .oracle slot control adj ws =>
    [3,slot,match control with | none => 0 | some a => a+1,if adj then 1 else 0,ws.length] ++ ws
structure Word where
  width : ℕ
  ops : List Opcode
  deriving DecidableEq, Repr

def legalOpcode (width : ℕ) : Opcode → Prop
  | .hadamard a => a < width
  | .phase a b _ _ => a < width ∧ b < width
  | .swap a b => a < width ∧ b < width
  | .oracle _ c _ ws => (∀ a ∈ ws, a < width) ∧ ws.Nodup ∧
      (∀ a ∈ c, a < width ∧ a ∉ ws)
def Legal (w : Word) : Prop := ∀ op ∈ w.ops, legalOpcode w.width op
def wordBits (w : Word) : Bits :=
  ([w.width,w.ops.length] ++ w.ops.flatMap fields).flatMap natBits

inductive Scalar where
  | literal (value : ℕ)
  | parameter (index : ℕ)
  | precision
  | counter (depth : ℕ)
  deriving DecidableEq, Repr

def scalarBits : Scalar → Bits
  | .literal n => natBits 0 ++ natBits n
  | .parameter i => natBits 1 ++ natBits i
  | .precision => natBits 2
  | .counter i => natBits 3 ++ natBits i

def binaryValue (b : Bits) : ℕ := b.foldr (fun bit n => 2*n + if bit then 1 else 0) 0

def value (params : List Bits) (k : ℕ) (counters : List ℕ) : Scalar → ℕ
  | .literal n => n
  | .parameter i => binaryValue (params.getD i [])
  | .precision => k
  | .counter i => counters.getD i 0

inductive Plan where
  | literal (bits : Bits)
  | copy (parameter : ℕ)
  | emitNat (arg : Scalar)
  | fixedCount (width : ℕ) (arg : Scalar)
  | pairScan (first second : ℕ)
  | append (first second : Plan)
  | repeat (bound : Scalar) (body : Plan)
  deriving DecidableEq, Repr

def planBits : Plan → Bits
  | .literal b => natBits 0 ++ framed b
  | .copy i => natBits 1 ++ natBits i
  | .emitNat a => natBits 2 ++ scalarBits a
  | .fixedCount w a => natBits 3 ++ natBits w ++ scalarBits a
  | .pairScan i j => natBits 4 ++ natBits i ++ natBits j
  | .append a b => natBits 5 ++ planBits a ++ planBits b
  | .repeat n b => natBits 6 ++ scalarBits n ++ planBits b

def emit (params : List Bits) (k : ℕ) (counters : List ℕ) : Plan → Bits
  | .literal b => b
  | .copy i => params.getD i []
  | .emitNat a => natBits (value params k counters a)
  | .fixedCount w a => List.ofFn (fun i : Fin w => (value params k counters a).testBit i.val)
  | .pairScan i j => ((params.getD i []).zip (params.getD j [])).flatMap (fun p => [p.1,p.2])
  | .append a b => emit params k counters a ++ emit params k counters b
  | .repeat n body => (List.range (value params k counters n)).flatMap
      (fun i => emit params k (i::counters) body)

def work (params : List Bits) (k : ℕ) (counters : List ℕ) : Plan → ℕ
  | .literal b => b.length+1
  | .copy i => (params.getD i []).length+1
  | .emitNat a => (natBits (value params k counters a)).length+1
  | .fixedCount w _ => w+1
  | .pairScan i j => (params.getD i []).length+(params.getD j []).length+1
  | .append a b => work params k counters a+work params k counters b+1
  | .repeat n body => 1+(List.range (value params k counters n)).foldl
      (fun sum i => sum + work params k (i::counters) body) 0

def emitterInput (p : Plan) (params : List Bits) (k : ℕ) : Bits :=
  planBits p ++ natBits params.length ++ params.flatMap framed ++ natBits k

def headPosition {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))) (input : Bits) : ℕ → ℤ
  | 0 => 0
  | t+1 => headPosition M input t +
    match BitMachineAfter M (input.map some) t with
    | none => 0
    | some cfg => match M cfg.q cfg.Tape.head with
      | some (_, .move .left) => -1
      | some (_, .move .right) => 1
      | _ => 0

def Runs {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q+1)))
    (input output : Bits) (time space : ℕ) : Prop :=
  input.length ≤ space ∧ ∃ t cfg,
    t ≤ time ∧ BitMachineAfter M (input.map some) t = some cfg ∧ Turing.TM0.step M cfg = none ∧
    headPosition M input t = 0 ∧
    (∀ i, cfg.Tape.right₀.nth i = (output.map some).getD i none) ∧
    (∀ i, cfg.Tape.left.nth i = none) ∧
    (∀ u ≤ t, -(space : ℤ) ≤ headPosition M input u ∧ headPosition M input u ≤ (space : ℤ))

def ComputesAt (f : Bits → Bits) (time space : Bits → ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ input, Runs M input (f input) (time input) (space input)
end Qatlib.Concepts.BitWordCompiler.CanonicalCodec
