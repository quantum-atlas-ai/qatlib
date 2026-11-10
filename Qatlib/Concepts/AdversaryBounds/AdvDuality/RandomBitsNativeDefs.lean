/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs

inductive Symbol
  | blank | cell | left | right | start | startLeft | startRight | out0 | out1
  deriving DecidableEq, Fintype, Inhabited

inductive Control
  | load | walk | done
  deriving DecidableEq, Fintype, Inhabited

def program : NativeTape.Program Symbol Control
  | .load, .left | .load, .cell => .det .load (.move .right)
  | .load, .start => .det .walk (.write .cell)
  | .load, .startLeft => .det .walk (.write .left)
  | .load, .startRight => .det .walk (.write .right)
  | .walk, .cell => .coin (fun b => (.walk, .move (if b then .right else .left)))
  | .walk, .left => .det .done (.write .out0)
  | .walk, .right => .det .done (.write .out1)
  | _, _ => .halt

def inputWord : ℕ → ℕ → List Symbol
  | 0, 0 => []
  | 0, b+1 => .startLeft :: List.replicate b .cell ++ [.right]
  | a+1, 0 => .left :: List.replicate a .cell ++ [.startRight]
  | a+1, b+1 => .left :: List.replicate a .cell ++ .start ::
      List.replicate b .cell ++ [.right]

def input (a b : ℕ) : Turing.TM0.Cfg Symbol Control :=
  ⟨.load, Turing.Tape.mk₁ (inputWord a b)⟩

def positionTape : ℕ → ℕ → Turing.Tape Symbol
  | 0, 0 => Turing.Tape.mk₂ [] []
  | 0, b+1 => Turing.Tape.mk₂ [] (.left :: List.replicate b .cell ++ [.right])
  | a+1, 0 => Turing.Tape.mk₂ (List.replicate a .cell ++ [.left]) [.right]
  | a+1, b+1 => Turing.Tape.mk₂ (List.replicate a .cell ++ [.left])
      (.cell :: List.replicate b .cell ++ [.right])

def loaded (a b : ℕ) : Turing.TM0.Cfg Symbol Control :=
  ⟨.walk, positionTape a b⟩

def outputSymbol (b : Bool) : Symbol := if b then .out1 else .out0

def output (r : NativeTape.Result Symbol Control) : Option Bool :=
  if r.stop = .halted ∧ r.cfg.q = .done then
    match r.cfg.Tape.head with
    | .out0 => some false
    | .out1 => some true
    | _ => none
  else none

def observation (r : NativeTape.Result Symbol Control) :
    Option Bool × NativeTape.Stop × ℕ × ℕ :=
  (output r, r.stop, r.steps, r.bits.length)

noncomputable def nativeLaw (a b budget : ℕ) :=
  (NativeTape.law program budget (input a b)).map observation

structure WalkResult where
  left : ℕ
  right : ℕ
  out : Option Bool
  stop : NativeTape.Stop
  unread : List Bool
  bits : List Bool
  steps : ℕ

def WalkResult.cfg (z : WalkResult) : Turing.TM0.Cfg Symbol Control :=
  match z.out with
  | none => loaded z.left z.right
  | some b => ⟨.done, (positionTape z.left z.right).write (outputSymbol b)⟩

def WalkResult.prependBit (b : Bool) (z : WalkResult) : WalkResult :=
  {z with bits := b :: z.bits, steps := z.steps + 1}

def walk : ℕ → List Bool → ℕ → ℕ → WalkResult
  | _, bs, 0, 0 => ⟨0, 0, none, .halted, bs, [], 0⟩
  | 0, bs, a, b => ⟨a, b, none, .fuel, bs, [], 0⟩
  | _+1, bs, 0, b+1 => ⟨0, b+1, some false, .halted, bs, [], 1⟩
  | _+1, bs, a+1, 0 => ⟨a+1, 0, some true, .halted, bs, [], 1⟩
  | _+1, [], a+1, b+1 => ⟨a+1, b+1, none, .needBits, [], [], 0⟩
  | n+1, bit::bs, a+1, b+1 =>
      (if bit then walk n bs (a+2) b else walk n bs a (b+2)).prependBit bit

def cycleWord : ℕ → List Bool
  | 0 => []
  | n+1 => true :: false :: cycleWord n

def workspace (a b : ℕ) (es : List (NativeTape.Tick Symbol Control)) : Finset ℤ :=
  (Finset.range (a+b+1)).image (fun n : ℕ => (n : ℤ)) ∪
    (NativeTape.cursorTrace program (a : ℤ) es).toFinset

end Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs
