/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.UnboundedExecutionRemainder

/-!
# Native tape definitions for a bounded random walk

`Symbol`, `Control`, and `program` describe a finite tape machine that loads an interval and
then moves left or right according to supplied coin bits until it reaches a boundary. `walk`
gives an arithmetic execution model, while `nativeLaw` records output, stopping reason,
transitions, and bits consumed. Classical random-walk simulation is studied in [Watrous1998].

The module also defines the initialized tape, an explicit alternating cycle word, and a
workspace set containing the input interval and cursor trace.

## Main statements

* `program`: A tape program with deterministic loading and coin-driven interior moves.
* `walk`: A fuel-bounded arithmetic model of the walk.
* `nativeLaw`: The distribution of native execution observations.
* `workspace`: The initialized interval together with visited cursor positions.

## References

* [Watrous, 1998][Watrous1998]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs

/-- The nine tape symbols used for blanks, interior cells, boundaries, start markers, and
Boolean outputs. -/
inductive Symbol
  | blank | cell | left | right | start | startLeft | startRight | out0 | out1
  deriving DecidableEq, Fintype, Inhabited

/-- The three control states of the native walk: loading, walking, and completion. -/
inductive Control
  | load | walk | done
  deriving DecidableEq, Fintype, Inhabited

/-- The native tape program that loads the start position, uses coin bits for interior moves,
and writes a Boolean output at a boundary. -/
def program : NativeTape.Program Symbol Control
  | .load, .left | .load, .cell => .det .load (.move .right)
  | .load, .start => .det .walk (.write .cell)
  | .load, .startLeft => .det .walk (.write .left)
  | .load, .startRight => .det .walk (.write .right)
  | .walk, .cell => .coin (fun b => (.walk, .move (if b then .right else .left)))
  | .walk, .left => .det .done (.write .out0)
  | .walk, .right => .det .done (.write .out1)
  | _, _ => .halt

/-- The finite interval encoding with left and right distances and a start marker, including the
boundary and empty-interval cases. -/
def inputWord : ℕ → ℕ → List Symbol
  | 0, 0 => []
  | 0, b+1 => .startLeft :: List.replicate b .cell ++ [.right]
  | a+1, 0 => .left :: List.replicate a .cell ++ [.startRight]
  | a+1, b+1 => .left :: List.replicate a .cell ++ .start ::
      List.replicate b .cell ++ [.right]

/-- The initial configuration in loading state with tape contents `inputWord a b`. -/
def input (a b : ℕ) : Turing.TM0.Cfg Symbol Control :=
  ⟨.load, Turing.Tape.mk₁ (inputWord a b)⟩

/-- The interval tape positioned at distances `a` and `b` from its two boundaries. -/
def positionTape : ℕ → ℕ → Turing.Tape Symbol
  | 0, 0 => Turing.Tape.mk₂ [] []
  | 0, b+1 => Turing.Tape.mk₂ [] (.left :: List.replicate b .cell ++ [.right])
  | a+1, 0 => Turing.Tape.mk₂ (List.replicate a .cell ++ [.left]) [.right]
  | a+1, b+1 => Turing.Tape.mk₂ (List.replicate a .cell ++ [.left])
      (.cell :: List.replicate b .cell ++ [.right])

/-- The walk-state configuration on `positionTape a b`. -/
def loaded (a b : ℕ) : Turing.TM0.Cfg Symbol Control :=
  ⟨.walk, positionTape a b⟩

/-- Encodes a Boolean as the tape symbol `out0` or `out1`. -/
def outputSymbol (b : Bool) : Symbol := if b then .out1 else .out0

/-- Decodes a Boolean only from a halted result in control state `done` whose head contains an
output symbol. -/
def output (r : NativeTape.Result Symbol Control) : Option Bool :=
  if r.stop = .halted ∧ r.cfg.q = .done then
    match r.cfg.Tape.head with
    | .out0 => some false
    | .out1 => some true
    | _ => none
  else none

/-- Extracts the optional output, stopping reason, transition count, and number of consumed bits
from a native result. -/
def observation (r : NativeTape.Result Symbol Control) :
    Option Bool × NativeTape.Stop × ℕ × ℕ :=
  (output r, r.stop, r.steps, r.bits.length)

/-- The distribution of observations of the native walk on `input a b` with the given transition
budget. -/
noncomputable def nativeLaw (a b budget : ℕ) :=
  (NativeTape.law program budget (input a b)).map observation

/-- The final boundary distances, optional output, stopping reason, unread and consumed bits,
and step count of an arithmetic walk. -/
structure WalkResult where
  left : ℕ
  right : ℕ
  out : Option Bool
  stop : NativeTape.Stop
  unread : List Bool
  bits : List Bool
  steps : ℕ

/-- Reconstructs the native configuration from a walk result, writing its output symbol in
control state `done` when an output is present. -/
def WalkResult.cfg (z : WalkResult) : Turing.TM0.Cfg Symbol Control :=
  match z.out with
  | none => loaded z.left z.right
  | some b => ⟨.done, (positionTape z.left z.right).write (outputSymbol b)⟩

/-- Prepends one consumed bit to a walk result and increases its step count by one. -/
def WalkResult.prependBit (b : Bool) (z : WalkResult) : WalkResult :=
  {z with bits := b :: z.bits, steps := z.steps + 1}

/-- Executes the bounded arithmetic walk using supplied bits, tracking boundary output, fuel
exhaustion, unavailable bits, and transition counts. -/
def walk : ℕ → List Bool → ℕ → ℕ → WalkResult
  | _, bs, 0, 0 => ⟨0, 0, none, .halted, bs, [], 0⟩
  | 0, bs, a, b => ⟨a, b, none, .fuel, bs, [], 0⟩
  | _+1, bs, 0, b+1 => ⟨0, b+1, some false, .halted, bs, [], 1⟩
  | _+1, bs, a+1, 0 => ⟨a+1, 0, some true, .halted, bs, [], 1⟩
  | _+1, [], a+1, b+1 => ⟨a+1, b+1, none, .needBits, [], [], 0⟩
  | n+1, bit::bs, a+1, b+1 =>
      (if bit then walk n bs (a+2) b else walk n bs a (b+2)).prependBit bit

/-- The word consisting of `n` repetitions of `true` followed by `false`. -/
def cycleWord : ℕ → List Bool
  | 0 => []
  | n+1 => true :: false :: cycleWord n

/-- The union of the initialized interval of `a + b + 1` cells and the cursor positions visited
by the supplied trace. -/
def workspace (a b : ℕ) (es : List (NativeTape.Tick Symbol Control)) : Finset ℤ :=
  (Finset.range (a+b+1)).image (fun n : ℕ => (n : ℤ)) ∪
    (NativeTape.cursorTrace program (a : ℤ) es).toFinset

end Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs
