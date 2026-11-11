/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Machine definitions for copying, reset, and majority repetition

This module defines multitrack Boolean tape symbols, TM0 copy and reset tables, and
`majorityTable`, which copies the input onto a separate track for each simulated run and tallies
the decisions. `majorityBudget` and `majorityPolyBound` record explicit budgets for this
repetition construction in the randomized-computation setting of [NielsenChuang2010].

It also provides TM2 stack copy and reset programs, three input encodings, and two small
coin-driven machines used to study the difference between fresh runs and repeated reads of one
stored result.

## Main definitions

* `copyMachineTable` and `resetMachineTable`: two-track copy and scratch-clear transition
  tables.
* `majorityTable`: a multitrack repeated-run machine with an acceptance tally.
* `tm2Copy` and `tm2Reset`: stack-based copy and reset programs.
* `naiveMajorityTable`: a machine that rereads a stored two-coin result.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

/-- A tape symbol consisting of `m` tracks, each carrying an optional Boolean bit. -/
def Tracks (m : ℕ) : Type := Fin m → Option Bool

instance tracksInhabited (m : ℕ) : Inhabited (Tracks m) := ⟨fun _ => none⟩

/-- Encode the input on track zero and leave all other tracks blank. -/
def tracksEncode (m : ℕ) (input : List Bool) : List (Tracks m) :=
  input.map fun b t => if t.val = 0 then some b else none

/-- Control states for the copy machine's write, right-move, and return-home phases, each
carrying a position counter. -/
inductive CopyCtrl : Type
  | cw (pos : ℕ)
  | cm (pos : ℕ)
  | ch (pos : ℕ)

instance : Inhabited CopyCtrl := ⟨.cw 0⟩

/-- The two-track transition table that copies the nonblank input prefix from track zero to
track one and then returns the head to the origin. -/
def copyMachineTable : Turing.TM0.Machine (Tracks 2) CopyCtrl
  | .cw pos, sym =>
      match sym 0 with
      | some b => some (.cm pos, .write fun t => if t.val = 1 then some b else sym t)
      | none => some (.ch pos, .write sym)
  | .cm pos, _ => some (.cw (pos + 1), .move Turing.Dir.right)
  | .ch 0, _ => none
  | .ch (pos + 1), _ => some (.ch pos, .move Turing.Dir.left)

/-- The constantly true acceptance function for the copy machine. -/
def copyAccept : CopyCtrl → Bool := fun _ => true

/-- Control states for the reset machine's scratch-clear, right-move, and return-home phases,
each carrying a position counter. -/
inductive ResetCtrl : Type
  | rw (pos : ℕ)
  | rm (pos : ℕ)
  | rh (pos : ℕ)

instance : Inhabited ResetCtrl := ⟨.rw 0⟩

/-- The two-track transition table that clears track one across the nonblank track-zero prefix
and then returns the head to the origin. -/
def resetMachineTable : Turing.TM0.Machine (Tracks 2) ResetCtrl
  | .rw pos, sym =>
      match sym 0 with
      | some _ => some (.rm pos, .write fun t => if t.val = 1 then none else sym t)
      | none => some (.rh pos, .write sym)
  | .rm pos, _ => some (.rw (pos + 1), .move Turing.Dir.right)
  | .rh 0, _ => none
  | .rh (pos + 1), _ => some (.rh pos, .move Turing.Dir.left)

/-- The constantly true acceptance function for the reset machine. -/
def resetAccept : ResetCtrl → Bool := fun _ => true

/-- Encode Boolean input on track zero of a two-track tape with track one blank. -/
def twoTrackBitEncode (input : List Bool) : List (Tracks 2) := tracksEncode 2 input

/-- Encode each input bit identically on both tracks. -/
def bothTrackEncode (input : List Bool) : List (Tracks 2) :=
  input.map fun b _ => some b

/-- The length of the initial tape-list prefix whose track-zero entries are nonblank. -/
def inputWindow (l : List (Tracks 2)) : ℕ :=
  (l.takeWhile fun s => (s 0).isSome).length

/-- Clear track one inside the input window and preserve the remainder of the tape list. -/
def resetWindowList (l : List (Tracks 2)) : List (Tracks 2) :=
  ((l.take (inputWindow l)).map (fun s t => if t.val = 1 then none else s t) : List (Tracks 2))
    ++ l.drop (inputWindow l)

/-- Every nonblank scratch cell on track one lies within distance `s` of the tape head. -/
def ScratchWithinHeadReach (s : ℕ) (T : Turing.Tape (Tracks 2)) : Prop :=
  ∀ i : ℤ, T.nth i 1 ≠ none → |i| ≤ s

/-- Update an integer head offset by minus one for a left move and plus one for a right move. -/
def dirShift (off : ℤ) : Turing.Dir → ℤ
  | Turing.Dir.left => off - 1
  | Turing.Dir.right => off + 1

/-- The work-track index `j + 1` reserved for simulated run `j`, leaving track zero for the
input. -/
def runTrackIdx (r : ℕ) (j : Fin (2 * r + 1)) : Fin (2 * r + 2) :=
  ⟨j.val + 1, by omega⟩

/-- Control states for copying input to each run track, simulating its machine, returning to the
origin, and accumulating an acceptance tally. -/
inductive MajCtrl (Q r : ℕ) : Type
  | copyW (j : Fin (2 * r + 1)) (tally pos : ℕ)
  | copyM (j : Fin (2 * r + 1)) (tally pos : ℕ)
  | copyHome (j : Fin (2 * r + 1)) (tally pos : ℕ)
  | simQ (j : Fin (2 * r + 1)) (q : Fin (Q + 1)) (tally : ℕ) (off : ℤ)
  | tallyH (j : Fin (2 * r + 1)) (tally : ℕ) (bit : Bool) (off : ℤ)
  | finalH (tally : ℕ)

instance {Q r : ℕ} : Inhabited (MajCtrl Q r) := ⟨.copyW ⟨0, by omega⟩ 0 0⟩

/-- The coin-selected multitrack transition table that copies the input for `2 * r + 1`
simulations, returns home between runs, and tallies their acceptance bits. -/
def majorityTable (Q r : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (Tracks (2 * r + 2)) (MajCtrl Q r)
  | _, .copyW j tally pos, sym =>
      match sym ⟨0, by omega⟩ with
      | some b => some (.copyM j tally pos,
          .write fun t => if t = runTrackIdx r j then some b else sym t)
      | none => some (.copyHome j tally pos, .write sym)
  | _, .copyM j tally pos, _ => some (.copyW j tally (pos + 1), .move Turing.Dir.right)
  | _, .copyHome j tally 0, sym =>
      some (.simQ j ⟨0, by omega⟩ tally 0, .write sym)
  | _, .copyHome j tally (pos + 1), _ =>
      some (.copyHome j tally pos, .move Turing.Dir.left)
  | c, .simQ j q tally off, sym =>
      match M c q (sym (runTrackIdx r j)) with
      | some (q', .write a) => some (.simQ j q' tally off,
          .write fun t => if t = runTrackIdx r j then a else sym t)
      | some (q', .move d) => some (.simQ j q' tally (dirShift off d), .move d)
      | none => some (.tallyH j tally (acceptM q) off, .write sym)
  | _, .tallyH j tally bit 0, sym =>
      if h : j.val + 1 < 2 * r + 1 then
        some (.copyW ⟨j.val + 1, h⟩ (tally + bit.toNat) 0, .write sym)
      else some (.finalH (tally + bit.toNat), .write sym)
  | _, .tallyH j tally bit (n + 1 : ℕ), _ =>
      some (.tallyH j tally bit n, .move Turing.Dir.left)
  | _, .tallyH j tally bit (-(n + 1 : ℕ)), _ =>
      some (.tallyH j tally bit (-(n : ℕ)), .move Turing.Dir.right)
  | _, .finalH _, _ => none

/-- The majority bit of `2 * r + 1` Boolean entries whose first `tally` indices are marked true. -/
def majorityAcceptBit (r tally : ℕ) : Bool :=
  MajorityBit fun i : Fin (2 * r + 1) => i.val < tally

/-- Read the majority acceptance bit in the final tally state, returning true in other control
states. -/
def majorityAccept (Q r : ℕ) : MajCtrl Q r → Bool
  | .finalH tally => majorityAcceptBit r tally
  | _ => true

/-- The repeated-run fair-coin machine defined by `majorityTable`. -/
def majorityCoinMachine (Q r : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (Tracks (2 * r + 2)) (MajCtrl Q r) :=
  majorityTable Q r M acceptM

/-- Encode input on track zero with `2 * r + 1` blank tracks reserved for simulated runs. -/
def majorityEncode (r : ℕ) (input : List Bool) : List (Tracks (2 * r + 2)) :=
  tracksEncode (2 * r + 2) input

/-- The explicit repetition budget `(2 * r + 1) * (4 * n + 2 * T + 8) + 2`. -/
def majorityBudget (r n T : ℕ) : ℕ := (2 * r + 1) * (4 * n + 2 * T + 8) + 2

/-- The polynomial repetition bound `(2 * r + 1) * (4 * c + 12) * ((n + 1)^(k + 1) + 1)`. -/
def majorityPolyBound (r c k n : ℕ) : ℕ :=
  (2 * r + 1) * (4 * c + 12) * (n + 1) ^ (k + 1) + (2 * r + 1) * (4 * c + 12)

/-- The input, work, and auxiliary stack indices for the TM2 programs. -/
inductive TM2Stack : Type
  | input
  | work
  | aux
  deriving DecidableEq

/-- The constant Boolean alphabet on each of the three TM2 stacks. -/
abbrev tm2StackΓ : TM2Stack → Type := fun _ => Bool

/-- The transfer and restore program labels for stack copying. -/
inductive TM2CopyLabel : Type
  | transfer
  | restore

/-- The stack program that transfers input to an auxiliary stack, then restores the input while
copying it onto the work stack. -/
def tm2Copy : TM2CopyLabel → Turing.TM2.Stmt tm2StackΓ TM2CopyLabel (Option Bool)
  | .transfer =>
      .pop TM2Stack.input (fun _ o => o)
        (.branch (fun v => v.isNone) (.goto fun _ => .restore)
          (.push TM2Stack.aux (fun v => v.getD false) (.goto fun _ => .transfer)))
  | .restore =>
      .pop TM2Stack.aux (fun _ o => o)
        (.branch (fun v => v.isNone) .halt
          (.push TM2Stack.work (fun v => v.getD false)
            (.push TM2Stack.input (fun v => v.getD false) (.goto fun _ => .restore))))

/-- Initialize the stack-copy program with the input list and empty work and auxiliary stacks. -/
def tm2InitCopy (input : List Bool) :
    Turing.TM2.Cfg tm2StackΓ TM2CopyLabel (Option Bool) :=
  ⟨some .transfer, none, fun k =>
    match k with
    | TM2Stack.input => input
    | _ => []⟩

/-- The single clear-phase label of the stack-reset program. -/
inductive TM2ResetLabel : Type
  | clear

/-- The stack program that repeatedly pops the work stack until it is empty and then halts. -/
def tm2Reset : TM2ResetLabel → Turing.TM2.Stmt tm2StackΓ TM2ResetLabel (Option Bool)
  | .clear =>
      .pop TM2Stack.work (fun _ o => o)
        (.branch (fun v => v.isNone) .halt (.goto fun _ => .clear))

/-- Initialize the stack-reset program with specified input and work lists and an empty
auxiliary stack. -/
def tm2InitReset (input work : List Bool) :
    Turing.TM2.Cfg tm2StackΓ TM2ResetLabel (Option Bool) :=
  ⟨some .clear, none, fun k =>
    match k with
    | TM2Stack.input => input
    | TM2Stack.work => work
    | _ => []⟩

/-- Run a TM2 program with a finite step budget, returning a halting configuration when reached
and `none` if the budget expires while its label is active. -/
def tm2Run {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) :
    ℕ → Turing.TM2.Cfg Γ Λ σ → Option (Turing.TM2.Cfg Γ Λ σ)
  | 0, cfg =>
      match cfg.l with
      | none => some cfg
      | some _ => none
  | t + 1, cfg =>
      match Turing.TM2.step M cfg with
      | none => some cfg
      | some cfg' => tm2Run M t cfg'

/-- Encode Boolean input as a list of nonblank optional bits. -/
def standardBitEncode (input : List Bool) : List (Option Bool) := input.map some

/-- Encode each input bit as a pair with false marker and append the terminal pair `(false,
true)`. -/
def delimitedPairEncode (input : List Bool) : List (Bool × Bool) :=
  (input.map fun b => (b, false)) ++ [(false, true)]

/-- Control states for reading two coin bits and storing their disjunction as output. -/
inductive OrRunCtrl : Type
  | read1
  | read2 (b : Bool)
  | outC (v : Bool)

instance : Inhabited OrRunCtrl := ⟨.read1⟩

/-- The coin-selected transition table that reads two successive coins and halts with their
disjunction stored in its control state. -/
def orRunTable : Bool → Turing.TM0.Machine (Tracks 2) OrRunCtrl
  | c, .read1, sym => some (.read2 c, .write sym)
  | c, .read2 b, sym => some (.outC (b || c), .write sym)
  | _, .outC _, _ => none

/-- Read the stored OR output in the final state, returning true in other states. -/
def orRunAccept : OrRunCtrl → Bool
  | .outC v => v
  | _ => true

/-- Control states for a two-coin OR computation followed by repeated reads of its stored
scratch result. -/
inductive NaiveCtrl (r : ℕ) : Type
  | read1
  | read2 (b : Bool)
  | settle (v : Bool)
  | fake (j : ℕ) (v : Bool) (half : Bool)
  | outC (v : Bool)

instance {r : ℕ} : Inhabited (NaiveCtrl r) := ⟨.read1⟩

/-- The coin-list budget `4 * r + 3` assigned to the repeated-read construction. -/
def naiveBudget (r : ℕ) : ℕ := 4 * r + 3

/-- The transition table that computes the OR of two coins, stores it on track one, and rereads
that stored bit during its repetition phase. -/
def naiveMajorityTable (r : ℕ) : Bool → Turing.TM0.Machine (Tracks 2) (NaiveCtrl r)
  | c, .read1, sym => some (.read2 c, .write sym)
  | c, .read2 b, sym => some (.settle (b || c), .write sym)
  | _, .settle v, sym =>
      some (.fake 0 v false, .write fun t => if t.val = 1 then some v else sym t)
  | _, .fake j _ false, sym =>
      match sym 1 with
      | some w => some (.fake j w true, .write sym)
      | none => some (.fake j false true, .write sym)
  | _, .fake j v true, sym =>
      if h : j + 1 < 2 * r then some (.fake (j + 1) v false, .write sym)
      else some (.outC v, .write sym)
  | _, .outC _, _ => none

/-- Read the stored output in a final repeated-read state, returning true in other states. -/
def naiveMajorityAccept (r : ℕ) : NaiveCtrl r → Bool
  | .outC v => v
  | _ => true

end Qatlib.Concepts.ClassicalTape.TapeCompilation
