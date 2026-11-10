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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

def Tracks (m : ℕ) : Type := Fin m → Option Bool

instance tracksInhabited (m : ℕ) : Inhabited (Tracks m) := ⟨fun _ => none⟩

def tracksEncode (m : ℕ) (input : List Bool) : List (Tracks m) :=
  input.map fun b t => if t.val = 0 then some b else none

inductive CopyCtrl : Type
  | cw (pos : ℕ)
  | cm (pos : ℕ)
  | ch (pos : ℕ)

instance : Inhabited CopyCtrl := ⟨.cw 0⟩

def copyMachineTable : Turing.TM0.Machine (Tracks 2) CopyCtrl
  | .cw pos, sym =>
      match sym 0 with
      | some b => some (.cm pos, .write fun t => if t.val = 1 then some b else sym t)
      | none => some (.ch pos, .write sym)
  | .cm pos, _ => some (.cw (pos + 1), .move Turing.Dir.right)
  | .ch 0, _ => none
  | .ch (pos + 1), _ => some (.ch pos, .move Turing.Dir.left)

def copyAccept : CopyCtrl → Bool := fun _ => true

inductive ResetCtrl : Type
  | rw (pos : ℕ)
  | rm (pos : ℕ)
  | rh (pos : ℕ)

instance : Inhabited ResetCtrl := ⟨.rw 0⟩

def resetMachineTable : Turing.TM0.Machine (Tracks 2) ResetCtrl
  | .rw pos, sym =>
      match sym 0 with
      | some _ => some (.rm pos, .write fun t => if t.val = 1 then none else sym t)
      | none => some (.rh pos, .write sym)
  | .rm pos, _ => some (.rw (pos + 1), .move Turing.Dir.right)
  | .rh 0, _ => none
  | .rh (pos + 1), _ => some (.rh pos, .move Turing.Dir.left)

def resetAccept : ResetCtrl → Bool := fun _ => true

def twoTrackBitEncode (input : List Bool) : List (Tracks 2) := tracksEncode 2 input

def bothTrackEncode (input : List Bool) : List (Tracks 2) :=
  input.map fun b _ => some b

def inputWindow (l : List (Tracks 2)) : ℕ :=
  (l.takeWhile fun s => (s 0).isSome).length

def resetWindowList (l : List (Tracks 2)) : List (Tracks 2) :=
  ((l.take (inputWindow l)).map (fun s t => if t.val = 1 then none else s t) : List (Tracks 2))
    ++ l.drop (inputWindow l)

def ScratchWithinHeadReach (s : ℕ) (T : Turing.Tape (Tracks 2)) : Prop :=
  ∀ i : ℤ, T.nth i 1 ≠ none → |i| ≤ s

def dirShift (off : ℤ) : Turing.Dir → ℤ
  | Turing.Dir.left => off - 1
  | Turing.Dir.right => off + 1

def runTrackIdx (r : ℕ) (j : Fin (2 * r + 1)) : Fin (2 * r + 2) :=
  ⟨j.val + 1, by omega⟩

inductive MajCtrl (Q r : ℕ) : Type
  | copyW (j : Fin (2 * r + 1)) (tally pos : ℕ)
  | copyM (j : Fin (2 * r + 1)) (tally pos : ℕ)
  | copyHome (j : Fin (2 * r + 1)) (tally pos : ℕ)
  | simQ (j : Fin (2 * r + 1)) (q : Fin (Q + 1)) (tally : ℕ) (off : ℤ)
  | tallyH (j : Fin (2 * r + 1)) (tally : ℕ) (bit : Bool) (off : ℤ)
  | finalH (tally : ℕ)

instance {Q r : ℕ} : Inhabited (MajCtrl Q r) := ⟨.copyW ⟨0, by omega⟩ 0 0⟩

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

def majorityAcceptBit (r tally : ℕ) : Bool :=
  MajorityBit fun i : Fin (2 * r + 1) => i.val < tally

def majorityAccept (Q r : ℕ) : MajCtrl Q r → Bool
  | .finalH tally => majorityAcceptBit r tally
  | _ => true

def majorityCoinMachine (Q r : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (Tracks (2 * r + 2)) (MajCtrl Q r) :=
  majorityTable Q r M acceptM

def majorityEncode (r : ℕ) (input : List Bool) : List (Tracks (2 * r + 2)) :=
  tracksEncode (2 * r + 2) input

def majorityBudget (r n T : ℕ) : ℕ := (2 * r + 1) * (4 * n + 2 * T + 8) + 2

def majorityPolyBound (r c k n : ℕ) : ℕ :=
  (2 * r + 1) * (4 * c + 12) * (n + 1) ^ (k + 1) + (2 * r + 1) * (4 * c + 12)

inductive TM2Stack : Type
  | input
  | work
  | aux
  deriving DecidableEq

abbrev tm2StackΓ : TM2Stack → Type := fun _ => Bool

inductive TM2CopyLabel : Type
  | transfer
  | restore

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

def tm2InitCopy (input : List Bool) :
    Turing.TM2.Cfg tm2StackΓ TM2CopyLabel (Option Bool) :=
  ⟨some .transfer, none, fun k =>
    match k with
    | TM2Stack.input => input
    | _ => []⟩

inductive TM2ResetLabel : Type
  | clear

def tm2Reset : TM2ResetLabel → Turing.TM2.Stmt tm2StackΓ TM2ResetLabel (Option Bool)
  | .clear =>
      .pop TM2Stack.work (fun _ o => o)
        (.branch (fun v => v.isNone) .halt (.goto fun _ => .clear))

def tm2InitReset (input work : List Bool) :
    Turing.TM2.Cfg tm2StackΓ TM2ResetLabel (Option Bool) :=
  ⟨some .clear, none, fun k =>
    match k with
    | TM2Stack.input => input
    | TM2Stack.work => work
    | _ => []⟩

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

def standardBitEncode (input : List Bool) : List (Option Bool) := input.map some

def delimitedPairEncode (input : List Bool) : List (Bool × Bool) :=
  (input.map fun b => (b, false)) ++ [(false, true)]

inductive OrRunCtrl : Type
  | read1
  | read2 (b : Bool)
  | outC (v : Bool)

instance : Inhabited OrRunCtrl := ⟨.read1⟩

def orRunTable : Bool → Turing.TM0.Machine (Tracks 2) OrRunCtrl
  | c, .read1, sym => some (.read2 c, .write sym)
  | c, .read2 b, sym => some (.outC (b || c), .write sym)
  | _, .outC _, _ => none

def orRunAccept : OrRunCtrl → Bool
  | .outC v => v
  | _ => true

inductive NaiveCtrl (r : ℕ) : Type
  | read1
  | read2 (b : Bool)
  | settle (v : Bool)
  | fake (j : ℕ) (v : Bool) (half : Bool)
  | outC (v : Bool)

instance {r : ℕ} : Inhabited (NaiveCtrl r) := ⟨.read1⟩

def naiveBudget (r : ℕ) : ℕ := 4 * r + 3

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

def naiveMajorityAccept (r : ℕ) : NaiveCtrl r → Bool
  | .outC v => v
  | _ => true

end Qatlib.Concepts.ClassicalTape.TapeCompilation
