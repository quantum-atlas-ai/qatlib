/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilistic
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Data.List.GetD
import Qatlib.Concepts.ClassicalTape.TapeBoundary

/-!
# Finite-tape majority compilation vocabulary

This module defines concrete encodings and transition tables for finite-control probabilistic
tape machines and their majority-vote compilation. `Code`, `encodeMachine`, and `table`
represent machines by lists of natural numbers, while `coinConfigRunAux` records stopped
configurations and resource counts. The computational background is described in
[KitaevShenVyalyi2002].

Marked input and work tracks support copying, erasing, source execution, and return scans.
`roundsTable` organizes repeated trials on separate work tracks, `bitSimTable` represents
multitrack transitions over optional Boolean symbols, and `rawMajorityCode` combines input
expansion with an odd number of trials. The module also defines finite coin-word equivalences,
majority masses, and natural-number formulas for control labels and transition rows.

## Main definitions

* `commonHalt` and `totalAt`: shared stopping locations and termination on all coin words of a
  fixed length.
* `prepareHomingCoinTable`: input copying followed by work execution and a return scan.
* `independentMajorityMass`: the uniform mass of a target majority outcome over separate coin
  blocks.
* `encodedMajorityCode` and `rawMajorityCode`: majority-machine codes for block-encoded and
  ordinary Boolean inputs.
* `encodedMajorityRowNat`: a natural-number transition-row formula for the block-encoded
  majority construction.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

open scoped BigOperators Classical

/-- The outcome of a finite coin-driven run, recording an optional stopped configuration, the
number of coin reads, and the number of completed transitions. -/
structure CoinRunResult (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where
  stopped : Option (Turing.TM0.Cfg Γ Λ)
  reads : ℕ
  transitions : ℕ

/-- Run a coin-indexed machine from a configuration using a finite list of coin bits, recording
any detected stopping configuration together with coin reads and completed transitions. -/
def coinConfigRunAux {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    List Bool → Turing.TM0.Cfg Γ Λ → CoinRunResult Γ Λ
  | [], cfg => if coinHalt M cfg then ⟨some cfg, 0, 0⟩ else ⟨none, 0, 0⟩
  | c :: cs, cfg =>
    if coinHalt M cfg then ⟨some cfg, 0, 0⟩ else
      match Turing.TM0.step (M c) cfg with
      | none => ⟨some cfg, 1, 0⟩
      | some next =>
        let r := coinConfigRunAux M cs next
        ⟨r.stopped, r.reads + 1, r.transitions + 1⟩

/-- A finite list of natural numbers encoding a control bound, Boolean readouts, and two
transition tables. -/
abbrev Code := List ℕ

/-- Read the control bound from the first entry of `code`, defaulting to zero; the associated
control labels lie in `Fin (controlSize code + 1)`. -/
def controlSize (code : Code) : ℕ := code.getD 0 0

/-- Encode the blank symbol, `some false`, and `some true` by the natural numbers zero, one, and
two, respectively. -/
def symbolIndex : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- Decode zero as blank and one as `some false`, and decode every larger natural number as
`some true`. -/
def decodeSymbol (n : ℕ) : Option Bool :=
  match n with
  | 0 => none
  | 1 => some false
  | _ => some true

/-- Encode left and right moves by zero and one, and writes of blank, false, and true by two,
three, and four. -/
def actionIndex : Turing.TM0.Stmt (Option Bool) → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write none => 2
  | .write (some false) => 3
  | .write (some true) => 4

/-- Decode a natural number modulo five as a left move, right move, or write of one of the three
tape symbols. -/
def decodeAction (n : ℕ) : Turing.TM0.Stmt (Option Bool) :=
  match n % 5 with
  | 0 => .move .left
  | 1 => .move .right
  | 2 => .write none
  | 3 => .write (some false)
  | _ => .write (some true)

/-- Encode a missing transition by zero and a transition to `q` with statement `stmt` by `5 *
q.val + actionIndex stmt + 1`. -/
def encodeTransition {Q : ℕ} :
    Option (Fin (Q + 1) × Turing.TM0.Stmt (Option Bool)) → ℕ
  | none => 0
  | some (q, stmt) => 5 * q.val + actionIndex stmt + 1

/-- Decode zero as a missing transition; for a positive record, decode its action modulo five
and its target label modulo `Q + 1`. -/
def decodeTransition (Q n : ℕ) :
    Option (Fin (Q + 1) × Turing.TM0.Stmt (Option Bool)) :=
  match n with
  | 0 => none
  | n + 1 => some (⟨n / 5 % (Q + 1), Nat.mod_lt _ (by omega)⟩, decodeAction n)

/-- Flatten a coin bit, a control label, and a tape symbol into the row index for the two
transition tables with control bound `Q`. -/
def rowIndex (Q : ℕ) (c : Bool) (q : Fin (Q + 1)) (a : Option Bool) : ℕ :=
  (c.toNat * (Q + 1) + q.val) * 3 + symbolIndex a

/-- Decode the transition table selected by `coin` from a machine code, treating missing list
entries as zero transition records. -/
def table (code : Code) (coin : Bool) :
    Turing.TM0.Machine (Option Bool) (Fin (controlSize code + 1)) := fun q a =>
  decodeTransition (controlSize code)
    (code.getD (1 + (controlSize code + 1) + rowIndex (controlSize code) coin q a) 0)

/-- Read the Boolean output associated with a control label from `code`, interpreting an odd
entry as true and a missing entry as false. -/
def readout (code : Code) (q : Fin (controlSize code + 1)) : Bool :=
  code.getD (1 + q.val) 0 % 2 == 1

/-- Require the two coin-selected transition tables to have exactly the same missing transitions
at every control label and tape symbol. -/
def commonHalt (code : Code) : Prop :=
  ∀ q a, (table code false q a = none) ↔ (table code true q a = none)

/-- Require the coded machine on `input` to return a Boolean result for every supplied coin word
of length `t`. -/
def totalAt (code : Code) (input : List Bool) (t : ℕ) : Prop :=
  ∀ ω : Fin t → Bool,
    (coinTapeRun (table code) (readout code) (input.map some) (List.ofFn ω)).1 ≠ none

/-- Encode a machine with control labels in `Fin (Q + 1)` by listing its control bound, Boolean
readouts, and all coin-indexed transition records. -/
def encodeMachine (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) : Code :=
  Q :: (List.ofFn (fun q : Fin (Q + 1) => (a q).toNat) ++
    List.ofFn (fun i : Fin (6 * (Q + 1)) =>
      encodeTransition (M (decide (3 * (Q + 1) ≤ i.val))
        ⟨i.val / 3 % (Q + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (i.val % 3)))))

/-- Transport a coin-selected transition table along an equivalence of control labels, applying
the equivalence to both current and successor labels. -/
def relabelTable {Γ Λ Λ' : Type*} [Inhabited Λ] [Inhabited Λ'] (e : Λ ≃ Λ')
    (M : Bool → Turing.TM0.Machine Γ Λ) (c : Bool) : Turing.TM0.Machine Γ Λ' :=
  fun q a => (M c (e.symm q) a).map fun p => (e p.1, p.2)

/-- Transport the control label of a configuration along `e` while retaining its tape. -/
def relabelCfg {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ'] (e : Λ ≃ Λ')
    (cfg : Turing.TM0.Cfg Γ Λ) : Turing.TM0.Cfg Γ Λ' := ⟨e cfg.q, cfg.Tape⟩

/-- A pair of counters bounded by `N`, used to record the number of processed coin bits and the
number of true bits. -/
abbrev TallyState (N : ℕ) := Fin (N + 1) × Fin (N + 1)

/-- Increment the step counter and add the coin bit's natural-number value to the true-bit
counter, saturating at `N` and preserving the scanned symbol; halt when the step counter
reaches `N`. -/
def tallyTable (N : ℕ) (coin : Bool) :
    Turing.TM0.Machine (Option Bool) (TallyState N) := fun q a =>
  if h : q.1.val < N then
    some ((⟨q.1.val + 1, by omega⟩,
      ⟨min N (q.2.val + coin.toNat), by omega⟩), .write a)
  else none

/-- Return true precisely when the tally state's true-bit counter is strictly greater than `N /
2`. -/
def tallyAccept (N : ℕ) (q : TallyState N) : Bool := decide (N / 2 < q.2.val)

/-- Count the true bits in a finite Boolean list by summing their natural-number values. -/
def trueCount (coins : List Bool) : ℕ := (coins.map Bool.toNat).sum

/-- The empty Boolean list contains zero true bits. -/
@[simp] theorem trueCount_nil : trueCount [] = 0 := rfl

/-- The true-bit count of `c :: cs` is the natural-number value of `c` plus the true-bit count
of `cs`. -/
@[simp] theorem trueCount_cons (c : Bool) (cs : List Bool) :
    trueCount (c :: cs) = c.toNat + trueCount cs := rfl

/-- Identify the two bounded tally counters with a single control label in `Fin (N * (N + 2) +
1)`. -/
def tallyLabels (N : ℕ) : TallyState N ≃ Fin (N * (N + 2) + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- Relabel the coin-counting transition table using the finite control labels supplied by
`tallyLabels`. -/
def nativeTallyTable (N : ℕ) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (N * (N + 2) + 1)) :=
  relabelTable (tallyLabels N) (tallyTable N)

/-- Evaluate the strict-majority tally readout after decoding a native control label with
`tallyLabels`. -/
def nativeTallyAccept (N : ℕ) (q : Fin (N * (N + 2) + 1)) : Bool :=
  tallyAccept N ((tallyLabels N).symm q)

/-- Encode the finite-control tally machine and its strict-majority readout as a natural-number
list. -/
def tallyCode (N : ℕ) : Code :=
  encodeMachine (N * (N + 2)) (nativeTallyTable N) (nativeTallyAccept N)

/-- A tape cell containing an optional input bit, an optional work bit, and a Boolean home
marker. -/
abbrev MarkerCell := Option Bool × Option Bool × Bool

/-- Copy the input component of a marked cell into its work component while preserving the input
and home marker. -/
def fillCell (s : MarkerCell) : MarkerCell := (s.1, s.1, s.2.2)

/-- A five-state machine that marks its starting cell, copies consecutive nonblank input
components to the work track, and scans left back to a marked cell. -/
def markerCopyTable : Turing.TM0.Machine MarkerCell (Fin 5) := fun q s =>
  match q.val with
  | 0 => some (1, .write (s.1, s.2.1, true))
  | 1 => if s.1.isSome then some (2, .write (fillCell s)) else some (3, .write s)
  | 2 => some (1, .move .right)
  | 3 => if s.2.2 then some (4, .write s) else some (3, .move .left)
  | _ => none

/-- Accept exactly control label four, the terminal label of the marker-copy machine. -/
def markerCopyAccept (q : Fin 5) : Bool := q == 4

/-- Embed a Boolean input list into marked cells with blank work components and false home
markers. -/
def markerInput (input : List Bool) : List MarkerCell :=
  input.map fun b => (some b, none, false)

/-- Construct the tape with the input copied into both input and work components and the initial
head cell marked as home. -/
def markerCopyResult (input : List Bool) : Turing.Tape MarkerCell :=
  let T := Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))
  T.write (T.head.1, T.head.2.1, true)

/-- Replace the work component of a marked cell by blank while preserving its input component
and home marker. -/
def eraseCell (s : MarkerCell) : MarkerCell := (s.1, none, s.2.2)

/-- A five-state machine that marks its starting cell, erases work components along consecutive
nonblank input cells, and scans left back to a marked cell. -/
def markerResetTable : Turing.TM0.Machine MarkerCell (Fin 5) := fun q s =>
  match q.val with
  | 0 => some (1, .write (s.1, s.2.1, true))
  | 1 => if s.1.isSome then some (2, .write (eraseCell s)) else some (3, .write s)
  | 2 => some (1, .move .right)
  | 3 => if s.2.2 then some (4, .write s) else some (3, .move .left)
  | _ => none

/-- Accept exactly control label four, the terminal label of the marker-reset machine. -/
def markerResetAccept (q : Fin 5) : Bool := q == 4

/-- Embed input bits with specified optional work bits into marked cells whose home markers are
false. -/
def markerResetInput (input : List (Bool × Option Bool)) : List MarkerCell :=
  input.map fun p => (some p.1, p.2, false)

/-- Construct the tape retaining the supplied input bits, blanking all work components, and
marking the initial head cell as home. -/
def markerResetResult (input : List (Bool × Option Bool)) : Turing.Tape MarkerCell :=
  let T := Turing.Tape.mk₁ (input.map fun p => (some p.1, none, false))
  T.write (T.head.1, T.head.2.1, true)

/-- Map the control label of a configuration by `f` without changing its tape. -/
def mapCfg {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (f : Λ → Μ) (cfg : Turing.TM0.Cfg Γ Λ) : Turing.TM0.Cfg Γ Μ := ⟨f cfg.q, cfg.Tape⟩

/-- Sequence two machines on a sum of their control types, switching to the default state of the
second machine when the first has no transition. -/
def sequenceTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (M₂ : Turing.TM0.Machine Γ Μ) :
    Turing.TM0.Machine Γ (Sum Λ Μ) := fun q a =>
  match q with
  | .inl q => match M₁ q a with
    | none => some (.inr default, .write a)
    | some (q', stmt) => some (.inl q', stmt)
  | .inr q => (M₂ q a).map fun p => (.inr p.1, p.2)

/-- Sequence the two coin-selected machines by applying `sequenceTable` separately for each coin
bit. -/
def sequenceCoinTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ) :
    Bool → Turing.TM0.Machine Γ (Sum Λ Μ) := fun c => sequenceTable (M₁ c) (M₂ c)

/-- Identify the disjoint union of the five copy states and five reset states with `Fin 10`. -/
def markerCopyResetLabels : Sum (Fin 5) (Fin 5) ≃ Fin 10 := finSumFinEquiv

/-- Relabel the sequential composition of the marker-copy and marker-reset machines as a machine
with ten control labels. -/
def markerCopyResetTable : Turing.TM0.Machine MarkerCell (Fin 10) :=
  relabelTable markerCopyResetLabels (fun _ => sequenceTable markerCopyTable markerResetTable) false

/-- Return false in the copy phase and use the marker-reset readout in the reset phase. -/
def markerCopyResetAccept (q : Fin 10) : Bool :=
  match markerCopyResetLabels.symm q with
  | .inl _ => false
  | .inr q => markerResetAccept q

/-- Construct the marked input tape with blank work components by applying `markerResetResult`
to the input with initially blank work bits. -/
def markerErasedResult (input : List Bool) : Turing.Tape MarkerCell :=
  markerResetResult (input.map fun b => (b, none))

/-- The blank-preserving projection from a marked cell to its optional work bit. -/
def workMap : Turing.PointedMap MarkerCell (Option Bool) := ⟨fun s => s.2.1, rfl⟩

/-- Project a marked-tape configuration to its work tape while preserving the control label. -/
def workCfg {Λ : Type*} [Inhabited Λ] (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    Turing.TM0.Cfg (Option Bool) Λ := ⟨cfg.q, cfg.Tape.map workMap⟩

/-- Lift a coin-selected machine to the work component of marked cells, preserving input
components and home markers during writes. -/
def liftWorkTable {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) :
    Turing.TM0.Machine MarkerCell Λ := fun q s =>
  (M c q s.2.1).map fun p =>
    match p.2 with
    | .move d => (p.1, .move d)
    | .write b => (p.1, .write (s.1, b, s.2.2))

/-- Identify the sum of five preparation states and `Q + 1` source states with `Fin (Q + 6)`. -/
def prepareLabels (Q : ℕ) : Sum (Fin 5) (Fin (Q + 1)) ≃ Fin (Q + 6) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Compose marker-based input copying with execution of the source machine on the work track,
using native finite control labels. -/
def prepareCoinTable (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) :
    Bool → Turing.TM0.Machine MarkerCell (Fin (Q + 6)) :=
  relabelTable (prepareLabels Q) (sequenceCoinTable (fun _ => markerCopyTable) (liftWorkTable M))

/-- Return false in the first summand of a control type and apply the supplied readout in the
second summand. -/
def sourcePhaseAccept {Λ Μ : Type*} (a : Μ → Bool) : Sum Λ Μ → Bool
  | .inl _ => false
  | .inr q => a q

/-- Decode a preparation-machine control label and apply the source readout only in the
source-execution phase. -/
def prepareAccept (Q : ℕ) (a : Fin (Q + 1) → Bool) (q : Fin (Q + 6)) : Bool :=
  sourcePhaseAccept a ((prepareLabels Q).symm q)

/-- Concatenation as an equivalence between a pair of Boolean words of lengths `k` and `m` and a
word of length `k + m`. -/
def appendCoinWords (k m : ℕ) :
    ((Fin k → Bool) × (Fin m → Bool)) ≃ (Fin (k + m) → Bool) where
  toFun p := Fin.append p.1 p.2
  invFun w := (fun i => w (i.castAdd m), fun i => w (i.natAdd k))
  left_inv p := by
    obtain ⟨u, v⟩ := p
    apply Prod.ext
    · funext i
      exact Fin.append_left' u v i
    · funext i
      exact Fin.append_right u v i
  right_inv w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left' (fun j => w (j.castAdd m)) (fun j => w (j.natAdd k)) j
    · exact Fin.append_right (fun j => w (j.castAdd m)) (fun j => w (j.natAdd k)) j

/-- Prepending a Boolean bit as an equivalence between a bit paired with a length-`t` word and a
word of length `t + 1`. -/
def consCoinWords (t : ℕ) : (Bool × (Fin t → Bool)) ≃ (Fin (t + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by obtain ⟨b, w⟩ := p; rfl
  right_inv w := Fin.cons_self_tail w

/-- Concatenate preparation coins, one handoff coin, and `t` source coins into a single word of
length `(3 * input.length + 3) + (t + 1)`. -/
def prepareCoinWords (input : List Bool) (t : ℕ) :
    ((Fin (3 * input.length + 3) → Bool) × Bool × (Fin t → Bool)) ≃
      (Fin ((3 * input.length + 3) + (t + 1)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (consCoinWords t)).trans
    (appendCoinWords (3 * input.length + 3) (t + 1))

/-- Reshape a Boolean word of length `N * t` into `N` indexed Boolean words of length `t`. -/
def freshBlocks (N t : ℕ) : (Fin (N * t) → Bool) ≃ (Fin N → Fin t → Bool) :=
  (Equiv.arrowCongr (finProdFinEquiv (m := N) (n := t)).symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin N) (Fin t) Bool)

/-- The uniform mass of coin-block assignments whose majority vote equals `target` across `2 * r
+ 1` runs of length `t`. A run votes true exactly when its result is `some true`. -/
noncomputable def independentMajorityMass {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t r : ℕ) (target : Bool) : ℝ :=
  (∑ ω : Fin (2 * r + 1) → Fin t → Bool,
    if (MajorityBit fun j =>
        (coinTapeRun M a input (List.ofFn (ω j))).1 == some true) = target
      then (1 : ℝ) else 0) / 2 ^ (t * (2 * r + 1))

/-- A pair of Boolean flags storing the side of home and the output bit to retain during the
return scan. -/
abbrev HomeState := Bool × Bool

/-- Choose a right move when the side flag is true and a left move otherwise. -/
def homeDirection (left : Bool) : Turing.Dir := if left then .right else .left

/-- Scan in the direction selected by the stored side flag until a cell with a true home marker
is encountered. -/
def markerHomeTable : Turing.TM0.Machine MarkerCell HomeState := fun q s =>
  if s.2.2 then none else some (q, .move (homeDirection q.1))

/-- Read the stored output bit from a homing state. -/
def markerHomeAccept (q : HomeState) : Bool := q.2

/-- Represent a distance `n` as the negative integer `-n` for the left side and as `n`
otherwise. -/
def homeDistance (left : Bool) (n : ℕ) : ℤ := if left then -(n : ℤ) else n

/-- Require the home marker of a tape to be true exactly at relative position `-off`. -/
def HomeAt (T : Turing.Tape MarkerCell) (off : ℤ) : Prop :=
  ∀ i : ℤ, (T.nth i).2.2 = decide (i + off = 0)

/-- Require the side flag to be true for negative offsets and false for positive offsets,
leaving the flag unrestricted at offset zero. -/
def SideAt (left : Bool) (off : ℤ) : Prop :=
  (off < 0 → left = true) ∧ (0 < off → left = false)

/-- Update the side flag when departing a home-marked cell, recording true for a left move and
false for a right move. -/
def sideAfterMove (old atHome : Bool) : Turing.Dir → Bool
  | .left => if atHome then true else old
  | .right => if atHome then false else old

/-- Run the source machine on a marked tape's work component while tracking which side of home
contains the head. -/
def sideWorkTable {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) :
    Turing.TM0.Machine MarkerCell (Λ × Bool) := fun q s =>
  (M c q.1 s.2.1).map fun p => match p.2 with
    | .move d => ((p.1, sideAfterMove q.2 s.2.2 d), .move d)
    | .write b => ((p.1, q.2), .write (s.1, b, s.2.2))

/-- Project a side-tracking marked-tape configuration to the source control label and work tape. -/
def sideWorkCfg {Λ : Type*} [Inhabited Λ] (cfg : Turing.TM0.Cfg MarkerCell (Λ × Bool)) :
    Turing.TM0.Cfg (Option Bool) Λ := ⟨cfg.q.1, cfg.Tape.map workMap⟩

/-- Sequence two machines, selecting the second machine's initial state with `next` when the
first machine has no transition. -/
def dispatchTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (next : Λ → Μ) (M₂ : Turing.TM0.Machine Γ Μ) :
    Turing.TM0.Machine Γ (Sum Λ Μ) := fun q a =>
  match q with
  | .inl q => match M₁ q a with
    | none => some (.inr (next q), .write a)
    | some (q', stmt) => some (.inl q', stmt)
  | .inr q => (M₂ q a).map fun p => (.inr p.1, p.2)

/-- Apply state-dependent sequential dispatch to each pair of coin-selected transition tables. -/
def dispatchCoinTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (next : Λ → Μ)
    (M₂ : Bool → Turing.TM0.Machine Γ Μ) :
    Bool → Turing.TM0.Machine Γ (Sum Λ Μ) := fun c => dispatchTable (M₁ c) next (M₂ c)

/-- Compose side-tracking work execution with a return scan whose state retains the final source
readout and side flag. -/
def homingCoinTable {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) :
    Bool → Turing.TM0.Machine MarkerCell (Sum (Λ × Bool) HomeState) :=
  dispatchCoinTable (sideWorkTable M) (fun q => (q.2, a q.1)) (fun _ => markerHomeTable)

/-- Return false during work execution and return the stored output bit during the homing phase. -/
def homingAccept {Λ : Type*} : Sum (Λ × Bool) HomeState → Bool
  | .inl _ => false
  | .inr q => q.2

/-- Identify the source states with side flags and the four homing states with `Fin (2 * Q +
6)`. -/
def homingLabels (Q : ℕ) :
    Sum (Fin (Q + 1) × Bool) HomeState ≃ Fin (2 * Q + 6) :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv |>.sumCongr
    ((Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))

/-- Relabel the side-tracking work machine followed by its home scan using `Fin (2 * Q + 6)`. -/
def nativeHomingCoinTable (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine MarkerCell (Fin (2 * Q + 6)) :=
  relabelTable (homingLabels Q) (homingCoinTable M a)

/-- Evaluate the homing readout after decoding a native homing control label. -/
def nativeHomingAccept (Q : ℕ) : Fin (2 * Q + 6) → Bool :=
  fun q => homingAccept ((homingLabels Q).symm q)

/-- Identify five copy states together with the native homing states with `Fin (2 * Q + 11)`. -/
def prepareHomingLabels (Q : ℕ) : Sum (Fin 5) (Fin (2 * Q + 6)) ≃ Fin (2 * Q + 11) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- Compose input copying with source execution and a home scan, using native control labels in
`Fin (2 * Q + 11)`. -/
def prepareHomingCoinTable (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine MarkerCell (Fin (2 * Q + 11)) :=
  relabelTable (prepareHomingLabels Q)
    (sequenceCoinTable (fun _ => markerCopyTable) (nativeHomingCoinTable Q M a))

/-- Return false in the copying phase and use the native homing readout in the subsequent phase. -/
def prepareHomingAccept (Q : ℕ) (q : Fin (2 * Q + 11)) : Bool :=
  sourcePhaseAccept (nativeHomingAccept Q) ((prepareHomingLabels Q).symm q)

/-- Concatenate coin words for copying, handoff, source execution, and homing into a single
Boolean word with the specified total length. -/
def homingCoinWords (input : List Bool) (t : ℕ) :
    ((Fin (3 * input.length + 3) → Bool) × Bool ×
      ((Fin t → Bool) × (Fin (t + 1) → Bool))) ≃
      (Fin ((3 * input.length + 3) + ((t + (t + 1)) + 1)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl Bool) (appendCoinWords t (t + 1)))).trans
    (prepareCoinWords input (t + (t + 1)))

/-- Require the current input component at each relative position `i` to match the initial input
component at `i + off`. -/
def InputAt (initial current : Turing.Tape MarkerCell) (off : ℤ) : Prop :=
  ∀ i : ℤ, (current.nth i).1 = (initial.nth (i + off)).1

/-- Require both a unique home marker at offset `-off` and preservation of the initial input
component under the same offset. -/
def ProtectedAt (initial current : Turing.Tape MarkerCell) (off : ℤ) : Prop :=
  HomeAt current off ∧ InputAt initial current off

/-- A tape cell containing an optional input bit, `N` optional work bits, and a Boolean home
marker. -/
abbrev TrackCell (N : ℕ) := Option Bool × (Fin N → Option Bool) × Bool

/-- Project a multitrack cell to its input component, work track `j`, and home marker as a
blank-preserving map. -/
def focusTrack {N : ℕ} (j : Fin N) : Turing.PointedMap (TrackCell N) MarkerCell :=
  ⟨fun s => (s.1, s.2.1 j, s.2.2), rfl⟩

/-- Replace the shared input component, work track `j`, and home marker with those of `b`,
preserving the other work tracks. -/
def writeTrack {N : ℕ} (j : Fin N) (s : TrackCell N) (b : MarkerCell) : TrackCell N :=
  (b.1, Function.update s.2.1 j b.2.1, b.2.2)

/-- Lift a marked-cell machine to work track `j` of a multitrack tape, routing each write
through `writeTrack`. -/
def trackTable {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (c : Bool) :
    Turing.TM0.Machine (TrackCell N) Λ := fun q s =>
  (M c q (focusTrack j s)).map fun p =>
    match p.2 with
    | .move d => (p.1, .move d)
    | .write b => (p.1, .write (writeTrack j s b))

/-- Project a multitrack configuration to work track `j` together with the shared input and home
components, retaining its control label. -/
def focusTrackCfg {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (cfg : Turing.TM0.Cfg (TrackCell N) Λ) : Turing.TM0.Cfg MarkerCell Λ :=
  ⟨cfg.q, cfg.Tape.map (focusTrack j)⟩

/-- Embed a Boolean input into multitrack cells with all work tracks blank and all home markers
false. -/
def tracksInput (N : ℕ) (input : List Bool) : List (TrackCell N) :=
  input.map fun b => (some b, fun _ => none, false)

/-- Require work track `j` to be blank at every integer position of the tape. -/
def BlankTrack {N : ℕ} (j : Fin N) (T : Turing.Tape (TrackCell N)) : Prop :=
  ∀ i : ℤ, (T.nth i).2.1 j = none

/-- Run the copy, source-execution, and homing construction on work track `j` of a multitrack
tape. -/
def trackRoundTable {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (TrackCell N) (Fin (2 * Q + 11)) :=
  trackTable j (prepareHomingCoinTable Q M a)

/-- Construct the marked-cell input tape with blank work components and set its initial head
cell's home marker to true. -/
def markedInputTape (input : List Bool) : Turing.Tape MarkerCell :=
  let T := Turing.Tape.mk₁ (markerInput input)
  T.write (T.head.1, T.head.2.1, true)

/-- The state of repeated trials, consisting of a bounded round counter, a bounded acceptance
counter, and a preparation-and-homing control label. -/
abbrev RoundsState (N Q : ℕ) := Fin (N + 1) × Fin (N + 1) × Fin (2 * Q + 11)

/-- Increment a bounded natural-number label, saturating at `N`. -/
def boundedSucc (N : ℕ) (q : Fin (N + 1)) : Fin (N + 1) :=
  ⟨min (q.val + 1) N, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Advance the round counter, increment the acceptance counter when the current
preparation-and-homing readout is true, and reset the local program label to zero. -/
def roundsNext (N Q : ℕ) (q : RoundsState N Q) : RoundsState N Q :=
  (boundedSucc N q.1,
    (if prepareHomingAccept Q q.2.2 then boundedSucc N q.2.1 else q.2.1), 0)

/-- Execute successive preparation-and-homing trials on work tracks indexed by the round
counter, updating the counters between trials and halting when the round counter reaches
`N`. -/
def roundsTable (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (c : Bool) : Turing.TM0.Machine (TrackCell N) (RoundsState N Q) := fun q s =>
  if hj : q.1.val < N then
    match trackRoundTable ⟨q.1.val, hj⟩ Q M a c q.2.2 s with
    | none => some (roundsNext N Q q, .write s)
    | some (next, stmt) => some ((q.1, q.2.1, next), stmt)
  else none

/-- Return true precisely when the stored acceptance count is strictly greater than `N / 2`. -/
def roundsAccept (N Q : ℕ) (q : RoundsState N Q) : Bool := decide (N / 2 < q.2.1.val)

/-- The number of product states in `RoundsState N Q` minus one, used as the bound for native
control labels. -/
def roundsControlMax (N Q : ℕ) : ℕ := (N + 1) * ((N + 1) * (2 * Q + 11)) - 1

/-- Flatten a repeated-trial state into a native control label in `Fin (roundsControlMax N Q +
1)`. -/
def roundsLabels (N Q : ℕ) : RoundsState N Q ≃ Fin (roundsControlMax N Q + 1) :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by
      have h : 0 < (N + 1) * ((N + 1) * (2 * Q + 11)) :=
        Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
      unfold roundsControlMax
      omega))

/-- Relabel the multitrack repeated-trial transition table using the finite labels supplied by
`roundsLabels`. -/
def nativeRoundsTable (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (TrackCell N) (Fin (roundsControlMax N Q + 1)) :=
  relabelTable (roundsLabels N Q) (roundsTable N Q M a)

/-- Evaluate the strict-majority repeated-trial readout after decoding a native control label. -/
def nativeRoundsAccept (N Q : ℕ) : Fin (roundsControlMax N Q + 1) → Bool :=
  fun q => roundsAccept N Q ((roundsLabels N Q).symm q)

/-- Extend a trial configuration with a round counter and acceptance counter while preserving
its tape and local program label. -/
def roundsCfg {N Q : ℕ} (j count : Fin (N + 1))
    (cfg : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11))) :
    Turing.TM0.Cfg (TrackCell N) (RoundsState N Q) := ⟨(j, count, cfg.q), cfg.Tape⟩

/-- Evaluate `g` on the stopped configuration of a run result, assigning zero when no stopped
configuration is recorded. -/
noncomputable def stoppedValue {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (g : Turing.TM0.Cfg Γ Λ → ℝ) (r : CoinRunResult Γ Λ) : ℝ := r.stopped.elim 0 g

/-- Average `stoppedValue g` over all Boolean coin words of length `n` for runs beginning at
`cfg`. -/
noncomputable def fairCfgValue {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (g : Turing.TM0.Cfg Γ Λ → ℝ)
    (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) : ℝ :=
  (∑ w : Fin n → Bool, stoppedValue g (coinConfigRunAux M (List.ofFn w) cfg)) / 2 ^ n

/-- Apply one machine step for each supplied coin bit, returning the final configuration if all
steps succeed and `none` otherwise. -/
def coinStepsAux {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    List Bool → Turing.TM0.Cfg Γ Λ → Option (Turing.TM0.Cfg Γ Λ)
  | [], cfg => some cfg
  | c :: cs, cfg => (Turing.TM0.step (M c) cfg).bind (coinStepsAux M cs)

/-- Recursively sum false-vote and true-vote branches with weights `pfalse` and `ptrue`,
starting from `count` and testing the strict-majority threshold after `fuel` further votes. -/
noncomputable def remainingVoteMass (N : ℕ) (pfalse ptrue : ℝ) (target : Bool) : ℕ → ℕ → ℝ
  | 0, count => if decide (N / 2 < count) = target then 1 else 0
  | fuel + 1, count =>
      pfalse * remainingVoteMass N pfalse ptrue target fuel count +
      ptrue * remainingVoteMass N pfalse ptrue target fuel (count + 1)

/-- Count length-`fuel` words in the finite trial space whose true-vote count, added to `count`,
yields the target majority outcome, and divide by `(Fintype.card I : ℝ) ^ fuel. -/
noncomputable def uniformVotesMass {I : Type*} [Fintype I] (N : ℕ) (vote : I → Bool)
    (target : Bool) (fuel count : ℕ) : ℝ :=
  (∑ w : Fin fuel → I,
    if decide (N / 2 < count + trueCount (List.ofFn fun j => vote (w j))) = target then (1 : ℝ) else 0) /
      (Fintype.card I : ℝ) ^ fuel

/-- Prepending a trial as an equivalence between an element paired with a length-`n` trial word
and a word of length `n + 1`. -/
def consTrials (I : Type*) (n : ℕ) : (I × (Fin n → I)) ≃ (Fin (n + 1) → I) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by obtain ⟨x, w⟩ := p; rfl
  right_inv w := Fin.cons_self_tail w

/-- Encode a multitrack cell as its input bit, `N` work bits, a home-marker symbol, and a final
blank separator. -/
def bitBlock (N : ℕ) (s : TrackCell N) : List (Option Bool) :=
  s.1 :: (List.ofFn s.2.1 ++ [if s.2.2 then some true else none, none])

/-- Insert `N + 2` blank symbols after each Boolean input bit. -/
def expandedInput (N : ℕ) (input : List Bool) : List (Option Bool) :=
  input.flatMap fun b => some b :: List.replicate (N + 2) none

/-- A queue of `N + 2` optional Boolean symbols used by the input-expansion machine. -/
abbrev ExpandQueue (N : ℕ) := Fin (N + 2) → Option Bool

/-- Discard the first queue entry, shift the remaining entries forward, and append `s` at the
end. -/
def expandQueuePush {N : ℕ} (q : ExpandQueue N) (s : Option Bool) : ExpandQueue N :=
  Fin.snoc (Fin.tail q) s

/-- The input-expansion control state, consisting of one of twelve phases, a first-block flag, a
bounded position, and a symbol queue. -/
abbrev ExpandState (N : ℕ) := Fin 12 × Bool × Fin (N + 3) × ExpandQueue N

/-- Define the input-expansion transition table using phases for gathering symbols, shifting
queued input, inserting blank slots, and scanning back toward the start. -/
def expandInputTable (N : ℕ) : Turing.TM0.Machine (Option Bool) (ExpandState N) := fun q s =>
  let phase := q.1
  let first := q.2.1
  let i := q.2.2.1
  let fifo := q.2.2.2
  match phase.val with
  | 0 => if s.isSome then some ((1, true, 0, fun _ => none), .move .right) else none
  | 1 => if hi : i.val < N + 2 then
      some ((2, first, i, Function.update fifo ⟨i.val, hi⟩ s),
        .write (if first && decide (i.val = N) then some true else none)) else none
  | 2 => if hi : i.val + 1 < N + 2 then
      some ((1, first, ⟨i.val + 1, by omega⟩, fifo), .move .right)
    else some ((3, first, 0, fifo), .move .right)
  | 3 => if (∀ k, fifo k = none) ∧ s = none then
      some ((5, first, 0, fifo), .move .left)
    else some ((4, first, 0, expandQueuePush fifo s), .write (fifo 0))
  | 4 => some ((3, first, 0, fifo), .move .right)
  | 5 => if s.isSome then some ((5, first, 0, fifo), .move .left)
    else some ((6, false, 0, fifo), .move .right)
  | 6 => if s.isSome then some ((1, false, 0, fun _ => none), .move .right)
    else some ((7, false, 0, fifo), .move .left)
  | 7 => some ((8, false, 0, fifo), .move .left)
  | 8 => if s = some true then some ((10, false, ⟨N + 1, by omega⟩, fifo), .write none)
    else some ((9, false, ⟨N + 2, by omega⟩, fifo), .move .left)
  | 9 => if 1 < i.val then some ((9, false, ⟨i.val - 1, by omega⟩, fifo), .move .left)
    else some ((8, false, 0, fifo), .move .left)
  | 10 => if 1 < i.val then some ((10, false, ⟨i.val - 1, by omega⟩, fifo), .move .left)
    else some ((11, false, 0, fifo), .move .left)
  | _ => none

/-- Read a window of `N + 2` input symbols beginning at index `k`, supplying blanks beyond the
end of `raw`. -/
def expandWindow (N : ℕ) (raw : List Bool) (k : ℕ) : ExpandQueue N :=
  fun i => (raw.map some).getD (k + i.val) none

/-- Construct the shifting-phase tape with the reversed consumed raw prefix and processed prefix
on the left, and the suffix after the buffered window on the right. -/
def expandShiftTape (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) (k : ℕ) :
    Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.mk (((raw.map some).take k).reverse ++ pre.reverse))
    (Turing.ListBlank.mk ((raw.map some).drop (N + 2 + k)))

/-- Construct a phase-three expansion configuration from the current raw-input window and its
shifting-phase tape. -/
def expandShiftCfg (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (k : ℕ) :
    Turing.TM0.Cfg (Option Bool) (ExpandState N) :=
  ⟨(3, first, 0, expandWindow N raw k), expandShiftTape N pre raw k⟩

/-- Construct `N + 2` inserted symbols, all blank except for a true marker at index `N` when
`first` is true. -/
def insertSlots (N : ℕ) (first : Bool) : List (Option Bool) :=
  List.ofFn fun i : Fin (N + 2) => if first && decide (i.val = N) then some true else none

/-- Buffer the first `i` symbols of `raw` within the expansion queue, assigning blank to later
queue entries and out-of-range input indices. -/
def expandCapture (N : ℕ) (raw : List Bool) (i : ℕ) : ExpandQueue N :=
  fun j => if j.val < i then (raw.map some).getD j.val none else none

/-- Construct the gathering-phase tape with the first `i` inserted slots on the left and the raw
input suffix starting at `i` on the right. -/
def expandGatherTape (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (i : ℕ) :
    Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.mk (((insertSlots N first).take i).reverse ++ pre.reverse))
    (Turing.ListBlank.mk ((raw.map some).drop i))

/-- Construct a gathering configuration with its captured prefix, selecting phase one before all
slots are gathered and phase three afterward. -/
def expandGatherCfg (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (i : Fin (N + 3)) :
    Turing.TM0.Cfg (Option Bool) (ExpandState N) :=
  ⟨(if i.val < N + 2 then 1 else 3, first, if i.val < N + 2 then i else 0, expandCapture N raw i.val),
    expandGatherTape N first pre raw i.val⟩

/-- Construct a phase-six expansion configuration at the boundary between the processed prefix
and the remaining raw input, with an empty queue. -/
def expandCheckCfg (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) :
    Turing.TM0.Cfg (Option Bool) (ExpandState N) :=
  ⟨(6, false, 0, fun _ => none),
    Turing.Tape.mk' (Turing.ListBlank.mk pre.reverse) (Turing.ListBlank.mk (raw.map some))⟩

/-- Define the processing-time recurrence for input expansion, adding `2 * (N + 2) + 3 * n + 3`
when passing from length `n` to length `n + 1`. -/
def expandProcessTime (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (N + 2) + 3 * n + 3 + expandProcessTime N n

/-- Construct an expanded input whose first block carries the temporary true marker and whose
remaining blocks contain only inserted blanks. -/
def markedExpandedInput (N : ℕ) (b : Bool) (raw : List Bool) : List (Option Bool) :=
  (some b :: insertSlots N true) ++ expandedInput N raw

/-- Identify blank, false, and true tape symbols with the three elements of `Fin 3`. -/
def optionBoolFin : Option Bool ≃ Fin 3 where
  toFun s := ⟨symbolIndex s, by cases s with
    | none => decide
    | some b => cases b <;> decide⟩
  invFun i := decodeSymbol i.val
  left_inv s := by cases s with
    | none => rfl
    | some b => cases b <;> rfl
  right_inv := by decide

/-- Encode a queue of `N + 2` ternary symbols as a label in `Fin (3 ^ (N + 2))`. -/
def expandQueueLabels (N : ℕ) : ExpandQueue N ≃ Fin (3 ^ (N + 2)) :=
  (Equiv.piCongrRight fun _ => optionBoolFin).trans finFunctionFinEquiv

/-- The number of input-expansion states minus one, accounting for twelve phases, two
first-block flags, bounded positions, and ternary queues. -/
def expandControlMax (N : ℕ) : ℕ := 12 * (2 * ((N + 3) * 3 ^ (N + 2))) - 1

/-- Flatten the components of an input-expansion state into a finite control label bounded by
`expandControlMax N`. -/
def expandLabels (N : ℕ) : ExpandState N ≃ Fin (expandControlMax N + 1) :=
  ((Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr finTwoEquiv.symm
      ((Equiv.prodCongr (Equiv.refl _) (expandQueueLabels N)).trans finProdFinEquiv)).trans finProdFinEquiv)).trans
        finProdFinEquiv).trans (finCongr (by
          have h : 0 < 12 * (2 * ((N + 3) * 3 ^ (N + 2))) :=
            Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (pow_pos (by decide) _)))
          unfold expandControlMax
          omega))

/-- Relabel the input-expansion machine using its native finite control labels. -/
def nativeExpandTable (N : ℕ) : Turing.TM0.Machine (Option Bool) (Fin (expandControlMax N + 1)) :=
  relabelTable (expandLabels N) (fun _ => expandInputTable N) false

/-- Encode the input-expansion machine as a coin-independent machine code with every Boolean
readout set to false. -/
def expandCode (N : ℕ) : Code :=
  encodeMachine (expandControlMax N) (fun _ => nativeExpandTable N) (fun _ => false)

/-- Move the head of the tape initialized from `l` to the right exactly `n` times. -/
def tapeAt (l : List (Option Bool)) (n : ℕ) : Turing.Tape (Option Bool) :=
  (Turing.Tape.move .right)^[n] (Turing.Tape.mk₁ l)

/-- Define the expansion-time budget, using zero for empty input and the processing recurrence
plus the return-scan distance for nonempty input. -/
def expandTime (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => expandProcessTime N (n + 1) + (n + 1) * (N + 3) + 1

/-- Expand a half-tape into optional Boolean blocks, reversing each block when `rev` is true to
accommodate the left-half orientation. -/
def bitHalf (N : ℕ) (rev : Bool) (l : Turing.ListBlank (TrackCell N)) :
    Turing.ListBlank (Option Bool) := by
  apply Turing.ListBlank.flatMap l (fun s => if rev then (bitBlock N s).reverse else bitBlock N s)
  refine ⟨N + 3, ?_⟩
  have hd : bitBlock N default = List.replicate (N + 3) none := by
    change none :: (List.ofFn (fun _ : Fin N => (none : Option Bool)) ++ List.replicate 2 none) =
      none :: List.replicate (N + 2) none
    rw [List.ofFn_const, ← List.replicate_add]
  simp only [hd, List.reverse_replicate, ite_self]
  rfl

/-- Encode a multitrack tape as blocks of optional Boolean symbols, placing the head at the
first symbol of the current cell's block. -/
def bitTape (N : ℕ) (T : Turing.Tape (TrackCell N)) : Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (bitHalf N true T.left)
    (Turing.ListBlank.append (bitBlock N T.head) (bitHalf N false T.right))

/-- A buffer of `N + 2` optional Boolean symbols representing the input, work bits, and home
component of a multitrack cell. -/
abbrev BitBuffer (N : ℕ) := Fin (N + 2) → Option Bool

/-- Encode a multitrack cell's input and work components in a buffer, using `some true` for a
true home marker and blank otherwise. -/
def cellBuffer (N : ℕ) (s : TrackCell N) : BitBuffer N :=
  Fin.cons s.1 (Fin.snoc s.2.1 (if s.2.2 then some true else none))

/-- Decode a buffer into a multitrack cell, interpreting its final entry as a true home marker
exactly when that entry is `some true`. -/
def bufferCell (N : ℕ) (f : BitBuffer N) : TrackCell N :=
  (f 0, fun j => f j.castSucc.succ, f (Fin.last (N + 1)) == some true)

/-- The block simulator's control state, consisting of one of nine phases, a source label, a
bounded position counter, and a cell buffer. -/
abbrev BitSimState (N : ℕ) (Λ : Type*) := Fin 9 × Λ × Fin (3 * (N + 2) + 1) × BitBuffer N

/-- Define the optional-Boolean transition table that simulates multitrack transitions through
phases for fetching a cell, executing a source transition, moving between blocks, and
writing a block. -/
def bitSimTable {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) :
    Bool → Turing.TM0.Machine (Option Bool) (BitSimState N Λ) := fun coin q s =>
  let phase := q.1
  let wide := q.2.1
  let i := q.2.2.1
  let buf := q.2.2.2
  match phase.val with
  | 0 => if hi : i.val < N + 2 then
      some ((if i.val + 1 < N + 2 then 0 else 1, wide,
        if i.val + 1 < N + 2 then ⟨i.val + 1, by omega⟩ else ⟨N + 2, by omega⟩,
        Function.update buf ⟨i.val, hi⟩ s), .move .right)
    else none
  | 1 => if 0 < i.val then
      some ((if 1 < i.val then 1 else 2, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else 0, buf), .move .left)
    else none
  | 2 => match M coin wide (bufferCell N buf) with
    | none => none
    | some (next, .move .left) => some ((3, next, ⟨N + 3, by omega⟩, buf), .write s)
    | some (next, .move .right) => some ((4, next, ⟨N + 3, by omega⟩, buf), .write s)
    | some (next, .write v) => some ((5, next, 0, cellBuffer N v), .write s)
  | 3 => if 0 < i.val then
      some ((if 1 < i.val then 3 else 6, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else ⟨2 * (N + 2) - 1, by omega⟩, buf), .move .left)
    else none
  | 4 => if 0 < i.val then
      some ((if 1 < i.val then 4 else 6, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else ⟨2 * (N + 2) - 1, by omega⟩, buf), .move .right)
    else none
  | 5 => if hi : i.val < N + 2 then some ((7, wide, i, buf), .write (buf ⟨i.val, hi⟩)) else none
  | 6 => if 0 < i.val then
      some ((if 1 < i.val then 6 else 0, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else 0,
        if 1 < i.val then buf else fun _ => none), .write s)
    else none
  | 7 => if hi : i.val + 1 < N + 2 then
      some ((5, wide, ⟨i.val + 1, by omega⟩, buf), .move .right)
    else some ((8, wide, ⟨N + 2, by omega⟩, buf), .move .right)
  | 8 => if 0 < i.val then
      some ((if 1 < i.val then 8 else 0, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else 0,
        if 1 < i.val then buf else fun _ => none), .move .left)
    else none
  | _ => none

/-- Encode a source configuration at the simulator's execution phase, with the current
multitrack cell buffered and its tape expanded into blocks. -/
def bitReady {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    Turing.TM0.Cfg (Option Bool) (BitSimState N Λ) :=
  ⟨(2, cfg.q, 0, cellBuffer N cfg.Tape.head), bitTape N cfg.Tape⟩

/-- Read the `N + 2` tape symbols at nonnegative offsets from the current head into a buffer. -/
def tapeBuffer (N : ℕ) (T : Turing.Tape (Option Bool)) : BitBuffer N :=
  fun j => T.nth (j.val : ℤ)

/-- Read tape symbols at offsets below `i` into a buffer and fill its remaining entries with
blanks. -/
def bitCapture (N : ℕ) (T : Turing.Tape (Option Bool)) (i : ℕ) : BitBuffer N :=
  fun j => if j.val < i then T.nth (j.val : ℤ) else none

/-- Construct a simulator configuration after fetching `i` buffer positions, with the tape head
shifted right by `i` and the phase selected by whether fetching is complete. -/
def bitFetchCfg {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ) (q : Λ) (T : Turing.Tape (Option Bool))
    (i : Fin (N + 3)) : Turing.TM0.Cfg (Option Bool) (BitSimState N Λ) :=
  ⟨(if i.val < N + 2 then 0 else 1, q, ⟨i.val, by have := i.isLt; omega⟩, bitCapture N T i.val),
    (Turing.Tape.move .right)^[i.val] T⟩

/-- Construct the intermediate tape after replacing the first `i` entries of `old` by entries of
`new`, with the head between the replaced prefix and remaining suffix. -/
def bitWriteTape (N : ℕ) (new old : BitBuffer N) (L R : Turing.ListBlank (Option Bool)) (i : ℕ) :
    Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.append ((List.ofFn new).take i).reverse L)
    (Turing.ListBlank.append ((List.ofFn old).drop i) R)

/-- Construct the simulator's intermediate write configuration, switching from the write phase
to the return phase once all buffer entries have been written. -/
def bitWriteCfg {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ) (q : Λ) (new old : BitBuffer N)
    (L R : Turing.ListBlank (Option Bool)) (i : Fin (N + 3)) :
    Turing.TM0.Cfg (Option Bool) (BitSimState N Λ) :=
  ⟨(if i.val < N + 2 then 5 else 8, q,
    if i.val < N + 2 then ⟨i.val, by have := i.isLt; omega⟩ else ⟨N + 2, by omega⟩, new),
    bitWriteTape N new old L R i.val⟩

/-- The number of block-simulator states minus one for `Q + 1` source labels, nine phases,
bounded positions, and ternary buffers. -/
def bitSimControlMax (N Q : ℕ) : ℕ :=
  9 * ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) - 1

/-- Flatten a block-simulator state into a finite control label bounded by `bitSimControlMax N
Q`. -/
def bitSimLabels (N Q : ℕ) : BitSimState N (Fin (Q + 1)) ≃ Fin (bitSimControlMax N Q + 1) :=
  ((Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodCongr (Equiv.refl _) (expandQueueLabels N)).trans finProdFinEquiv)).trans
        finProdFinEquiv)).trans finProdFinEquiv).trans (finCongr (by
          have h : 0 < 9 * ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) :=
            Nat.mul_pos (by decide) (Nat.mul_pos (by omega)
              (Nat.mul_pos (by omega) (pow_pos (by decide) _)))
          unfold bitSimControlMax
          omega))

/-- Relabel the optional-Boolean block simulator using native finite control labels bounded by
`bitSimControlMax N Q`. -/
def nativeBitSimTable (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (bitSimControlMax N Q + 1)) :=
  relabelTable (bitSimLabels N Q) (bitSimTable N M)

/-- Decode a native block-simulator control label and apply `a` to its stored source label. -/
def nativeBitSimAccept (N Q : ℕ) (a : Fin (Q + 1) → Bool)
    (q : Fin (bitSimControlMax N Q + 1)) : Bool :=
  a ((bitSimLabels N Q).symm q).2.1

/-- Encode a multitrack machine's optional-Boolean block simulator together with the readout of
its stored source label. -/
def bitSimCode (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) : Code :=
  encodeMachine (bitSimControlMax N Q) (nativeBitSimTable N Q M) (nativeBitSimAccept N Q a)

/-- The coin-block width `5 * (N + 2) + 1` used for one source transition in the
block-simulation schedule. -/
def bitMicroWidth (N : ℕ) : ℕ := 5 * (N + 2) + 1

/-- Concatenate a list of fixed-width simulator coin blocks into a single Boolean list. -/
def bitMicroCoins (N : ℕ) (blocks : List (Fin (bitMicroWidth N) → Bool)) : List Bool :=
  blocks.flatMap List.ofFn

/-- Extract the first coin bit from each simulator coin block to form the source coin list. -/
def bitSourceCoins (N : ℕ) (blocks : List (Fin (bitMicroWidth N) → Bool)) : List Bool :=
  blocks.map fun b => b ⟨0, by unfold bitMicroWidth; omega⟩

/-- Identify source coin bits paired with the remaining `5 * (N + 2)` bits per step with `t`
complete simulator coin blocks. -/
def bitSplitWords (N t : ℕ) :
    ((Fin t → Bool) × (Fin t → Fin (5 * (N + 2)) → Bool)) ≃
      (Fin t → Fin (bitMicroWidth N) → Bool) where
  toFun p j := Fin.cons (p.1 j) (p.2 j)
  invFun w := (fun j => w j ⟨0, by unfold bitMicroWidth; omega⟩, fun j => Fin.tail (w j))
  left_inv p := by
    apply Prod.ext
    · funext j
      rfl
    · funext j i
      rfl
  right_inv w := by
    funext j
    exact Fin.cons_self_tail (w j)

/-- Concatenate an initial coin word of length `2 * (N + 2)` with `t` flattened simulator coin
blocks. -/
def bitInitialWords (N t : ℕ) :
    ((Fin (2 * (N + 2)) → Bool) × (Fin t → Fin (bitMicroWidth N) → Bool)) ≃
      (Fin (2 * (N + 2) + t * bitMicroWidth N) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (freshBlocks t (bitMicroWidth N)).symm).trans
    (appendCoinWords (2 * (N + 2)) (t * bitMicroWidth N))

/-- Encode the optional-Boolean block simulation of `2 * r + 1` multitrack trials with a
strict-majority readout, for input already in block form. -/
def encodedMajorityCode (code : Code) (r : ℕ) : Code :=
  bitSimCode (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code))
    (nativeRoundsTable (2 * r + 1) (controlSize code) (table code) (readout code))
    (nativeRoundsAccept (2 * r + 1) (controlSize code))

/-- The combined control bound for input expansion followed by `next`, obtained by adding the
two control bounds and one. -/
def expandedSequenceMax (N : ℕ) (next : Code) : ℕ :=
  controlSize (expandCode N) + controlSize next + 1

/-- Identify the disjoint control labels of the expansion machine and `next` with the native
labels of their sequential composition. -/
def expandedSequenceLabels (N : ℕ) (next : Code) :
    Sum (Fin (controlSize (expandCode N) + 1)) (Fin (controlSize next + 1)) ≃
      Fin (expandedSequenceMax N next + 1) :=
  finSumFinEquiv.trans (finCongr (by unfold expandedSequenceMax; omega))

/-- Sequence the coded input-expansion machine with the machine coded by `next`, then relabel
their combined control states. -/
def expandedSequenceTable (N : ℕ) (next : Code) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (expandedSequenceMax N next + 1)) :=
  relabelTable (expandedSequenceLabels N next) (sequenceCoinTable (table (expandCode N)) (table next))

/-- Return false during input expansion and use the readout of `next` during its execution
phase. -/
def expandedSequenceAccept (N : ℕ) (next : Code) (q : Fin (expandedSequenceMax N next + 1)) : Bool :=
  sourcePhaseAccept (readout next) ((expandedSequenceLabels N next).symm q)

/-- Encode the sequential composition of input expansion and `next`, using the latter machine's
readout after the handoff. -/
def expandThenCode (N : ℕ) (next : Code) : Code :=
  encodeMachine (expandedSequenceMax N next) (expandedSequenceTable N next) (expandedSequenceAccept N next)

/-- Prepend input expansion to `encodedMajorityCode`, producing the majority-compilation code
for an ordinary Boolean input. -/
def rawMajorityCode (code : Code) (r : ℕ) : Code :=
  expandThenCode (2 * r + 1) (encodedMajorityCode code r)

/-- Concatenate expansion coins, one handoff coin, and a continuation word of length `D` into a
single word. -/
def expandThenWords (N : ℕ) (input : List Bool) (D : ℕ) :
    ((Fin (expandTime N input.length) → Bool) × Bool × (Fin D → Bool)) ≃
      (Fin (expandTime N input.length + (D + 1)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (consCoinWords D)).trans
    (appendCoinWords (expandTime N input.length) (D + 1))

/-- Form a code list by evaluating `row` at the natural-number indices from zero through `n -
1`. -/
def codeTabulate (n : ℕ) (row : ℕ → ℕ) : Code := (List.range n).map row

/-- Construct a code by listing the control bound `Q`, the first `Q + 1` Boolean outputs, and
the first `6 * (Q + 1)` transition records. -/
def codeEnumerate (Q : ℕ) (output : ℕ → Bool) (row : ℕ → ℕ) : Code :=
  Q :: (codeTabulate (Q + 1) (fun q => (output q).toNat) ++ codeTabulate (6 * (Q + 1)) row)

/-- Compute the strict-majority readout from a natural-number block-simulator label by
extracting its repeated-trial acceptance counter. -/
def bitMajorityOutputNat (N Q q : ℕ) : Bool :=
  let stride := (3 * (N + 2) + 1) * 3 ^ (N + 2)
  let wide := q % ((roundsControlMax N Q + 1) * stride) / stride
  decide (N / 2 < wide % ((N + 1) * (2 * Q + 11)) / (2 * Q + 11))

/-- Compute the readout for the raw-input majority construction from a natural-number control
label, returning false in the expansion phase. -/
def rawMajorityOutputNat (code : Code) (r q : ℕ) : Bool :=
  let N := 2 * r + 1
  let Q := controlSize code
  let exp := expandControlMax N + 1
  let bit := bitSimControlMax N (roundsControlMax N Q) + 1
  let label := q % (exp + bit)
  if label < exp then false else bitMajorityOutputNat N Q ((label - exp) % bit)

/-- Extract the base-three digit at position `i` from `label`. -/
def queueDigitNat (label i : ℕ) : ℕ := label / 3 ^ i % 3

/-- Subtract the existing base-three contribution at position `i` from `label` and add `digit *
3 ^ i`. -/
def queueUpdateNat (label i digit : ℕ) : ℕ :=
  label - queueDigitNat label i * 3 ^ i + digit * 3 ^ i

/-- Shift a base-three queue label down by one digit and insert `digit` at position `N + 1`. -/
def queuePushNat (N label digit : ℕ) : ℕ := label / 3 + digit * 3 ^ (N + 1)

/-- Combine the expansion phase, first-block flag, position, and queue label into a
natural-number control label. -/
def expandLabelNat (N phase first i fifo : ℕ) : ℕ :=
  (fifo + 3 ^ (N + 2) * i) + ((N + 3) * 3 ^ (N + 2)) * first +
    (2 * ((N + 3) * 3 ^ (N + 2))) * phase

/-- Compute the encoded optional-Boolean transition record for one expansion step from its
natural-number state components and scanned-symbol index. -/
def expandStepNat (N phase first i fifo s : ℕ) : ℕ :=
  let emit := fun phase first i fifo action => 5 * expandLabelNat N phase first i fifo + action + 1
  if phase = 0 then
    if s = 0 then 0 else emit 1 1 0 0 1
  else if phase = 1 then
    if i < N + 2 then emit 2 first i (queueUpdateNat fifo i s)
      (2 + if first = 1 ∧ i = N then 2 else 0) else 0
  else if phase = 2 then
    if i + 1 < N + 2 then emit 1 first (i + 1) fifo 1 else emit 3 first 0 fifo 1
  else if phase = 3 then
    if fifo = 0 ∧ s = 0 then emit 5 first 0 fifo 0
    else emit 4 first 0 (queuePushNat N fifo s) (2 + queueDigitNat fifo 0)
  else if phase = 4 then emit 3 first 0 fifo 1
  else if phase = 5 then
    if s = 0 then emit 6 0 0 fifo 1 else emit 5 first 0 fifo 0
  else if phase = 6 then
    if s = 0 then emit 7 0 0 fifo 0 else emit 1 0 0 0 1
  else if phase = 7 then emit 8 0 0 fifo 0
  else if phase = 8 then
    if s = 2 then emit 10 0 (N + 1) fifo 2 else emit 9 0 (N + 2) fifo 0
  else if phase = 9 then
    if 1 < i then emit 9 0 (i - 1) fifo 0 else emit 8 0 0 fifo 0
  else if phase = 10 then
    if 1 < i then emit 10 0 (i - 1) fifo 0 else emit 11 0 0 fifo 0
  else 0

/-- Decode an expansion-table row into its control components and scanned-symbol index, then
compute its transition record with `expandStepNat`. -/
def expandRowNat (N row : ℕ) : ℕ :=
  let label := row / 3 % (expandControlMax N + 1)
  let slots := 3 ^ (N + 2)
  let block := (N + 3) * slots
  let rest := label % (2 * block)
  expandStepNat N (label / (2 * block)) (rest / block)
    (rest % block / slots) (rest % block % slots) (row % 3)

/-- Preserve a zero transition record and reduce the successor label of each nonzero record
modulo `Q + 1`, retaining its action. -/
def normalizeTransitionNat (Q record : ℕ) : ℕ :=
  if record = 0 then 0 else
    5 * ((record - 1) / 5 % (Q + 1)) + (record - 1) % 5 + 1

/-- Look up and normalize a coded source transition, reducing the current label modulo `Q + 1`
and the scanned-symbol index modulo three. -/
def sourceRowNat (code : Code) (coin : Bool) (q s : ℕ) : ℕ :=
  let Q := controlSize code
  normalizeTransitionNat Q
    (code.getD (1 + (Q + 1) + (coin.toNat * (Q + 1) + q % (Q + 1)) * 3 + s % 3) 0)

/-- Compute the readout of input expansion followed by `next` from a natural-number label,
returning false on expansion states. -/
def expandThenOutputNat (N : ℕ) (next : Code) (q : ℕ) : Bool :=
  let exp := expandControlMax N + 1
  let sz := controlSize next + 1
  let label := q % (exp + sz)
  if label < exp then false else next.getD (1 + (label - exp) % sz) 0 % 2 == 1

/-- Compute a transition row for expansion followed by `next`, replacing an expansion halt by a
handoff and offsetting continuation-state labels. -/
def expandThenRowNat (N : ℕ) (next : Code) (row : ℕ) : ℕ :=
  let exp := expandControlMax N + 1
  let sz := controlSize next + 1
  let total := exp + sz
  let q := row / 3 % total
  let s := row % 3
  if q < exp then
    let record := expandRowNat N (3 * q + s)
    if record = 0 then 5 * exp + (2 + s) + 1 else record
  else
    let record := sourceRowNat next (decide (3 * total ≤ row)) (q - exp) s
    if record = 0 then 0 else 5 * exp + record

/-- Normalize a buffer's home-marker digit by preserving the value two and replacing either
other base-three digit by zero. -/
def canonicalBufferNat (N label : ℕ) : ℕ :=
  queueUpdateNat label (N + 1) (if queueDigitNat label (N + 1) = 2 then 2 else 0)

/-- Combine a simulator phase, source label, position, and ternary buffer label into a
natural-number control label. -/
def bitSimLabelNat (N Q phase wide i buffer : ℕ) : ℕ :=
  buffer + 3 ^ (N + 2) * i + ((3 * (N + 2) + 1) * 3 ^ (N + 2)) * wide +
    ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) * phase

/-- The number `3 ^ (N + 2) + 2` of action codes reserved per target state for multitrack
transition records. -/
def wideRecordStride (N : ℕ) : ℕ := 3 ^ (N + 2) + 2

/-- Encode left and right moves by zero and one, and encode a multitrack-cell write by two plus
its ternary buffer label. -/
def wideActionNat (N : ℕ) : Turing.TM0.Stmt (TrackCell N) → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write v => 2 + (expandQueueLabels N (cellBuffer N v)).val

/-- Encode a missing multitrack transition by zero and a present transition using its target
label, `wideRecordStride`, and `wideActionNat`. -/
def wideRecordNat (N : ℕ) {Q : ℕ} :
    Option (Fin (Q + 1) × Turing.TM0.Stmt (TrackCell N)) → ℕ
  | none => 0
  | some (q, action) => wideRecordStride N * q.val + wideActionNat N action + 1

/-- Compute a block-simulator transition record from natural-number state components, a
scanned-symbol index, and an encoded multitrack source transition. -/
def bitSimStepNat (N Q phase wide i buffer symbol record : ℕ) : ℕ :=
  let L := N + 2
  let emit :=
      fun phase wide i buffer action => 5 * bitSimLabelNat N Q phase wide i buffer + action + 1
  if phase = 0 then
    if i < L then emit (if i + 1 < L then 0 else 1) wide
      (if i + 1 < L then i + 1 else L) (queueUpdateNat buffer i symbol) 1 else 0
  else if phase = 1 then
    if 0 < i then emit (if 1 < i then 1 else 2) wide (if 1 < i then i - 1 else 0) buffer 0 else 0
  else if phase = 2 then
    if record = 0 then 0 else
      let next := (record - 1) / wideRecordStride N
      let action := (record - 1) % wideRecordStride N
      if action = 0 then emit 3 next (N + 3) buffer (2 + symbol)
      else if action = 1 then emit 4 next (N + 3) buffer (2 + symbol)
      else emit 5 next 0 (action - 2) (2 + symbol)
  else if phase = 3 then
    if 0 < i then emit (if 1 < i then 3 else 6) wide
      (if 1 < i then i - 1 else 2 * L - 1) buffer 0 else 0
  else if phase = 4 then
    if 0 < i then emit (if 1 < i then 4 else 6) wide
      (if 1 < i then i - 1 else 2 * L - 1) buffer 1 else 0
  else if phase = 5 then
    if i < L then emit 7 wide i buffer (2 + queueDigitNat buffer i) else 0
  else if phase = 6 then
    if 0 < i then emit (if 1 < i then 6 else 0) wide
      (if 1 < i then i - 1 else 0) (if 1 < i then buffer else 0) (2 + symbol) else 0
  else if phase = 7 then
    if i + 1 < L then emit 5 wide (i + 1) buffer 1 else emit 8 wide L buffer 1
  else if phase = 8 then
    if 0 < i then emit (if 1 < i then 8 else 0) wide
      (if 1 < i then i - 1 else 0) (if 1 < i then buffer else 0) 0 else 0
  else 0

/-- Evaluate a multitrack source table after reducing and decoding its natural-number state and
buffer labels, then encode the resulting transition. -/
def wideTableNat (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (coin : Bool) (wide buffer : ℕ) : ℕ :=
  wideRecordNat N (M coin ⟨wide % (Q + 1), Nat.mod_lt _ (by omega)⟩
    (bufferCell N ((expandQueueLabels N).symm
      ⟨buffer % 3 ^ (N + 2), Nat.mod_lt _ (pow_pos (by decide) _)⟩)))

/-- Decode a block-simulator row and compute its transition record using `source` to supply the
coin-selected multitrack transition record. -/
def bitSimRowNat (N Q : ℕ) (source : Bool → ℕ → ℕ → ℕ) (row : ℕ) : ℕ :=
  let label := row / 3 % (bitSimControlMax N Q + 1)
  let P := 3 ^ (N + 2)
  let stride := (3 * (N + 2) + 1) * P
  let full := (Q + 1) * stride
  let rest := label % full
  let wide := rest / stride
  let index := rest % stride / P
  let buffer := rest % stride % P
  bitSimStepNat N Q (label / full) wide index buffer (row % 3)
    (source (decide (3 * (bitSimControlMax N Q + 1) ≤ row)) wide buffer)

/-- Update the input digit, work-track digit `j + 1`, and home-marker digit of a ternary cell
buffer. -/
def trackWriteBufferNat (N j buffer input work home : ℕ) : ℕ :=
  queueUpdateNat (queueUpdateNat (queueUpdateNat buffer 0 input) (j + 1) work)
    (N + 1) home

/-- Combine a round counter, acceptance counter, and local program label into a natural-number
repeated-trial label. -/
def roundsLabelNat (N Q round count prog : ℕ) : ℕ :=
  prog + (2 * Q + 11) * count + ((N + 1) * (2 * Q + 11)) * round

/-- Compute the multitrack transition record for a single copy, source-execution, and homing
trial on work track `j` from natural-number labels. -/
def trackRoundRowNat (N j : ℕ) (code : Code) (coin : Bool) (prog buffer : ℕ) : ℕ :=
  let Q := controlSize code
  let buf := canonicalBufferNat N buffer
  let input := queueDigitNat buf 0
  let work := queueDigitNat buf (j + 1)
  let home := queueDigitNat buf (N + 1)
  let emit := fun target action => wideRecordStride N * target + action + 1
  let write := fun input work home => 2 + trackWriteBufferNat N j buf input work home
  let same := 2 + buf
  if prog = 0 then emit 1 (write input work 2)
  else if prog = 1 then if input = 0 then emit 3 same else emit 2 (write input input home)
  else if prog = 2 then emit 1 1
  else if prog = 3 then if home = 2 then emit 4 same else emit 3 0
  else if prog = 4 then emit 5 same
  else
    let h := prog - 5
    let base := 2 * (Q + 1)
    if h < base then
      let source := h / 2
      let side := h % 2
      let record := sourceRowNat code coin source work
      if record = 0 then
        let output := (code.getD (1 + source) 0 % 2 == 1).toNat
        emit (5 + (base + (output + 2 * side))) same
      else
        let next := (record - 1) / 5
        let action := (record - 1) % 5
        if action = 0 then emit (5 + ((if home = 2 then 1 else side) + 2 * next)) 0
        else if action = 1 then emit (5 + ((if home = 2 then 0 else side) + 2 * next)) 1
        else emit (5 + (side + 2 * next)) (write input (action - 2) home)
    else if home = 2 then 0
    else emit prog (if (h - base) / 2 = 1 then 1 else 0)

/-- Return true exactly when `prog` lies in the homing range and its offset from `5 + 2 * (Q +
1)` is odd. -/
def prepareHomingOutputNat (Q prog : ℕ) : Bool :=
  decide (5 + 2 * (Q + 1) ≤ prog) && ((prog - (5 + 2 * (Q + 1))) % 2 == 1)

/-- Compute a repeated-trial transition record, advancing counters and resetting the local
program when a trial halts, and returning zero once the round counter reaches `N`. -/
def roundsStepNat (N : ℕ) (code : Code) (coin : Bool) (round count prog buffer : ℕ) : ℕ :=
  let Q := controlSize code
  let emit := fun target action => wideRecordStride N * target + action + 1
  if round < N then
    let record := trackRoundRowNat N round code coin prog buffer
    if record = 0 then
      let nextCount := if prepareHomingOutputNat Q prog then min (count + 1) N else count
      emit (roundsLabelNat N Q (min (round + 1) N) nextCount 0) (2 + canonicalBufferNat N buffer)
    else
      emit (roundsLabelNat N Q round count ((record - 1) / wideRecordStride N))
        ((record - 1) % wideRecordStride N)
  else 0

/-- Reduce and decode a repeated-trial label and buffer label, then compute the corresponding
coin-selected multitrack transition record. -/
def roundsRowNat (N : ℕ) (code : Code) (coin : Bool) (wide buffer : ℕ) : ℕ :=
  let Q := controlSize code
  let label := wide % (roundsControlMax N Q + 1)
  let size := 2 * Q + 11
  let rest := label % ((N + 1) * size)
  roundsStepNat N code coin (label / ((N + 1) * size)) (rest / size) (rest % size)
    (buffer % 3 ^ (N + 2))

/-- Compute the block-encoded majority readout for `2 * r + 1` trials after reducing the
natural-number control label to the simulator's range. -/
def encodedMajorityOutputNat (code : Code) (r q : ℕ) : Bool :=
  let N := 2 * r + 1
  let Q := controlSize code
  bitMajorityOutputNat N Q (q % (bitSimControlMax N (roundsControlMax N Q) + 1))

/-- Compute a transition row of the block-encoded majority construction by combining the
repeated-trial row function with the block-simulator row function. -/
def encodedMajorityRowNat (code : Code) (r row : ℕ) : ℕ :=
  let N := 2 * r + 1
  bitSimRowNat N (roundsControlMax N (controlSize code)) (roundsRowNat N code) row

end Qatlib.Concepts.ClassicalTape.TapeCompilation
