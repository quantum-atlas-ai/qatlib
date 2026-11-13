/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.FiniteTapeMajority
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilistic
import Mathlib.Computability.Partrec

/-!
# Copy–run–reset compilation of coin-tape machines

This module constructs `tmCopyRunResetCompile`, a finite-table compiler for Boolean coin-tape
machines. Its four-track alphabet `CellCore` retains input, stores work symbols, marks home, and
records visited cells. The dispatch machine copies the input, simulates the source on the work
track, returns home, and erases the work and visitation tracks while preserving the source
result bit. Classical machine encodings and effective simulation provide the background; see
[KitaevShenVyalyi2002].

The simulation lemmas track absolute head offsets and marked intervals. They give exact phase
costs and a uniform bound `tmCopyRunResetCoinBudget n m = 6 * n + 15 * m + 16` for reads,
transitions, and the stated workspace envelope on executions built from fully consumed halting
source words. The numeric compiler is primitive recursive.

## Main statements

* `phaseCopyRunReset`: correctness and tape invariants of the separate phases.
* `tmCopyRunResetCompile_run`: correctness of the encoded compiled execution.
* `tmCopyRunResetCompile_coinBudget_bound`: a bound on reads and transitions.
* `tmCopyRunResetCompile_workspace_bound`: confinement of busy cells along every execution
  prefix.
* `primrec_tmCopyRunResetCompile`: primitive recursiveness of the compiler.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler

open Qatlib.Concepts.ClassicalTape.TapeBoundary

/-- The four tape tracks recording input, work symbols, the home marker, and visitation marks. -/
abbrev CellCore := Option Bool × Option Bool × Bool × Option Bool

instance : Inhabited CellCore := ⟨(none, none, false, none)⟩

/-- Write the work symbol `b` into the current cell and mark it as visited, preserving its input
and home marker. -/
def markCell (T : Turing.Tape CellCore) (b : Option Bool) : CellCore :=
  (T.head.1, b, T.head.2.2.1, some true)

/-- Project a phase cell onto its input, work, and home-marker tracks. -/
def phaseMarker (s : CellCore) : MarkerCell := (s.1, s.2.1, s.2.2.1)

/-- The blank-preserving projection from phase cells to marker cells. -/
def phaseMarkerMap : Turing.PointedMap CellCore MarkerCell := ⟨phaseMarker, rfl⟩

/-- Project the tape of a phase configuration onto the marker tracks, preserving its control
state. -/
def phaseMarkerCfg {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg CellCore Λ) :
    Turing.TM0.Cfg MarkerCell Λ := ⟨cfg.q, cfg.Tape.map phaseMarkerMap⟩

/-- Embed a marker cell into the phase alphabet with an empty visitation track. -/
def phaseEmbed (s : MarkerCell) : CellCore := (s.1, s.2.1, s.2.2, none)

/-- The blank-preserving embedding of marker cells into phase cells. -/
def phaseEmbedMap : Turing.PointedMap MarkerCell CellCore := ⟨phaseEmbed, rfl⟩

/-- Embed a marker configuration into the phase alphabet, preserving its control state. -/
def phaseEmbedCfg {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    Turing.TM0.Cfg CellCore Λ := ⟨cfg.q, cfg.Tape.map phaseEmbedMap⟩

/-- Projecting an embedded marker cell recovers the original cell. -/
theorem phaseMarker_phaseEmbed (s : MarkerCell) : phaseMarker (phaseEmbed s) = s := rfl

/-- Lift a coin-indexed marker machine to phase cells while preserving visitation marks on
writes. -/
def liftMarkerTable {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (c : Bool) :
    Turing.TM0.Machine CellCore Λ := fun q s =>
  (M c q (phaseMarker s)).map fun p =>
    match p.2 with
    | .move d => (p.1, Turing.TM0.Stmt.move d)
    | .write b => (p.1, Turing.TM0.Stmt.write (b.1, b.2.1, b.2.2, s.2.2.2))

/-- One step of the lifted marker machine commutes with embedding configurations. -/
theorem liftMarker_step {Λ : Type} [Inhabited Λ] (M : Turing.TM0.Machine MarkerCell Λ)
    (c : Bool) (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    Turing.TM0.step (liftMarkerTable (fun _ => M) c) (phaseEmbedCfg cfg) =
      (Turing.TM0.step M cfg).map phaseEmbedCfg := by
  obtain ⟨q, T⟩ := cfg
  simp only [TM0_step_apply, liftMarkerTable, phaseEmbedCfg, Turing.Tape.map_fst,
    phaseEmbedMap, phaseMarker_phaseEmbed]
  cases M q T.head with
  | none => rfl
  | some p =>
    obtain ⟨q', stmt⟩ := p
    cases stmt with
    | move d =>
      simp only [Option.map_some, TM0StmtApply, phaseEmbedCfg, Turing.Tape.map_move]
      rfl
    | write b =>
      simp only [Option.map_some, TM0StmtApply, phaseEmbedCfg, Turing.Tape.map_write,
        phaseEmbedMap, phaseEmbed]

/-- Running the lifted marker machine for `t` steps commutes with embedding configurations. -/
theorem liftMarker_runFrom {Λ : Type} [Inhabited Λ] (M : Turing.TM0.Machine MarkerCell Λ)
    (t : ℕ) (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => M) false) t (phaseEmbedCfg cfg) =
      (Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M t cfg).map phaseEmbedCfg := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 = 1 + t by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, liftMarker_step]
    cases hs : Turing.TM0.step M cfg with
    | none => simp
    | some next =>
      simp only [Option.bind_some, Option.map_some]
      exact ih next

/-- The blank-preserving projection onto the work track of a phase cell. -/
def phaseWorkMap : Turing.PointedMap CellCore (Option Bool) := ⟨fun s => s.2.1, rfl⟩

/-- Project a phase configuration onto its work tape, preserving its control state. -/
def phaseWorkCfg {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg CellCore Λ) :
    Turing.TM0.Cfg (Option Bool) Λ := ⟨cfg.q, cfg.Tape.map phaseWorkMap⟩

/-- Encode a Boolean input on the input track with blank work and visitation tracks and no home
markers. -/
def phaseInput (input : List Bool) : List CellCore :=
  input.map fun b => (some b, none, false, none)

/-- The tape obtained by embedding the marker-copy output in the phase alphabet. -/
def phaseCopyResult (input : List Bool) : Turing.Tape CellCore :=
  (markerCopyResult input).map phaseEmbedMap

/-- Initializing the phase input agrees with embedding the initialized marker input. -/
theorem phaseCopy_init (input : List Bool) :
    Turing.TM0.init (phaseInput input) =
      phaseEmbedCfg ((Turing.TM0.init (markerInput input) :
        Turing.TM0.Cfg MarkerCell (Fin 5))) := by
  have hmap : List.map (fun b => (some b, none, false, none)) input
      = List.map (fun x => phaseEmbed (some x, none, false)) input :=
    List.map_congr_left fun x _ => rfl
  simp [Turing.TM0.init, phaseInput, phaseEmbedCfg, phaseEmbedMap, markerInput,
    Turing.Tape.map_mk₁, Function.comp_def, hmap]

/-- The lifted copy machine reaches `phaseCopyResult input` and halts after `3 * input.length +
3` steps. -/
theorem phaseCopy_run (input : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => markerCopyTable) false)
        (3 * input.length + 3) (Turing.TM0.init (phaseInput input)) =
      some ⟨4, phaseCopyResult input⟩ ∧
    Turing.TM0.step (liftMarkerTable (fun _ => markerCopyTable) false)
        ⟨4, phaseCopyResult input⟩ = none := by
  have h := markerCopy_run input
  have h1 : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => markerCopyTable) false)
      (3 * input.length + 3) (Turing.TM0.init (phaseInput input)) =
      some ⟨4, phaseCopyResult input⟩ := by
    rw [phaseCopy_init, liftMarker_runFrom, h.1]
    rfl
  refine ⟨h1, ?_⟩
  have hs := liftMarker_step markerCopyTable false ⟨4, markerCopyResult input⟩
  rw [h.2] at hs
  have hcfg : (⟨4, phaseCopyResult input⟩ : Turing.TM0.Cfg CellCore (Fin 5)) =
      phaseEmbedCfg ⟨4, markerCopyResult input⟩ := rfl
  rw [hcfg]
  simpa using! hs

/-- With enough coins, the lifted copy machine returns `true` with exactly `3 * input.length +
3` reads and transitions. -/
theorem phaseCopy_coin_run (input : List Bool) (coins : List Bool)
    (hlen : 3 * input.length + 3 ≤ coins.length) :
    coinTapeRun (fun _ => liftMarkerTable (fun _ => markerCopyTable) false) markerCopyAccept
        (phaseInput input) coins = (some true, 3 * input.length + 3) ∧
    coinTapeTransitionCount (fun _ => liftMarkerTable (fun _ => markerCopyTable) false)
        (phaseInput input) coins = 3 * input.length + 3 := by
  have h := runFrom_coin_constant (liftMarkerTable (fun _ => markerCopyTable) false)
    markerCopyAccept (3 * input.length + 3) (Turing.TM0.init (phaseInput input))
    ⟨4, phaseCopyResult input⟩ coins (phaseCopy_run input).1 (phaseCopy_run input).2 hlen
  simpa [coinTapeRun, coinTapeTransitionCount, markerCopyAccept] using! h

/-- A source control label paired with the Boolean recording the side of the home position. -/
abbrev MarkRunLabel (Λ : Type*) := Λ × Bool

/-- A pending marked-run label carrying an optional tape movement. -/
abbrev MarkPendingLabel (Λ : Type*) := (Λ × Bool) × Option Turing.Dir

/-- Control states for the live, pending, and final stages of the marked simulation. -/
abbrev MarkRunControl (Λ : Type*) :=
  Sum (MarkRunLabel Λ) (Sum (MarkPendingLabel Λ) (MarkRunLabel Λ))

instance {Λ : Type} [Inhabited Λ] : Inhabited (MarkRunControl Λ) :=
  ⟨Sum.inl (default, false)⟩

/-- Simulate source transitions on the work track, marking visited cells and staging movements
through pending states. -/
def markRunTable {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) :
    Turing.TM0.Machine CellCore (MarkRunControl Λ) :=
  fun q s =>
    match q with
    | .inl p =>
      match M c p.1 s.2.1 with
      | none => some (.inr (.inr p), .write (s.1, s.2.1, s.2.2.1, some true))
      | some (q', .write b) =>
          some (.inr (.inl ((q', p.2), none)), .write (s.1, b, s.2.2.1, some true))
      | some (q', .move d) =>
          some (.inr (.inl ((q', sideAfterMove p.2 s.2.2.1 d), some d)),
            .write (s.1, s.2.1, s.2.2.1, some true))
    | .inr (.inl pp) =>
      match pp.2 with
      | none => some (.inl pp.1, .write s)
      | some d => some (.inl pp.1, Turing.TM0.Stmt.move d)
    | .inr (.inr _) => none

/-- Read the source acceptance bit from any stage of a marked-run control state. -/
def markRunAccept {Λ : Type} (a : Λ → Bool) : MarkRunControl Λ → Bool
  | .inl p => a p.1
  | .inr (.inl pp) => a pp.1.1
  | .inr (.inr p) => a p.1

/-- A live marked-run state always has a transition. -/
theorem markRun_live_ne_none {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) (p : MarkRunLabel Λ)
    (s : CellCore) : markRunTable M c (Sum.inl p) s ≠ none := by
  simp only [markRunTable]
  cases M c p.1 s.2.1 with
  | none => simp
  | some p' =>
    obtain ⟨q', stmt⟩ := p'
    cases stmt <;> simp

/-- A pending marked-run state always has a transition. -/
theorem markRun_pending_ne_none {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (pp : MarkPendingLabel Λ) (s : CellCore) :
    markRunTable M c (Sum.inr (Sum.inl pp)) s ≠ none := by
  simp only [markRunTable]
  cases pp.2 <;> simp

/-- Halting of the marked-run transition table is independent of the supplied coin bit. -/
theorem markRun_commonHalt {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) :
    ∀ q s, (markRunTable M false q s = none) ↔ (markRunTable M true q s = none) := by
  intro q s
  match q with
  | .inl p =>
    constructor
    · intro h; exact absurd h (markRun_live_ne_none M false p s)
    · intro h; exact absurd h (markRun_live_ne_none M true p s)
  | .inr (.inl pp) =>
    constructor
    · intro h; exact absurd h (markRun_pending_ne_none M false pp s)
    · intro h; exact absurd h (markRun_pending_ne_none M true pp s)
  | .inr (.inr _) => simp [markRunTable]

/-- The home track marks exactly the cell whose absolute position is zero when the head offset
is `off`. -/
def PhaseHomeAt (T : Turing.Tape CellCore) (off : ℤ) : Prop :=
  ∀ i : ℤ, (T.nth i).2.2.1 = decide (i + off = 0)

/-- Every nonblank work cell is marked as visited or lies within the original input interval of
length `n`. -/
def PhaseWorkMarked (T : Turing.Tape CellCore) (off : ℤ) (n : ℕ) : Prop :=
  ∀ i : ℤ, (T.nth i).2.1 ≠ none →
    ((T.nth i).2.2.2 ≠ none ∨ (0 ≤ i + off ∧ i + off < (n : ℤ)))

/-- The current input track equals the initial input track after accounting for the head offset. -/
def PhaseInputSame (initial current : Turing.Tape CellCore) (off : ℤ) : Prop :=
  ∀ i : ℤ, (current.nth i).1 = (initial.nth (i + off)).1

/-- The visitation marks occupy exactly the closed absolute interval from `lo` to `hi`. -/
def PhaseMarkAbs (T : Turing.Tape CellCore) (off lo hi : ℤ) : Prop :=
  ∀ i : ℤ, (T.nth i).2.2.2 ≠ none ↔ (lo ≤ i + off ∧ i + off ≤ hi)

/-- Under `PhaseHomeAt`, the current cell has its home marker precisely when the head offset is
zero. -/
theorem phaseHomeAt_head (T : Turing.Tape CellCore) (off : ℤ) (h : PhaseHomeAt T off) :
    T.head.2.2.1 = decide (off = 0) := by simpa using! h 0

/-- Moving left preserves the home-marker invariant with the head offset decreased by one. -/
theorem phaseHomeAt_move_left (T : Turing.Tape CellCore) (off : ℤ) (h : PhaseHomeAt T off) :
    PhaseHomeAt (T.move .left) (off - 1) := by
  intro i
  rw [Turing.Tape.move_left_nth, h]
  rw [show i - 1 + off = i + (off - 1) by omega]

/-- Moving right preserves the home-marker invariant with the head offset increased by one. -/
theorem phaseHomeAt_move_right (T : Turing.Tape CellCore) (off : ℤ) (h : PhaseHomeAt T off) :
    PhaseHomeAt (T.move .right) (off + 1) := by
  intro i
  rw [Turing.Tape.move_right_nth, h]
  rw [show i + 1 + off = i + (off + 1) by omega]

/-- A marked work write preserves the home marker, input track, and marked-work invariant. -/
theorem phaseWrite_invariants (T : Turing.Tape CellCore) (off : ℤ) (n : ℕ)
    (b : Option Bool) (initial : Turing.Tape CellCore)
    (hhome : PhaseHomeAt T off) (hinp : PhaseInputSame initial T off)
    (hwork : PhaseWorkMarked T off n) :
    PhaseHomeAt (T.write (markCell T b)) off ∧
      PhaseInputSame initial (T.write (markCell T b)) off ∧
      PhaseWorkMarked (T.write (markCell T b)) off n := by
  constructor
  · intro i
    rw [Turing.Tape.write_nth]
    split
    · next h0 =>
      subst h0
      simpa [markCell] using! hhome 0
    · next _ => exact hhome i
  · constructor
    · intro i
      rw [Turing.Tape.write_nth]
      split
      · next h0 =>
        subst h0
        simpa [markCell] using! hinp 0
      · next _ => exact hinp i
    · intro i
      rw [Turing.Tape.write_nth]
      split
      · next h0 =>
        subst h0
        intro hm
        simp only [markCell] at hm ⊢
        by_cases hb : b = none
        · simp [hb] at hm
        · exact Or.inl (by simp)
      · next _ => exact hwork i

/-- Extending an integer interval to include a point at distance at most one preserves the
stated endpoint bounds and contains no other new points. -/
theorem int_min_max_facts (lo hi off : ℤ) (hslack : lo - 1 ≤ off ∧ off ≤ hi + 1) :
    min lo off ≤ lo ∧ hi ≤ max hi off ∧ max hi off ≤ hi + 1 ∧ lo - 1 ≤ min lo off ∧
      ∀ x : ℤ, min lo off ≤ x → x ≤ max hi off → x ≠ off → lo ≤ x ∧ x ≤ hi := by
  have h1 : min lo off ≤ lo := min_le_left lo off
  have h2 : hi ≤ max hi off := le_max_left hi off
  have h3 : min lo off ≤ off := min_le_right lo off
  have h4 : off ≤ max hi off := le_max_right hi off
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · rcases le_total off hi with hle | hge
    · rw [max_eq_left hle]; omega
    · rw [max_eq_right hge]; omega
  · rcases le_total lo off with hle | hge
    · rw [min_eq_left hle]; omega
    · rw [min_eq_right hge]; omega
  · intro x hx1 hx2 hx3
    rcases le_total off hi with hle | hge
    · rw [max_eq_left hle] at hx2
      rcases le_total lo off with hle2 | hge2
      · rw [min_eq_left hle2] at hx1; omega
      · rw [min_eq_right hge2] at hx1; omega
    · rw [max_eq_right hge] at hx2
      rcases le_total lo off with hle2 | hge2
      · rw [min_eq_left hle2] at hx1; omega
      · rw [min_eq_right hge2] at hx1; omega

/-- A marked write extends the marked interval to include the current offset when it is at most
one cell beyond either endpoint. -/
theorem phaseMarkAbs_write (T : Turing.Tape CellCore) (b : Option Bool) (off lo hi : ℤ)
    (h : PhaseMarkAbs T off lo hi) (hs : lo - 1 ≤ off ∧ off ≤ hi + 1) :
    PhaseMarkAbs (T.write (markCell T b)) off (min lo off) (max hi off) := by
  intro i
  rw [Turing.Tape.write_nth]
  split
  · next h0 =>
    subst h0
    simp only [markCell]
    exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => by simp⟩
  · next _ =>
    constructor
    · intro hm
      obtain ⟨h1, h2⟩ := (h i).mp hm
      exact ⟨by omega, by omega⟩
    · intro hm
      exact (h i).mpr ⟨by omega, by omega⟩

/-- Moving left preserves the absolute marked interval and decreases the head offset by one. -/
theorem phaseMarkAbs_move_left (T : Turing.Tape CellCore) (off lo hi : ℤ)
    (h : PhaseMarkAbs T off lo hi) : PhaseMarkAbs (T.move .left) (off - 1) lo hi := by
  intro i
  rw [Turing.Tape.move_left_nth]
  constructor
  · intro hm
    obtain ⟨h1, h2⟩ := (h _).mp hm
    omega
  · intro hm
    obtain ⟨h1, h2⟩ := hm
    exact (h _).mpr ⟨by omega, by omega⟩

/-- Moving right preserves the absolute marked interval and increases the head offset by one. -/
theorem phaseMarkAbs_move_right (T : Turing.Tape CellCore) (off lo hi : ℤ)
    (h : PhaseMarkAbs T off lo hi) : PhaseMarkAbs (T.move .right) (off + 1) lo hi := by
  intro i
  rw [Turing.Tape.move_right_nth]
  constructor
  · intro hm
    obtain ⟨h1, h2⟩ := (h _).mp hm
    omega
  · intro hm
    obtain ⟨h1, h2⟩ := hm
    exact (h _).mpr ⟨by omega, by omega⟩

/-- Moving left preserves the input-track invariant with the head offset decreased by one. -/
theorem phaseInputSame_move_left (initial T : Turing.Tape CellCore) (off : ℤ)
    (h : PhaseInputSame initial T off) : PhaseInputSame initial (T.move .left) (off - 1) := by
  intro i
  rw [Turing.Tape.move_left_nth]
  have hi := h (i - 1)
  rw [show i - 1 + off = i + (off - 1) by omega] at hi
  exact hi

/-- Moving right preserves the input-track invariant with the head offset increased by one. -/
theorem phaseInputSame_move_right (initial T : Turing.Tape CellCore) (off : ℤ)
    (h : PhaseInputSame initial T off) : PhaseInputSame initial (T.move .right) (off + 1) := by
  intro i
  rw [Turing.Tape.move_right_nth]
  have hi := h (i + 1)
  rw [show i + 1 + off = i + (off + 1) by omega] at hi
  exact hi

/-- Moving left preserves the marked-work invariant with the head offset decreased by one. -/
theorem phaseWorkMarked_move_left (T : Turing.Tape CellCore) (off : ℤ) (n : ℕ)
    (h : PhaseWorkMarked T off n) : PhaseWorkMarked (T.move .left) (off - 1) n := by
  intro i hm
  rw [Turing.Tape.move_left_nth] at hm ⊢
  rcases h _ hm with hm2 | ⟨hw1, hw2⟩
  · exact Or.inl hm2
  · exact Or.inr ⟨by omega, by omega⟩

/-- Moving right preserves the marked-work invariant with the head offset increased by one. -/
theorem phaseWorkMarked_move_right (T : Turing.Tape CellCore) (off : ℤ) (n : ℕ)
    (h : PhaseWorkMarked T off n) : PhaseWorkMarked (T.move .right) (off + 1) n := by
  intro i hm
  rw [Turing.Tape.move_right_nth] at hm ⊢
  rcases h _ hm with hm2 | ⟨hw1, hw2⟩
  · exact Or.inl hm2
  · exact Or.inr ⟨by omega, by omega⟩

/-- Writing the current cell leaves every tape cell at a nonzero relative index unchanged. -/
theorem phaseWriteNth_of_ne (T : Turing.Tape CellCore) (c : CellCore) (i : ℤ)
    (h0 : i ≠ 0) : (T.write c).nth i = T.nth i := by
  rw [Turing.Tape.write_nth, ite_eq_right h0]

/-- The cell at relative index zero after a write is the written symbol. -/
theorem phaseWriteNth_zero (T : Turing.Tape CellCore) (c : CellCore) :
    (T.write c).nth 0 = c := by
  rw [Turing.Tape.write_nth, ite_eq_left rfl]

/-- Every unmarked cell retains its initial work symbol at the corresponding absolute position. -/
def PhaseUnmarkedWork (initial T : Turing.Tape CellCore) (off : ℤ) : Prop :=
  ∀ i : ℤ, (T.nth i).2.2.2 = none → (T.nth i).2.1 = (initial.nth (i + off)).2.1

/-- Every marked absolute position on the first tape remains marked on the second tape. -/
def PhaseMarkGrows (T T' : Turing.Tape CellCore) (off off' : ℤ) : Prop :=
  ∀ i : ℤ, (T.nth (i - off)).2.2.2 ≠ none → (T'.nth (i - off')).2.2.2 ≠ none

/-- Marking and writing the current work cell preserves the initial contents of all unmarked
work cells. -/
theorem phaseUnmarkedWork_write_markCell (T initial : Turing.Tape CellCore)
    (b : Option Bool) (off : ℤ)
    (h : PhaseUnmarkedWork initial T off) :
    PhaseUnmarkedWork initial (T.write (markCell T b)) off := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    rw [phaseWriteNth_zero] at hi
    exact absurd hi (by simp [markCell])
  · rw [phaseWriteNth_of_ne _ (markCell T b) i h0]
    rw [phaseWriteNth_of_ne _ (markCell T b) i h0] at hi
    exact h i hi

/-- Rewriting the current head symbol preserves the unmarked-work invariant. -/
theorem phaseUnmarkedWork_write_self (T initial : Turing.Tape CellCore) (off : ℤ)
    (h : PhaseUnmarkedWork initial T off) :
    PhaseUnmarkedWork initial (T.write T.head) off := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    rw [phaseWriteNth_zero] at hi ⊢
    rw [← Turing.Tape.nth_zero]
    exact h 0 hi
  · rw [phaseWriteNth_of_ne _ T.head i h0]
    rw [phaseWriteNth_of_ne _ T.head i h0] at hi
    exact h i hi

/-- Moving left preserves the unmarked-work invariant after decreasing the head offset by one. -/
theorem phaseUnmarkedWork_move_left (initial T : Turing.Tape CellCore) (off : ℤ)
    (h : PhaseUnmarkedWork initial T off) :
    PhaseUnmarkedWork initial (T.move .left) (off - 1) := by
  intro i hi
  rw [Turing.Tape.move_left_nth] at hi ⊢
  have h2 := h (i - 1) hi
  rw [show i - 1 + off = i + (off - 1) by omega] at h2
  exact h2

/-- Moving right preserves the unmarked-work invariant after increasing the head offset by one. -/
theorem phaseUnmarkedWork_move_right (initial T : Turing.Tape CellCore) (off : ℤ)
    (h : PhaseUnmarkedWork initial T off) :
    PhaseUnmarkedWork initial (T.move .right) (off + 1) := by
  intro i hi
  rw [Turing.Tape.move_right_nth] at hi ⊢
  have h2 := h (i + 1) hi
  rw [show i + 1 + off = i + (off + 1) by omega] at h2
  exact h2

/-- A marked work write preserves every existing visitation mark. -/
theorem phaseMarkGrows_write_markCell (T : Turing.Tape CellCore) (b : Option Bool) (off : ℤ) :
    PhaseMarkGrows T (T.write (markCell T b)) off off := by
  intro i hi
  by_cases h0 : i - off = 0
  · rw [h0, phaseWriteNth_zero]
    simp [markCell]
  · rw [phaseWriteNth_of_ne _ (markCell T b) _ h0]
    exact hi

/-- Rewriting the current head symbol preserves every visitation mark. -/
theorem phaseMarkGrows_write_self (T : Turing.Tape CellCore) (off : ℤ) :
    PhaseMarkGrows T (T.write T.head) off off := by
  intro i hi
  by_cases h0 : i - off = 0
  · rw [h0] at hi
    rw [h0, phaseWriteNth_zero]
    rwa [Turing.Tape.nth_zero] at hi
  · rw [phaseWriteNth_of_ne _ T.head _ h0]
    exact hi

/-- Moving left preserves visitation marks at their absolute positions. -/
theorem phaseMarkGrows_move_left (T : Turing.Tape CellCore) (off : ℤ) :
    PhaseMarkGrows T (T.move .left) off (off - 1) := by
  intro i hi
  have h1 : i - (off - 1) - 1 = i - off := by omega
  rw [Turing.Tape.move_left_nth, h1]
  exact hi

/-- Moving right preserves visitation marks at their absolute positions. -/
theorem phaseMarkGrows_move_right (T : Turing.Tape CellCore) (off : ℤ) :
    PhaseMarkGrows T (T.move .right) off (off + 1) := by
  intro i hi
  have h1 : i - (off + 1) + 1 = i - off := by omega
  rw [Turing.Tape.move_right_nth, h1]
  exact hi

/-- Preservation of visitation marks is transitive across three tapes with their respective head
offsets. -/
theorem phaseMarkGrows_trans {T₁ T₂ T₃ : Turing.Tape CellCore} {o₁ o₂ o₃ : ℤ}
    (h12 : PhaseMarkGrows T₁ T₂ o₁ o₂) (h23 : PhaseMarkGrows T₂ T₃ o₂ o₃) :
    PhaseMarkGrows T₁ T₃ o₁ o₃ := fun _ hi => h23 _ (h12 _ hi)

/-- Interleave source coins with filler coins, returning the remaining source suffix unchanged
if the fillers run out. -/
def pairCoins : List Bool → List Bool → List Bool
  | [], _ => []
  | c :: cs, f :: fs => c :: f :: pairCoins cs fs
  | c :: cs, [] => c :: cs

/-- At a live configuration, consuming a coin and taking a successful step adds one read and one
transition to the remaining configuration run. -/
theorem coinConfigRunAux_cons_live {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    {M : Bool → Turing.TM0.Machine Γ Λ} {c : Bool} {cs : List Bool}
    {cfg : Turing.TM0.Cfg Γ Λ} {q' : Λ} {T' : Turing.Tape Γ}
    (hchf : coinHalt M cfg = false)
    (hstep : Turing.TM0.step (M c) cfg = some ⟨q', T'⟩) :
    coinConfigRunAux M (c :: cs) cfg =
      ⟨(coinConfigRunAux M cs ⟨q', T'⟩).stopped,
        (coinConfigRunAux M cs ⟨q', T'⟩).reads + 1,
        (coinConfigRunAux M cs ⟨q', T'⟩).transitions + 1⟩ := by
  simp only [coinConfigRunAux, hchf, hstep]
  rw [ite_eq_right (by simp)]

/-- At a live configuration, consuming a coin and taking a successful step preserves the
remaining acceptance result and adds one read. -/
theorem coinTapeRunAux_cons_live {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    {M : Bool → Turing.TM0.Machine Γ Λ} {accept : Λ → Bool} {c : Bool} {cs : List Bool}
    {cfg : Turing.TM0.Cfg Γ Λ} {q' : Λ} {T' : Turing.Tape Γ}
    (hchf : coinHalt M cfg = false)
    (hstep : Turing.TM0.step (M c) cfg = some ⟨q', T'⟩) :
    coinTapeRunAux M accept (c :: cs) cfg =
      Prod.map id (· + 1) (coinTapeRunAux M accept cs ⟨q', T'⟩) := by
  simp only [coinTapeRunAux, hchf, hstep]
  rw [ite_eq_right (by simp)]

/-- A live marked-run configuration does not satisfy the coin-halting predicate. -/
theorem markRun_coinHalt_live {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ)
    (p : MarkRunLabel Λ) (T : Turing.Tape CellCore) :
    coinHalt (markRunTable M) ⟨Sum.inl p, T⟩ = false := by
  simp only [coinHalt, markRunTable]
  split <;> split <;> simp

/-- A pending marked-run configuration does not satisfy the coin-halting predicate. -/
theorem markRun_coinHalt_pending {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ)
    (pp : MarkPendingLabel Λ) (T : Turing.Tape CellCore) :
    coinHalt (markRunTable M) ⟨Sum.inr (Sum.inl pp), T⟩ = false := by
  simp only [coinHalt, markRunTable]
  split <;> simp

/-- A final marked-run configuration satisfies the coin-halting predicate. -/
theorem markRun_coinHalt_final {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ)
    (p : MarkRunLabel Λ) (T : Turing.Tape CellCore) :
    coinHalt (markRunTable M) ⟨Sum.inr (Sum.inr p), T⟩ = true := by
  simp [coinHalt, markRunTable]

/-- When the source table halts, the marked simulator marks the current cell and enters its
final state. -/
theorem markRun_step_none {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) (p : MarkRunLabel Λ)
    (T : Turing.Tape CellCore) (h : M c p.1 T.head.2.1 = none) :
    Turing.TM0.step (markRunTable M c) ⟨Sum.inl p, T⟩ =
      some ⟨Sum.inr (Sum.inr p), T.write (markCell T T.head.2.1)⟩ := by
  simp [TM0_step_apply, markRunTable, h, TM0StmtApply, markCell]

/-- A source write becomes a marked work write followed by a pending state with no movement. -/
theorem markRun_step_write {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) (p : MarkRunLabel Λ)
    (T : Turing.Tape CellCore) (q' : Λ) (b : Option Bool)
    (h : M c p.1 T.head.2.1 = some (q', Turing.TM0.Stmt.write b)) :
    Turing.TM0.step (markRunTable M c) ⟨Sum.inl p, T⟩ =
      some ⟨Sum.inr (Sum.inl ((q', p.2), none)), T.write (markCell T b)⟩ := by
  simp [TM0_step_apply, markRunTable, h, TM0StmtApply, markCell]

/-- A source movement first marks the current cell and records the movement and updated side in
a pending state. -/
theorem markRun_step_move {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) (p : MarkRunLabel Λ)
    (T : Turing.Tape CellCore) (q' : Λ) (d : Turing.Dir)
    (h : M c p.1 T.head.2.1 = some (q', Turing.TM0.Stmt.move d)) :
    Turing.TM0.step (markRunTable M c) ⟨Sum.inl p, T⟩ =
      some ⟨Sum.inr (Sum.inl ((q', sideAfterMove p.2 T.head.2.2.1 d), some d)),
        T.write (markCell T T.head.2.1)⟩ := by
  simp [TM0_step_apply, markRunTable, h, TM0StmtApply, markCell]

/-- A pending state without a movement rewrites the head symbol and returns to a live state. -/
theorem markRun_step_pending_write {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (pp : MarkPendingLabel Λ) (T : Turing.Tape CellCore) (h : pp.2 = none) :
    Turing.TM0.step (markRunTable M c) ⟨Sum.inr (Sum.inl pp), T⟩ =
      some ⟨Sum.inl pp.1, T.write T.head⟩ := by
  simp [TM0_step_apply, markRunTable, h, TM0StmtApply]

/-- A pending movement moves the tape in the stored direction and returns to a live state. -/
theorem markRun_step_pending_move {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (pp : MarkPendingLabel Λ) (T : Turing.Tape CellCore) (d : Turing.Dir)
    (h : pp.2 = some d) :
    Turing.TM0.step (markRunTable M c) ⟨Sum.inr (Sum.inl pp), T⟩ =
      some ⟨Sum.inl pp.1, T.move d⟩ := by
  simp [TM0_step_apply, markRunTable, h, TM0StmtApply]

/-- Projecting a marked work write onto the work track gives the corresponding write on the
projected tape. -/
theorem markCell_workMap (T : Turing.Tape CellCore) (b : Option Bool) :
    (T.write (markCell T b)).map phaseWorkMap = (T.map phaseWorkMap).write b := by
  rw [Turing.Tape.map_write]
  simp [phaseWorkMap, markCell]

/-- A source run consuming all of `w` is simulated with interleaved fillers in exactly `2 *
w.length + 1` reads and transitions, preserving its final work tape and acceptance bit. The
resulting tape satisfies the stated input, home, mark-growth, interval, and displacement
bounds. -/
theorem markRun_coin_run {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (initial : Turing.Tape CellCore) (n : ℕ)
    (w fs : List Bool) (q : Λ) (side : Bool) (T : Turing.Tape CellCore)
    (off lo hi : ℤ)
    (hhome : PhaseHomeAt T off) (hside : SideAt side off)
    (hinp : PhaseInputSame initial T off)
    (hmark : PhaseMarkAbs T off lo hi) (hwork : PhaseWorkMarked T off n)
    (hucopy : PhaseUnmarkedWork initial T off)
    (hslack : lo - 1 ≤ off ∧ off ≤ hi + 1)
    (final : Turing.TM0.Cfg (Option Bool) Λ)
    (hstop : (coinConfigRunAux M w ⟨q, T.map phaseWorkMap⟩).stopped = some final)
    (hread : (coinConfigRunAux M w ⟨q, T.map phaseWorkMap⟩).reads = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (Tf : Turing.Tape CellCore) (off' lo' hi' : ℤ),
      PhaseHomeAt Tf off' ∧ SideAt sf off' ∧
      PhaseInputSame initial Tf off' ∧ PhaseMarkAbs Tf off' lo' hi' ∧
      PhaseWorkMarked Tf off' n ∧
      PhaseUnmarkedWork initial Tf off' ∧ PhaseMarkGrows T Tf off off' ∧
      (Tf.nth (off - off')).2.2.2 ≠ none ∧
      lo' ≤ lo ∧ hi ≤ hi' ∧ hi' - hi ≤ 2 * w.length + 1 ∧ lo - lo' ≤ 2 * w.length + 1 ∧
      off - w.length ≤ off' ∧ off' ≤ off + w.length ∧
      Tf.map phaseWorkMap = final.Tape ∧
      ∀ (x : Bool) (rest : List Bool),
        coinConfigRunAux (markRunTable M) (pairCoins w fs ++ x :: rest)
            ⟨Sum.inl (q, side), T⟩ =
          ⟨some ⟨Sum.inr (Sum.inr (final.q, sf)), Tf⟩, 2 * w.length + 1, 2 * w.length + 1⟩ ∧
        (coinTapeRunAux (markRunTable M) (markRunAccept a) (pairCoins w fs ++ x :: rest)
          ⟨Sum.inl (q, side), T⟩).1 = some (a final.q) := by
  induction w generalizing q side T off lo hi fs final with
  | nil =>
    have hch : coinHalt M ⟨q, T.map phaseWorkMap⟩ = true := by
      by_contra hcon
      simp only [coinConfigRunAux] at hstop
      split at hstop
      · next h => exact absurd h hcon
      · simp at hstop
    simp only [coinConfigRunAux, ite_eq_left hch] at hstop hread
    have hfin : final = ⟨q, T.map phaseWorkMap⟩ := (Option.some.inj hstop).symm
    subst final
    have h1 : (T.map phaseWorkMap).head = T.head.2.1 := by
      simp [Turing.Tape.map_fst, phaseWorkMap]
    have hM : ∀ x : Bool, M x q T.head.2.1 = none := by
      intro x
      have hf : (M false q (T.map phaseWorkMap).head).isNone = true := by
        have hh := hch
        simp only [coinHalt, Bool.and_eq_true] at hh
        exact hh.1
      have ht : (M true q (T.map phaseWorkMap).head).isNone = true := by
        have hh := hch
        simp only [coinHalt, Bool.and_eq_true] at hh
        exact hh.2
      rw [h1] at hf ht
      cases x with
      | false => simpa using! hf
      | true => simpa using! ht
    have hstep : ∀ x : Bool, Turing.TM0.step (markRunTable M x) ⟨Sum.inl (q, side), T⟩ =
        some ⟨Sum.inr (Sum.inr (q, side)), T.write (markCell T T.head.2.1)⟩ :=
      fun x => markRun_step_none M x (q, side) T (hM x)
    have hwinv := phaseWrite_invariants T off n T.head.2.1 initial hhome hinp hwork
    have hmark' := phaseMarkAbs_write T T.head.2.1 off lo hi hmark hslack
    have hproj : (T.write (markCell T T.head.2.1)).map phaseWorkMap = (T.map phaseWorkMap) := by
      rw [markCell_workMap, ← h1, Turing.Tape.write_self]
    refine ⟨side, T.write (markCell T T.head.2.1), off, min lo off, max hi off,
      hwinv.1, hside, hwinv.2.1, hmark', hwinv.2.2,
      phaseUnmarkedWork_write_markCell T initial T.head.2.1 off hucopy,
      phaseMarkGrows_write_markCell T T.head.2.1 off, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hproj, ?_⟩
    · rw [show off - off = 0 by omega, phaseWriteNth_zero]
      simp [markCell]
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · intro x rest
      have hword : pairCoins ([] : List Bool) fs ++ x :: rest = x :: rest := rfl
      have key : coinConfigRunAux (markRunTable M) (x :: rest)
          ⟨Sum.inl (q, side), T⟩ =
          ⟨some ⟨Sum.inr (Sum.inr (q, side)), T.write (markCell T T.head.2.1)⟩, 1, 1⟩ := by
        simp only [coinConfigRunAux, markRun_coinHalt_live, hstep x]
        cases rest with
        | nil => simp [coinConfigRunAux, markRun_coinHalt_final]
        | cons c cs => simp [coinConfigRunAux, markRun_coinHalt_final]
      constructor
      · rw [hword, key]
        simp
      · rw [hword]
        simp only [coinTapeRunAux, markRun_coinHalt_live, hstep x]
        cases rest with
        | nil => simp [coinTapeRunAux, markRun_coinHalt_final, markRunAccept]
        | cons c cs => simp [coinTapeRunAux, markRun_coinHalt_final, markRunAccept]
  | cons c cs ih =>
    have hchf : coinHalt M ⟨q, T.map phaseWorkMap⟩ = false := by
      by_contra hcon
      have hch' : coinHalt M ⟨q, T.map phaseWorkMap⟩ = true := by
        cases hh : coinHalt M ⟨q, T.map phaseWorkMap⟩ <;> simp_all
      simp only [coinConfigRunAux, ite_eq_left hch'] at hread
      simp at hread
    obtain ⟨f, fs', rfl⟩ : ∃ f fs', fs = f :: fs' := by
      cases fs with
      | nil => simp at hfs
      | cons f fs' => exact ⟨f, fs', rfl⟩
    have hheadWork : (T.map phaseWorkMap).head = T.head.2.1 := by
      simp [Turing.Tape.map_fst, phaseWorkMap]
    have hlive : ∀ x : Bool, M x q (T.map phaseWorkMap).head ≠ none := by
      intro x hx
      have hboth : M false q (T.map phaseWorkMap).head = none ∧
          M true q (T.map phaseWorkMap).head = none := by
        cases x with
        | false => exact ⟨hx, (hc q _).mp hx⟩
        | true => exact ⟨(hc q _).mpr hx, hx⟩
      simp only [coinHalt] at hchf
      rw [hboth.1, hboth.2] at hchf
      simp at hchf
    cases hs : M c q (T.map phaseWorkMap).head with
    | none => exact absurd hs (hlive c)
    | some p =>
      obtain ⟨q', stmt⟩ := p
      rw [hheadWork] at hs
      have hmark₁ := phaseMarkAbs_write T T.head.2.1 off lo hi hmark hslack
      have hslack₁ : min lo off - 1 ≤ off ∧ off ≤ max hi off + 1 := by omega
      have hcs : (c :: cs).length = cs.length + 1 := rfl
      cases stmt with
      | write b =>
        have hsrcstep : Turing.TM0.step (M c) ⟨q, T.map phaseWorkMap⟩ =
            some ⟨q', (T.map phaseWorkMap).write b⟩ := by
          simp only [TM0_step_apply]
          rw [hheadWork, hs]
          rfl
        rw [coinConfigRunAux_cons_live hchf hsrcstep] at hstop hread
        have hread' : (coinConfigRunAux M cs ⟨q', (T.map phaseWorkMap).write b⟩).reads
            = cs.length := by
          have h := hread
          simp only [List.length_cons] at h
          omega
        have hwinv := phaseWrite_invariants T off n b initial hhome hinp hwork
        have hmark₁ := phaseMarkAbs_write T b off lo hi hmark hslack
        have hproj0 : (T.write (markCell T b)).map phaseWorkMap =
            (T.map phaseWorkMap).write b := markCell_workMap T b
        rw [← hproj0] at hstop hread'
        obtain ⟨sf, Tf, off'', lo', hi', hhome', hside', hinp', hmark', hwork', hucopy', hgrow',
            hstart', hlo', hhi', hg1, hg2, hdisp1, hdisp2, hproj, hforall⟩ :=
          ih fs' q' side (T.write (markCell T b)) off (min lo off) (max hi off)
            hwinv.1 hside hwinv.2.1 hmark₁ hwinv.2.2
            (phaseUnmarkedWork_write_markCell T initial b off hucopy) hslack₁ final hstop hread'
            (by have h := hfs; simp only [List.length_cons] at h; omega)
        refine ⟨sf, Tf, off'', lo', hi', hhome', hside', hinp', hmark', hwork',
          hucopy', phaseMarkGrows_trans (phaseMarkGrows_write_markCell T b off) hgrow', hstart',
          ?_, ?_, ?_, ?_, ?_, ?_, hproj, ?_⟩
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · intro x rest
          obtain ⟨h1, h2⟩ := hforall x rest
          have hstep1 : Turing.TM0.step (markRunTable M c) ⟨Sum.inl (q, side), T⟩ =
              some ⟨Sum.inr (Sum.inl ((q', side), none)), T.write (markCell T b)⟩ :=
            markRun_step_write M c (q, side) T q' b hs
          have hstep2 : Turing.TM0.step (markRunTable M f)
              ⟨Sum.inr (Sum.inl ((q', side), none)), T.write (markCell T b)⟩ =
              some ⟨Sum.inl (q', side), T.write (markCell T b)⟩ := by
            rw [markRun_step_pending_write M f ((q', side), none)
              (T.write (markCell T b)) rfl, Turing.Tape.write_self]
          constructor
          · show coinConfigRunAux (markRunTable M)
                (pairCoins (c :: cs) (f :: fs') ++ x :: rest) ⟨Sum.inl (q, side), T⟩ = _
            rw [show pairCoins (c :: cs) (f :: fs') ++ x :: rest
                  = c :: f :: (pairCoins cs fs' ++ x :: rest) from rfl,
              coinConfigRunAux_cons_live (markRun_coinHalt_live M (q, side) T) hstep1,
              coinConfigRunAux_cons_live
                (markRun_coinHalt_pending M ((q', side), none)
                  (T.write (markCell T b))) hstep2,
              h1]
            congr 1
          · show (coinTapeRunAux (markRunTable M) (markRunAccept a)
                (pairCoins (c :: cs) (f :: fs') ++ x :: rest)
                ⟨Sum.inl (q, side), T⟩).1 = _
            rw [show pairCoins (c :: cs) (f :: fs') ++ x :: rest
                  = c :: f :: (pairCoins cs fs' ++ x :: rest) from rfl,
              coinTapeRunAux_cons_live (markRun_coinHalt_live M (q, side) T) hstep1,
              coinTapeRunAux_cons_live
                (markRun_coinHalt_pending M ((q', side), none)
                  (T.write (markCell T b))) hstep2]
            simp only [Prod.map, id_eq]
            rw [h2]
      | move d =>
        have hsrcstep : Turing.TM0.step (M c) ⟨q, T.map phaseWorkMap⟩ =
            some ⟨q', (T.map phaseWorkMap).move d⟩ := by
          simp only [TM0_step_apply]
          rw [hheadWork, hs]
          rfl
        rw [coinConfigRunAux_cons_live hchf hsrcstep] at hstop hread
        have hread' : (coinConfigRunAux M cs ⟨q', (T.map phaseWorkMap).move d⟩).reads
            = cs.length := by
          have h := hread
          simp only [List.length_cons] at h
          omega
        have hwinv := phaseWrite_invariants T off n T.head.2.1 initial hhome hinp hwork
        have hsidehome : T.head.2.2.1 = decide (off = 0) := phaseHomeAt_head T off hhome
        cases d with
        | left =>
          have hsideL : SideAt (sideAfterMove side T.head.2.2.1 Turing.Dir.left) (off - 1) := by
            have hsml := sideAt_move_left side off hside
            rwa [← hsidehome] at hsml
          have hstep1 : Turing.TM0.step (markRunTable M c) ⟨Sum.inl (q, side), T⟩ =
              some ⟨Sum.inr (Sum.inl ((q', sideAfterMove side T.head.2.2.1 Turing.Dir.left),
                some Turing.Dir.left)), T.write (markCell T T.head.2.1)⟩ :=
            markRun_step_move M c (q, side) T q' Turing.Dir.left hs
          have hstep2 : Turing.TM0.step (markRunTable M f)
              ⟨Sum.inr (Sum.inl ((q', sideAfterMove side T.head.2.2.1 Turing.Dir.left),
                some Turing.Dir.left)), T.write (markCell T T.head.2.1)⟩ =
              some ⟨Sum.inl (q', sideAfterMove side T.head.2.2.1 Turing.Dir.left),
                (T.write (markCell T T.head.2.1)).move Turing.Dir.left⟩ :=
            markRun_step_pending_move M f _ _ Turing.Dir.left rfl
          have hTapec : ((T.write (markCell T T.head.2.1)).move Turing.Dir.left).map phaseWorkMap
              = (T.map phaseWorkMap).move Turing.Dir.left := by
            rw [Turing.Tape.map_move, markCell_workMap, ← hheadWork, Turing.Tape.write_self]
          rw [← hTapec] at hstop hread'
          have hhome₂ := phaseHomeAt_move_left _ off hwinv.1
          have hmark₂ := phaseMarkAbs_move_left _ off (min lo off) (max hi off) hmark₁
          have hinp₂ := phaseInputSame_move_left initial _ off hwinv.2.1
          have hwork₂ := phaseWorkMarked_move_left _ off n hwinv.2.2
          have hslack₂ : min lo off - 1 ≤ off - 1 ∧ off - 1 ≤ max hi off + 1 := by omega
          have hucopy₁ : PhaseUnmarkedWork initial
              ((T.write (markCell T T.head.2.1)).move Turing.Dir.left) (off - 1) :=
            phaseUnmarkedWork_move_left initial _ off
              (phaseUnmarkedWork_write_markCell T initial T.head.2.1 off hucopy)
          have hgrow₁ : PhaseMarkGrows T
              ((T.write (markCell T T.head.2.1)).move Turing.Dir.left) off (off - 1) :=
            phaseMarkGrows_trans (phaseMarkGrows_write_markCell T T.head.2.1 off)
              (phaseMarkGrows_move_left _ off)
          obtain ⟨sf, Tf, off'', lo', hi', hhome', hside', hinp', hmark', hwork', hucopy', hgrow',
              hstart', hlo', hhi', hg1, hg2, hdisp1, hdisp2, hproj, hforall⟩ :=
            ih fs' q' (sideAfterMove side T.head.2.2.1 Turing.Dir.left)
              ((T.write (markCell T T.head.2.1)).move Turing.Dir.left) (off - 1)
              (min lo off) (max hi off) hhome₂ hsideL hinp₂ hmark₂ hwork₂ hucopy₁ hslack₂ final
              hstop hread'
              (by have h := hfs; simp only [List.length_cons] at h; omega)
          have hstartCell : (((T.write (markCell T T.head.2.1)).move Turing.Dir.left).nth
              (off - (off - 1))).2.2.2 ≠ none := by
            have h1 : off - (off - 1) = 1 := by omega
            rw [h1, Turing.Tape.move_left_nth, show (1 : ℤ) - 1 = 0 by omega,
              phaseWriteNth_zero]
            simp [markCell]
          refine ⟨sf, Tf, off'', lo', hi', hhome', hside', hinp', hmark', hwork',
            hucopy', phaseMarkGrows_trans hgrow₁ hgrow', hgrow' off hstartCell,
            ?_, ?_, ?_, ?_, ?_, ?_, hproj, ?_⟩
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · intro x rest
            obtain ⟨h1, h2⟩ := hforall x rest
            constructor
            · show coinConfigRunAux (markRunTable M)
                  (pairCoins (c :: cs) (f :: fs') ++ x :: rest) ⟨Sum.inl (q, side), T⟩ = _
              rw [show pairCoins (c :: cs) (f :: fs') ++ x :: rest
                    = c :: f :: (pairCoins cs fs' ++ x :: rest) from rfl,
                coinConfigRunAux_cons_live (markRun_coinHalt_live M (q, side) T) hstep1,
                coinConfigRunAux_cons_live
                  (markRun_coinHalt_pending M _ (T.write (markCell T T.head.2.1))) hstep2,
                h1]
              congr 1
            · show (coinTapeRunAux (markRunTable M) (markRunAccept a)
                  (pairCoins (c :: cs) (f :: fs') ++ x :: rest)
                  ⟨Sum.inl (q, side), T⟩).1 = _
              rw [show pairCoins (c :: cs) (f :: fs') ++ x :: rest
                    = c :: f :: (pairCoins cs fs' ++ x :: rest) from rfl,
                coinTapeRunAux_cons_live (markRun_coinHalt_live M (q, side) T) hstep1,
                coinTapeRunAux_cons_live
                  (markRun_coinHalt_pending M _ (T.write (markCell T T.head.2.1))) hstep2]
              simp only [Prod.map, id_eq]
              rw [h2]
        | right =>
          have hsideR : SideAt (sideAfterMove side T.head.2.2.1 Turing.Dir.right) (off + 1) := by
            have hsmr := sideAt_move_right side off hside
            rwa [← hsidehome] at hsmr
          have hstep1 : Turing.TM0.step (markRunTable M c) ⟨Sum.inl (q, side), T⟩ =
              some ⟨Sum.inr (Sum.inl ((q', sideAfterMove side T.head.2.2.1 Turing.Dir.right),
                some Turing.Dir.right)), T.write (markCell T T.head.2.1)⟩ :=
            markRun_step_move M c (q, side) T q' Turing.Dir.right hs
          have hstep2 : Turing.TM0.step (markRunTable M f)
              ⟨Sum.inr (Sum.inl ((q', sideAfterMove side T.head.2.2.1 Turing.Dir.right),
                some Turing.Dir.right)), T.write (markCell T T.head.2.1)⟩ =
              some ⟨Sum.inl (q', sideAfterMove side T.head.2.2.1 Turing.Dir.right),
                (T.write (markCell T T.head.2.1)).move Turing.Dir.right⟩ :=
            markRun_step_pending_move M f _ _ Turing.Dir.right rfl
          have hTapec : ((T.write (markCell T T.head.2.1)).move Turing.Dir.right).map phaseWorkMap
              = (T.map phaseWorkMap).move Turing.Dir.right := by
            rw [Turing.Tape.map_move, markCell_workMap, ← hheadWork, Turing.Tape.write_self]
          rw [← hTapec] at hstop hread'
          have hhome₂ := phaseHomeAt_move_right _ off hwinv.1
          have hmark₂ := phaseMarkAbs_move_right _ off (min lo off) (max hi off) hmark₁
          have hinp₂ := phaseInputSame_move_right initial _ off hwinv.2.1
          have hwork₂ := phaseWorkMarked_move_right _ off n hwinv.2.2
          have hslack₂ : min lo off - 1 ≤ off + 1 ∧ off + 1 ≤ max hi off + 1 := by omega
          have hucopy₁ : PhaseUnmarkedWork initial
              ((T.write (markCell T T.head.2.1)).move Turing.Dir.right) (off + 1) :=
            phaseUnmarkedWork_move_right initial _ off
              (phaseUnmarkedWork_write_markCell T initial T.head.2.1 off hucopy)
          have hgrow₁ : PhaseMarkGrows T
              ((T.write (markCell T T.head.2.1)).move Turing.Dir.right) off (off + 1) :=
            phaseMarkGrows_trans (phaseMarkGrows_write_markCell T T.head.2.1 off)
              (phaseMarkGrows_move_right _ off)
          obtain ⟨sf, Tf, off'', lo', hi', hhome', hside', hinp', hmark', hwork', hucopy', hgrow',
              hstart', hlo', hhi', hg1, hg2, hdisp1, hdisp2, hproj, hforall⟩ :=
            ih fs' q' (sideAfterMove side T.head.2.2.1 Turing.Dir.right)
              ((T.write (markCell T T.head.2.1)).move Turing.Dir.right) (off + 1)
              (min lo off) (max hi off) hhome₂ hsideR hinp₂ hmark₂ hwork₂ hucopy₁ hslack₂ final
              hstop hread'
              (by have h := hfs; simp only [List.length_cons] at h; omega)
          have hstartCell : (((T.write (markCell T T.head.2.1)).move Turing.Dir.right).nth
              (off - (off + 1))).2.2.2 ≠ none := by
            have h1 : off - (off + 1) = -1 := by omega
            rw [h1, Turing.Tape.move_right_nth, show (-1 : ℤ) + 1 = 0 by omega,
              phaseWriteNth_zero]
            simp [markCell]
          refine ⟨sf, Tf, off'', lo', hi', hhome', hside', hinp', hmark', hwork',
            hucopy', phaseMarkGrows_trans hgrow₁ hgrow', hgrow' off hstartCell,
            ?_, ?_, ?_, ?_, ?_, ?_, hproj, ?_⟩
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · intro x rest
            obtain ⟨h1, h2⟩ := hforall x rest
            constructor
            · show coinConfigRunAux (markRunTable M)
                  (pairCoins (c :: cs) (f :: fs') ++ x :: rest) ⟨Sum.inl (q, side), T⟩ = _
              rw [show pairCoins (c :: cs) (f :: fs') ++ x :: rest
                    = c :: f :: (pairCoins cs fs' ++ x :: rest) from rfl,
                coinConfigRunAux_cons_live (markRun_coinHalt_live M (q, side) T) hstep1,
                coinConfigRunAux_cons_live
                  (markRun_coinHalt_pending M _ (T.write (markCell T T.head.2.1))) hstep2,
                h1]
              congr 1
            · show (coinTapeRunAux (markRunTable M) (markRunAccept a)
                  (pairCoins (c :: cs) (f :: fs') ++ x :: rest)
                  ⟨Sum.inl (q, side), T⟩).1 = _
              rw [show pairCoins (c :: cs) (f :: fs') ++ x :: rest
                    = c :: f :: (pairCoins cs fs' ++ x :: rest) from rfl,
                coinTapeRunAux_cons_live (markRun_coinHalt_live M (q, side) T) hstep1,
                coinTapeRunAux_cons_live
                  (markRun_coinHalt_pending M _ (T.write (markCell T T.head.2.1))) hstep2]
              simp only [Prod.map, id_eq]
              rw [h2]

/-- The lifted homing machine halts when the current cell carries the home marker. -/
theorem liftMarkerHome_step_home (q : HomeState) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = true) :
    Turing.TM0.step (liftMarkerTable (fun _ => markerHomeTable) false) ⟨q, T⟩ = none := by
  simp [TM0_step_apply, markerHomeTable, liftMarkerTable, phaseMarker, h, TM0StmtApply]

/-- Away from the home marker, the lifted homing machine moves in `homeDirection left` without
changing its state. -/
theorem liftMarkerHome_step_away (left bit : Bool) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = false) :
    Turing.TM0.step (liftMarkerTable (fun _ => markerHomeTable) false) ⟨(left, bit), T⟩ =
      some ⟨(left, bit), T.move (homeDirection left)⟩ := by
  simp [TM0_step_apply, markerHomeTable, liftMarkerTable, phaseMarker, h, TM0StmtApply]

/-- From offset `homeDistance left n`, the lifted homing machine reaches home and halts after
`n` steps, changing only the tape's relative indexing. -/
theorem liftMarkerHome_run (left bit : Bool) (n : ℕ) (T : Turing.Tape CellCore)
    (h : PhaseHomeAt T (homeDistance left n)) :
    ∃ final : Turing.Tape CellCore,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => markerHomeTable) false) n
          ⟨(left, bit), T⟩ = some ⟨(left, bit), final⟩ ∧
      PhaseHomeAt final 0 ∧
      Turing.TM0.step (liftMarkerTable (fun _ => markerHomeTable) false)
          ⟨(left, bit), final⟩ = none ∧
      ∀ i : ℤ, final.nth i = T.nth (i - homeDistance left n) := by
  induction n generalizing T with
  | zero =>
    have hh : PhaseHomeAt T 0 := by simpa [homeDistance] using! h
    have hhead : T.head.2.2.1 = true := by simpa using! hh 0
    exact ⟨T, rfl, hh, liftMarkerHome_step_home (left, bit) T hhead, by simp [homeDistance]⟩
  | succ n ih =>
    have hhead : T.head.2.2.1 = false := by
      have hz : homeDistance left (n + 1) ≠ 0 := by
        cases left <;> dsimp [homeDistance] <;> omega
      have h0 := h 0
      have hd0 : decide (homeDistance left (n + 1) = 0) = false := by simp [hz]
      rw [zero_add, hd0] at h0
      exact h0
    have hnext : PhaseHomeAt (T.move (homeDirection left)) (homeDistance left n) := by
      cases left with
      | false =>
        have hm := phaseHomeAt_move_left T (homeDistance false (n + 1)) h
        convert! hm using 1; simp [homeDistance]
      | true =>
        have hm := phaseHomeAt_move_right T (homeDistance true (n + 1)) h
        convert! hm using 1; simp [homeDistance]
    obtain ⟨final, hr, hh, halt, data⟩ := ih (T.move (homeDirection left)) hnext
    refine ⟨final, ?_, hh, halt, ?_⟩
    · rw [show n + 1 = 1 + n by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, liftMarkerHome_step_away left bit T hhead]
      exact hr
    · intro i
      rw [data]
      cases left with
      | false =>
        change (T.move Turing.Dir.left).nth (i - (n : ℤ)) = T.nth (i - (↑(n + 1)))
        rw [Turing.Tape.move_left_nth]
        congr 1
        omega
      | true =>
        change (T.move Turing.Dir.right).nth (i - (-(n : ℤ))) = T.nth (i - (-(↑(n + 1))))
        rw [Turing.Tape.move_right_nth]
        congr 1
        omega

/-- With at least `n` coins, the lifted homing machine returns `bit` after exactly `n` reads and
transitions and recenters the tape at home. -/
theorem liftMarkerHome_coin_run (left bit : Bool) (n : ℕ) (T : Turing.Tape CellCore)
    (h : PhaseHomeAt T (homeDistance left n)) (coins : List Bool) (hlen : n ≤ coins.length) :
    ∃ final : Turing.Tape CellCore, PhaseHomeAt final 0 ∧
      (∀ i : ℤ, final.nth i = T.nth (i - homeDistance left n)) ∧
      coinTapeRunAux (fun _ => liftMarkerTable (fun _ => markerHomeTable) false)
          markerHomeAccept coins ⟨(left, bit), T⟩ = (some bit, n) ∧
      coinTapeTransitionCountAux (fun _ => liftMarkerTable (fun _ => markerHomeTable) false)
          coins ⟨(left, bit), T⟩ = n := by
  obtain ⟨final, hr, hh, halt, data⟩ := liftMarkerHome_run left bit n T h
  have hc := runFrom_coin_constant (liftMarkerTable (fun _ => markerHomeTable) false)
    markerHomeAccept n ⟨(left, bit), T⟩ ⟨(left, bit), final⟩ coins hr halt hlen
  exact ⟨final, hh, data, hc⟩

/-- Recentering a tape at home preserves its absolute marked interval, input track, and
marked-work invariant. -/
theorem phaseShift_invariants (T final : Turing.Tape CellCore) (off lo hi : ℤ) (n : ℕ)
    (initial : Turing.Tape CellCore)
    (hdata : ∀ i : ℤ, final.nth i = T.nth (i - off))
    (hmark : PhaseMarkAbs T off lo hi) (hinp : PhaseInputSame initial T off)
    (hwork : PhaseWorkMarked T off n) :
    PhaseMarkAbs final 0 lo hi ∧ PhaseInputSame initial final 0 ∧ PhaseWorkMarked final 0 n := by
  constructor
  · intro i
    rw [hdata i]
    constructor
    · intro hm
      obtain ⟨h1, h2⟩ := (hmark (i - off)).mp hm
      exact ⟨by omega, by omega⟩
    · intro hm
      exact (hmark (i - off)).mpr ⟨by omega, by omega⟩
  · constructor
    · intro i
      have hi1 := hdata i
      have hi2 := hinp (i - off)
      rw [hi1, hi2]
      rw [show (i - off) + off = i + 0 by omega]
    · intro i hm
      rw [hdata i] at hm ⊢
      rcases hwork (i - off) hm with hm2 | ⟨hw1, hw2⟩
      · exact Or.inl hm2
      · exact Or.inr ⟨by omega, by omega⟩

/-- The six control phases used to erase work and visitation tracks on both sides of home. -/
inductive SweepPhase : Type
  | rightErase | backHomeL | leftErase | backHomeR | stepRight | stepLeft

/-- A sweep phase paired with the Boolean result preserved during reset. -/
abbrev SweepState := SweepPhase × Bool

instance : Inhabited SweepState := ⟨.rightErase, false⟩

/-- Test whether a phase cell has a nonblank work symbol or a visitation mark. -/
def phaseBusy (s : CellCore) : Bool := s.2.1.isSome || s.2.2.2.isSome

/-- Clear the work and visitation tracks of a phase cell while preserving its input and home
marker. -/
def eraseCellP (s : CellCore) : CellCore := (s.1, none, s.2.2.1, none)

/-- The deterministic transition table that erases busy cells on both sides and returns the head
home. -/
def sweepResetTable : Turing.TM0.Machine CellCore SweepState := fun q s =>
  match q.1 with
  | .rightErase =>
      if phaseBusy s then some ((.stepRight, q.2), .write (eraseCellP s))
      else some ((.backHomeL, q.2), .move .left)
  | .stepRight => some ((.rightErase, q.2), .move .right)
  | .backHomeL =>
      if s.2.2.1 then some ((.leftErase, q.2), .move .left)
      else some ((.backHomeL, q.2), .move .left)
  | .leftErase =>
      if phaseBusy s then some ((.stepLeft, q.2), .write (eraseCellP s))
      else some ((.backHomeR, q.2), .move .right)
  | .stepLeft => some ((.leftErase, q.2), .move .left)
  | .backHomeR => if s.2.2.1 then none else some ((.backHomeR, q.2), .move .right)

/-- Extract the result bit stored in a sweep state. -/
def sweepResetAccept (q : SweepState) : Bool := q.2

/-- Halting of the constant sweep-reset machine is independent of the coin bit. -/
theorem sweepReset_commonHalt :
    ∀ q s, ((fun _ => sweepResetTable) false q s = none) ↔
      ((fun _ => sweepResetTable) true q s = none) := by
  intro q s
  obtain ⟨p, b⟩ := q
  cases p <;> exact Iff.rfl

/-- A sweep configuration is live unless it is in the final return phase at the home marker. -/
theorem sweep_coinHalt_live (q : SweepState) (T : Turing.Tape CellCore)
    (h : ¬ (q.1 = .backHomeR ∧ T.head.2.2.1 = true)) :
    coinHalt (fun _ => sweepResetTable) ⟨q, T⟩ = false := by
  obtain ⟨p, b⟩ := q
  cases p with
  | rightErase =>
      by_cases hb : phaseBusy T.head = true
      · simp [coinHalt, sweepResetTable, hb]
      · simp [coinHalt, sweepResetTable, hb]
  | stepRight => simp [coinHalt, sweepResetTable]
  | backHomeL =>
      by_cases hb : T.head.2.2.1 = true
      · simp [coinHalt, sweepResetTable, hb]
      · simp [coinHalt, sweepResetTable, hb]
  | leftErase =>
      by_cases hb : phaseBusy T.head = true
      · simp [coinHalt, sweepResetTable, hb]
      · simp [coinHalt, sweepResetTable, hb]
  | stepLeft => simp [coinHalt, sweepResetTable]
  | backHomeR =>
      cases hb : T.head.2.2.1 with
      | false => simp [coinHalt, sweepResetTable, hb]
      | true => exact absurd ⟨rfl, hb⟩ h

/-- The rightward erase phase clears a busy head cell and enters the right-step phase. -/
theorem sweep_step_erase_right (b : Bool) (T : Turing.Tape CellCore)
    (h : phaseBusy T.head = true) :
    Turing.TM0.step sweepResetTable ⟨(.rightErase, b), T⟩ =
      some ⟨(.stepRight, b), T.write (eraseCellP T.head)⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- The right-step phase moves right and resumes rightward erasure. -/
theorem sweep_step_stepRight (b : Bool) (T : Turing.Tape CellCore) :
    Turing.TM0.step sweepResetTable ⟨(.stepRight, b), T⟩ =
      some ⟨(.rightErase, b), T.move .right⟩ := by
  simp [TM0_step_apply, sweepResetTable, TM0StmtApply]

/-- At a clean cell, the rightward erase phase moves left and begins returning home. -/
theorem sweep_step_virgin_right (b : Bool) (T : Turing.Tape CellCore)
    (h : phaseBusy T.head = false) :
    Turing.TM0.step sweepResetTable ⟨(.rightErase, b), T⟩ =
      some ⟨(.backHomeL, b), T.move .left⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- At home, the leftward return phase moves left and starts leftward erasure. -/
theorem sweep_step_backHomeL_home (b : Bool) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = true) :
    Turing.TM0.step sweepResetTable ⟨(.backHomeL, b), T⟩ =
      some ⟨(.leftErase, b), T.move .left⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- Away from home, the leftward return phase continues moving left. -/
theorem sweep_step_backHomeL_away (b : Bool) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = false) :
    Turing.TM0.step sweepResetTable ⟨(.backHomeL, b), T⟩ =
      some ⟨(.backHomeL, b), T.move .left⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- The leftward erase phase clears a busy head cell and enters the left-step phase. -/
theorem sweep_step_erase_left (b : Bool) (T : Turing.Tape CellCore)
    (h : phaseBusy T.head = true) :
    Turing.TM0.step sweepResetTable ⟨(.leftErase, b), T⟩ =
      some ⟨(.stepLeft, b), T.write (eraseCellP T.head)⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- The left-step phase moves left and resumes leftward erasure. -/
theorem sweep_step_stepLeft (b : Bool) (T : Turing.Tape CellCore) :
    Turing.TM0.step sweepResetTable ⟨(.stepLeft, b), T⟩ =
      some ⟨(.leftErase, b), T.move .left⟩ := by
  simp [TM0_step_apply, sweepResetTable, TM0StmtApply]

/-- At a clean cell, the leftward erase phase moves right and begins the final return home. -/
theorem sweep_step_virgin_left (b : Bool) (T : Turing.Tape CellCore)
    (h : phaseBusy T.head = false) :
    Turing.TM0.step sweepResetTable ⟨(.leftErase, b), T⟩ =
      some ⟨(.backHomeR, b), T.move .right⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- The final rightward return phase halts at the home marker. -/
theorem sweep_step_backHomeR_home (b : Bool) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = true) :
    Turing.TM0.step sweepResetTable ⟨(.backHomeR, b), T⟩ = none := by
  simp [TM0_step_apply, sweepResetTable, h]

/-- Away from home, the final rightward return phase continues moving right. -/
theorem sweep_step_backHomeR_away (b : Bool) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = false) :
    Turing.TM0.step sweepResetTable ⟨(.backHomeR, b), T⟩ =
      some ⟨(.backHomeR, b), T.move .right⟩ := by
  simp [TM0_step_apply, sweepResetTable, h, TM0StmtApply]

/-- Erasing the head's work and visitation tracks preserves the home-marker invariant. -/
theorem phaseEraseWrite_home (T : Turing.Tape CellCore) (off : ℤ)
    (h : PhaseHomeAt T off) : PhaseHomeAt (T.write (eraseCellP T.head)) off := by
  intro i
  rw [Turing.Tape.write_nth]
  split
  · next h0 =>
    subst h0
    simpa [eraseCellP] using! h 0
  · next _ => exact h i

/-- Erasing the head's work and visitation tracks preserves the input-track invariant. -/
theorem phaseEraseWrite_input (T : Turing.Tape CellCore) (initial : Turing.Tape CellCore)
    (off : ℤ) (h : PhaseInputSame initial T off) :
    PhaseInputSame initial (T.write (eraseCellP T.head)) off := by
  intro i
  rw [Turing.Tape.write_nth]
  split
  · next h0 =>
    subst h0
    simpa [eraseCellP] using! h 0
  · next _ => exact h i

/-- Erasing the head's work and visitation tracks makes the head cell clean. -/
theorem phaseEraseWrite_head_busy (T : Turing.Tape CellCore) :
    phaseBusy ((T.write (eraseCellP T.head)).head) = false := by
  show phaseBusy (eraseCellP T.head) = false
  simp [phaseBusy, eraseCellP]

/-- Erasing the head leaves every cell at a nonzero relative index unchanged. -/
theorem phaseEraseWrite_nth_of_ne (T : Turing.Tape CellCore) (i : ℤ) (h0 : i ≠ 0) :
    (T.write (eraseCellP T.head)).nth i = T.nth i := by
  rw [Turing.Tape.write_nth]
  split
  · next h => exact absurd h h0
  · next => rfl

/-- The busy predicate on the tape head equals its value at relative index zero. -/
theorem phaseBusy_head (T : Turing.Tape CellCore) : phaseBusy T.head = phaseBusy (T.nth 0) := rfl

/-- After moving right, the busy predicate at index `i` equals its former value at index `i +
1`. -/
theorem phaseBusy_move_right (T : Turing.Tape CellCore) (i : ℤ) :
    phaseBusy ((T.move .right).nth i) = phaseBusy (T.nth (i + 1)) := by
  rw [Turing.Tape.move_right_nth]

/-- After moving left, the busy predicate at index `i` equals its former value at index `i - 1`. -/
theorem phaseBusy_move_left (T : Turing.Tape CellCore) (i : ℤ) :
    phaseBusy ((T.move .left).nth i) = phaseBusy (T.nth (i - 1)) := by
  rw [Turing.Tape.move_left_nth]

/-- Moving a tape right and then left returns the original tape. -/
theorem tape_move_right_left (T : Turing.Tape CellCore) :
    (T.move .right).move .left = T := by
  apply Qatlib.Concepts.ClassicalTape.TapeCompilation.tape_ext
  intro i
  rw [Turing.Tape.move_left_nth, Turing.Tape.move_right_nth]
  have h2 : i - 1 + 1 = i := by omega
  rw [h2]

/-- Moving a tape left and then right returns the original tape. -/
theorem tape_move_left_right (T : Turing.Tape CellCore) :
    (T.move .left).move .right = T := by
  apply Qatlib.Concepts.ClassicalTape.TapeCompilation.tape_ext
  intro i
  rw [Turing.Tape.move_right_nth, Turing.Tape.move_left_nth]
  have h2 : i + 1 - 1 = i := by omega
  rw [h2]

/-- Under the stated busy-interval and cleanliness hypotheses, the right sweep clears all
nonnegative absolute positions in `2 * k + 3` steps and enters the leftward return phase,
preserving the input and home marker. -/
theorem sweepRight_erase (b : Bool) (k : ℕ) (T : Turing.Tape CellCore) (off : ℤ)
    (initial : Turing.Tape CellCore) (hoff : 0 ≤ off)
    (hhome : PhaseHomeAt T off) (hinp : PhaseInputSame initial T off)
    (hpre : ∀ i : ℤ, 0 ≤ i + off → i < 0 → phaseBusy (T.nth i) = false)
    (hbusy : ∀ i : ℤ, 0 ≤ i → i ≤ (k : ℤ) → phaseBusy (T.nth i) = true)
    (hvir : ∀ i : ℤ, (k : ℤ) < i → phaseBusy (T.nth i) = false) :
    ∃ T' : Turing.Tape CellCore,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable (2 * k + 3) ⟨(.rightErase, b), T⟩ =
        some ⟨(.backHomeL, b), T'⟩ ∧
      PhaseHomeAt T' (off + (k : ℤ)) ∧ PhaseInputSame initial T' (off + (k : ℤ)) ∧
      (∀ i : ℤ, 0 ≤ i + (off + (k : ℤ)) → phaseBusy (T'.nth i) = false) ∧
      (∀ i : ℤ, i + (off + (k : ℤ)) < 0 →
        phaseBusy (T'.nth i) = phaseBusy (T.nth (i + (k : ℤ)))) := by
  induction k generalizing T off with
  | zero =>
      have hb0 : phaseBusy T.head = true := by
        rw [phaseBusy_head]
        exact hbusy 0 (by omega) (by omega)
      have hv1 : phaseBusy (T.nth 1) = false := hvir 1 (by omega)
      have hstep1 := sweep_step_erase_right b T hb0
      have hstep2 := sweep_step_stepRight b (T.write (eraseCellP T.head))
      have hhead2 : phaseBusy ((T.write (eraseCellP T.head)).move .right).head = false := by
        have h1 : ((T.write (eraseCellP T.head)).move .right).head
            = (T.write (eraseCellP T.head)).nth 1 := by
          rw [show ((T.write (eraseCellP T.head)).move .right).head
              = ((T.write (eraseCellP T.head)).move .right).nth 0 from rfl,
            Turing.Tape.move_right_nth]
          simp
        rw [h1, phaseEraseWrite_nth_of_ne _ 1 (by decide)]
        exact hv1
      have hstep3 := sweep_step_virgin_right b _ hhead2
      refine ⟨(T.write (eraseCellP T.head)).move .right |>.move .left, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show (2 * 0 + 3 : ℕ) = 1 + (1 + 1) by rfl, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep1, Option.bind_some,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep2,
          Option.bind_some, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep3]
      · have h1 := phaseEraseWrite_home T off hhome
        have h2 := phaseHomeAt_move_right _ off h1
        have h3 := phaseHomeAt_move_left _ (off + 1) h2
        simpa using! h3
      · have h1 := phaseEraseWrite_input T initial off hinp
        have h2 := phaseInputSame_move_right initial _ off h1
        have h3 := phaseInputSame_move_left initial _ (off + 1) h2
        simpa using! h3
      · intro i hi
        have hcancel : ((T.write (eraseCellP T.head)).move .right).move .left
            = T.write (eraseCellP T.head) := tape_move_right_left _
        rw [hcancel]
        by_cases h0 : i = 0
        · subst h0
          rw [Turing.Tape.nth_zero, phaseEraseWrite_head_busy]
        · rw [phaseEraseWrite_nth_of_ne _ i h0]
          by_cases hi1 : 0 < i
          · exact hvir i (by omega)
          · exact hpre i (by omega) (by omega)
      · intro i hi
        have hcancel : ((T.write (eraseCellP T.head)).move .right).move .left
            = T.write (eraseCellP T.head) := tape_move_right_left _
        rw [hcancel, phaseEraseWrite_nth_of_ne _ i (by omega)]
        norm_num
  | succ k ih =>
      have hb0 : phaseBusy T.head = true := by
        rw [phaseBusy_head]
        exact hbusy 0 (by omega) (by omega)
      have hstep1 := sweep_step_erase_right b T hb0
      have hstep2 := sweep_step_stepRight b (T.write (eraseCellP T.head))
      have hhome1 := phaseHomeAt_move_right _ off (phaseEraseWrite_home T off hhome)
      have hinp1 := phaseInputSame_move_right initial _ off
        (phaseEraseWrite_input T initial off hinp)
      have hshift (j : ℤ) (hj : j + 1 ≠ 0) : ((T.write (eraseCellP T.head)).move .right).nth j
          = T.nth (j + 1) := by
        rw [Turing.Tape.move_right_nth, phaseEraseWrite_nth_of_ne _ (j + 1) hj]
      have hpre1 : ∀ j : ℤ, 0 ≤ j + (off + 1) → j < 0 →
          phaseBusy (((T.write (eraseCellP T.head)).move .right).nth j) = false := by
        intro j hj1 hj2
        by_cases hj : j = -1
        · subst hj
          rw [Turing.Tape.move_right_nth, show (-1 : ℤ) + 1 = 0 by omega,
            Turing.Tape.nth_zero]
          exact phaseEraseWrite_head_busy _
        · rw [hshift j (by omega)]
          exact hpre (j + 1) (by omega) (by omega)
      have hbusy1 : ∀ i : ℤ, 0 ≤ i → i ≤ (k : ℤ) →
          phaseBusy (((T.write (eraseCellP T.head)).move .right).nth i) = true := by
        intro i hi1 hi2
        rw [hshift i (by omega)]
        exact hbusy (i + 1) (by omega) (by omega)
      have hvir1 : ∀ i : ℤ, (k : ℤ) < i →
          phaseBusy (((T.write (eraseCellP T.head)).move .right).nth i) = false := by
        intro i hi
        rw [hshift i (by omega)]
        exact hvir (i + 1) (by omega)
      obtain ⟨T', hr', hhome', hinp', hclean', hbelow'⟩ :=
        ih ((T.write (eraseCellP T.head)).move .right) (off + 1) (by omega) hhome1 hinp1 hpre1
          hbusy1 hvir1
      refine ⟨T', ?_, ?_, ?_, ?_, ?_⟩
      · rw [show (2 * (k + 1) + 3 : ℕ) = 1 + (1 + (2 * k + 3)) by omega,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep1,
          Option.bind_some,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep2,
          Option.bind_some]
        exact hr'
      · rw [show off + ((k + 1 : ℕ) : ℤ) = off + 1 + (k : ℤ) by push_cast; ring]
        exact hhome'
      · rw [show off + ((k + 1 : ℕ) : ℤ) = off + 1 + (k : ℤ) by push_cast; ring]
        exact hinp'
      · rw [show off + ((k + 1 : ℕ) : ℤ) = off + 1 + (k : ℤ) by push_cast; ring]
        exact hclean'
      · intro i hi
        have hk : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
        rw [hk] at hi
        have hargs : i + (k : ℤ) + 1 = i + ((k + 1 : ℕ) : ℤ) := by rw [hk]; omega
        rw [hbelow' i (by omega), hshift (i + (k : ℤ)) (by omega), hargs]

/-- The leftward return from offset `k` takes `k + 1` steps to enter leftward erasure at offset
`-1`, preserving the tape contents up to reindexing. -/
theorem sweepBackHomeL_return (b : Bool) (k : ℕ) (T : Turing.Tape CellCore)
    (initial : Turing.Tape CellCore)
    (hhome : PhaseHomeAt T (k : ℤ)) (hinp : PhaseInputSame initial T (k : ℤ)) :
    ∃ T' : Turing.Tape CellCore,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable (k + 1) ⟨(.backHomeL, b), T⟩ =
        some ⟨(.leftErase, b), T'⟩ ∧
      PhaseHomeAt T' (-1) ∧ PhaseInputSame initial T' (-1) ∧
      (∀ i : ℤ, T'.nth i = T.nth (i - 1 - (k : ℤ))) := by
  induction k generalizing T with
  | zero =>
      have hhead : T.head.2.2.1 = true := by simpa using! hhome 0
      have hstep := sweep_step_backHomeL_home b T hhead
      refine ⟨T.move .left, ?_, ?_, ?_, ?_⟩
      · rw [show (0 + 1 : ℕ) = 1 by rfl, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep]
      · have h := phaseHomeAt_move_left T 0 hhome
        simpa using! h
      · have h := phaseInputSame_move_left initial T 0 hinp
        simpa using! h
      · intro i
        rw [Turing.Tape.move_left_nth]
        congr 1
        omega
  | succ k ih =>
      have hhead : T.head.2.2.1 = false := by
        have h0 := hhome 0
        have hk : ((k : ℕ) + 1 : ℤ) ≠ 0 := by omega
        simpa [hk] using! h0
      have hstep := sweep_step_backHomeL_away b T hhead
      have hhome1 : PhaseHomeAt (T.move .left) ((k : ℕ) : ℤ) := by
        have h := phaseHomeAt_move_left T (((k + 1 : ℕ) : ℤ)) hhome
        have hcast : (((k + 1 : ℕ) : ℤ) - 1 : ℤ) = ((k : ℕ) : ℤ) := by omega
        rw [hcast] at h
        exact h
      have hinp1 : PhaseInputSame initial (T.move .left) ((k : ℕ) : ℤ) := by
        have h := phaseInputSame_move_left initial T (((k + 1 : ℕ) : ℤ)) hinp
        have hcast : (((k + 1 : ℕ) : ℤ) - 1 : ℤ) = ((k : ℕ) : ℤ) := by omega
        rw [hcast] at h
        exact h
      obtain ⟨T', hr', hhome', hinp', hdata'⟩ := ih (T.move .left) hhome1 hinp1
      refine ⟨T', ?_, hhome', hinp', ?_⟩
      · rw [show ((k : ℕ) + 1 + 1 : ℕ) = 1 + (k + 1) by omega,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep]
        exact hr'
      · intro i
        rw [hdata' i, Turing.Tape.move_left_nth]
        congr 1
        have hk : ((k : ℕ) + 1 : ℤ) = (k : ℤ) + 1 := by omega
        omega

/-- Under the stated busy-interval and cleanliness hypotheses, the left sweep clears every busy
cell in `2 * k + 3` steps and enters the rightward return phase, preserving the input and
home marker. -/
theorem sweepLeft_erase (b : Bool) (k : ℕ) (T : Turing.Tape CellCore) (off : ℤ)
    (initial : Turing.Tape CellCore)
    (hhome : PhaseHomeAt T off) (hinp : PhaseInputSame initial T off)
    (hbusy : ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ 0 → phaseBusy (T.nth i) = true)
    (hvir : ∀ i : ℤ, i < -(k : ℤ) → phaseBusy (T.nth i) = false)
    (hclean : ∀ i : ℤ, 0 < i → phaseBusy (T.nth i) = false) :
    ∃ T' : Turing.Tape CellCore,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable (2 * k + 3) ⟨(.leftErase, b), T⟩ =
        some ⟨(.backHomeR, b), T'⟩ ∧
      PhaseHomeAt T' (off - (k : ℤ)) ∧ PhaseInputSame initial T' (off - (k : ℤ)) ∧
      (∀ i : ℤ, phaseBusy (T'.nth i) = false) := by
  induction k generalizing T off with
  | zero =>
      have hb0 : phaseBusy T.head = true := by
        rw [phaseBusy_head]
        exact hbusy 0 (by omega) (by omega)
      have hvm1 : phaseBusy ((T.write (eraseCellP T.head)).move .left).head = false := by
        have h1 : ((T.write (eraseCellP T.head)).move .left).head
            = (T.write (eraseCellP T.head)).nth (-1) := by
          rw [show ((T.write (eraseCellP T.head)).move .left).head
              = ((T.write (eraseCellP T.head)).move .left).nth 0 from rfl,
            Turing.Tape.move_left_nth]
          simp
        rw [h1, phaseEraseWrite_nth_of_ne _ (-1) (by decide)]
        exact hvir (-1) (by omega)
      have hstep1 := sweep_step_erase_left b T hb0
      have hstep2 := sweep_step_stepLeft b (T.write (eraseCellP T.head))
      have hstep3 := sweep_step_virgin_left b _ hvm1
      refine ⟨(T.write (eraseCellP T.head)).move .left |>.move .right, ?_, ?_, ?_, ?_⟩
      · rw [show (2 * 0 + 3 : ℕ) = 1 + (1 + 1) by rfl, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep1, Option.bind_some,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep2,
          Option.bind_some, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep3]
      · have h1 := phaseEraseWrite_home T off hhome
        have h2 := phaseHomeAt_move_left _ off h1
        have h3 := phaseHomeAt_move_right _ (off - 1) h2
        simpa using! h3
      · have h1 := phaseEraseWrite_input T initial off hinp
        have h2 := phaseInputSame_move_left initial _ off h1
        have h3 := phaseInputSame_move_right initial _ (off - 1) h2
        simpa using! h3
      · intro i
        have hcancel : ((T.write (eraseCellP T.head)).move .left).move .right
            = T.write (eraseCellP T.head) := tape_move_left_right _
        rw [hcancel]
        by_cases h0 : i = 0
        · subst h0
          rw [Turing.Tape.nth_zero, phaseEraseWrite_head_busy]
        · rw [phaseEraseWrite_nth_of_ne _ i h0]
          by_cases hi1 : 0 < i
          · exact hclean i hi1
          · exact hvir i (by omega)
  | succ k ih =>
      have hb0 : phaseBusy T.head = true := by
        rw [phaseBusy_head]
        exact hbusy 0 (by omega) (by omega)
      have hstep1 := sweep_step_erase_left b T hb0
      have hstep2 := sweep_step_stepLeft b (T.write (eraseCellP T.head))
      have hhome1 : PhaseHomeAt ((T.write (eraseCellP T.head)).move .left) (off - 1) := by
        have h := phaseHomeAt_move_left _ off (phaseEraseWrite_home T off hhome)
        simpa using! h
      have hinp1 : PhaseInputSame initial ((T.write (eraseCellP T.head)).move .left) (off - 1) := by
        have h := phaseInputSame_move_left initial _ off
          (phaseEraseWrite_input T initial off hinp)
        simpa using! h
      have hshift (j : ℤ) (hj : j - 1 ≠ 0) :
          ((T.write (eraseCellP T.head)).move .left).nth j = T.nth (j - 1) := by
        rw [Turing.Tape.move_left_nth, phaseEraseWrite_nth_of_ne _ (j - 1) hj]
      have hk : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      have hbusy1 : ∀ i : ℤ, -(k : ℤ) ≤ i → i ≤ 0 →
          phaseBusy (((T.write (eraseCellP T.head)).move .left).nth i) = true := by
        intro i hi1 hi2
        rw [hshift i (by omega)]
        refine hbusy (i - 1) ?_ ?_
        · rw [hk]; omega
        · omega
      have hvir1 : ∀ i : ℤ, i < -(k : ℤ) →
          phaseBusy (((T.write (eraseCellP T.head)).move .left).nth i) = false := by
        intro i hi
        rw [hshift i (by omega)]
        exact hvir (i - 1) (by omega)
      have hclean1 : ∀ i : ℤ, 0 < i →
          phaseBusy (((T.write (eraseCellP T.head)).move .left).nth i) = false := by
        intro i hi
        by_cases h0 : i = 1
        · subst h0
          rw [Turing.Tape.move_left_nth, show (1 : ℤ) - 1 = 0 by omega,
            Turing.Tape.nth_zero]
          exact phaseEraseWrite_head_busy _
        · rw [hshift i (by omega)]
          exact hclean (i - 1) (by omega)
      obtain ⟨T', hr', hhome', hinp', hclean'⟩ :=
        ih ((T.write (eraseCellP T.head)).move .left) (off - 1) hhome1 hinp1 hbusy1 hvir1 hclean1
      refine ⟨T', ?_, ?_, ?_, hclean'⟩
      · rw [show (2 * (k + 1) + 3 : ℕ) = 1 + (1 + (2 * k + 3)) by omega,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep1,
          Option.bind_some,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep2,
          Option.bind_some]
        exact hr'
      · rw [show off - ((k + 1 : ℕ) : ℤ) = off - 1 - (k : ℤ) by push_cast; ring]
        exact hhome'
      · rw [show off - ((k + 1 : ℕ) : ℤ) = off - 1 - (k : ℤ) by push_cast; ring]
        exact hinp'

/-- From offset `-k`, the final rightward return reaches home and halts after `k` steps,
preserving tape contents up to reindexing. -/
theorem sweepBackHomeR_return (b : Bool) (k : ℕ) (T : Turing.Tape CellCore)
    (initial : Turing.Tape CellCore)
    (hhome : PhaseHomeAt T (-(k : ℤ))) (hinp : PhaseInputSame initial T (-(k : ℤ))) :
    ∃ T' : Turing.Tape CellCore,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable k ⟨(.backHomeR, b), T⟩ =
        some ⟨(.backHomeR, b), T'⟩ ∧
      PhaseHomeAt T' 0 ∧ PhaseInputSame initial T' 0 ∧
      Turing.TM0.step sweepResetTable ⟨(.backHomeR, b), T'⟩ = none ∧
      (∀ i : ℤ, T'.nth i = T.nth (i + (k : ℤ))) := by
  induction k generalizing T with
  | zero =>
      have hhead : T.head.2.2.1 = true := by
        have h0 := hhome 0
        simpa using! h0
      refine ⟨T, rfl, by simpa using! hhome, by simpa using! hinp,
        sweep_step_backHomeR_home b T hhead, ?_⟩
      intro i
      congr 1
      omega
  | succ k ih =>
      have hhead : T.head.2.2.1 = false := by
        have h0 := phaseHomeAt_head T (-(((k + 1 : ℕ) : ℤ))) hhome
        have hk : (-(((k + 1 : ℕ) : ℤ))) ≠ 0 := by push_cast; omega
        rw [h0, decide_eq_false_iff_not]
        exact hk
      have hstep := sweep_step_backHomeR_away b T hhead
      have hhome1 : PhaseHomeAt (T.move .right) (-(k : ℤ)) := by
        have h := phaseHomeAt_move_right T (-((k + 1 : ℕ) : ℤ)) hhome
        have hcast : (-((k + 1 : ℕ) : ℤ) + 1 : ℤ) = -((k : ℕ) : ℤ) := by
          push_cast
          ring
        rw [hcast] at h
        exact h
      have hinp1 : PhaseInputSame initial (T.move .right) (-(k : ℤ)) := by
        have h := phaseInputSame_move_right initial T (-((k + 1 : ℕ) : ℤ)) hinp
        have hcast : (-((k + 1 : ℕ) : ℤ) + 1 : ℤ) = -((k : ℕ) : ℤ) := by
          push_cast
          ring
        rw [hcast] at h
        exact h
      obtain ⟨T', hr', hhome', hinp', hhalt', hdata'⟩ := ih (T.move .right) hhome1 hinp1
      refine ⟨T', ?_, hhome', hinp', hhalt', ?_⟩
      · rw [show ((k : ℕ) + 1 : ℕ) = 1 + k by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep]
        exact hr'
      · intro i
        rw [hdata' i, Turing.Tape.move_right_nth]
        congr 1
        push_cast
        ring

/-- A sweep reset of the busy interval `[L, R]` containing home halts at home after `3 * R.toNat
+ 3 * (-L).toNat + 5` steps, preserving input and clearing every busy cell. -/
theorem sweepReset_run (bit : Bool) (T initial : Turing.Tape CellCore) (L R : ℤ)
    (hhome : PhaseHomeAt T 0) (hinp : PhaseInputSame initial T 0)
    (hregion : ∀ i : ℤ, phaseBusy (T.nth i) = true ↔ L ≤ i ∧ i ≤ R)
    (hL : L ≤ 0) (hR : 0 ≤ R) :
    ∃ T' : Turing.Tape CellCore,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable
        (3 * R.toNat + 3 * (-L).toNat + 5) ⟨(.rightErase, bit), T⟩ =
        some ⟨(.backHomeR, bit), T'⟩ ∧
      Turing.TM0.step sweepResetTable ⟨(.backHomeR, bit), T'⟩ = none ∧
      PhaseHomeAt T' 0 ∧ PhaseInputSame initial T' 0 ∧
      (∀ i : ℤ, phaseBusy (T'.nth i) = false) := by
  have hRnat : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR
  have hbusyR : ∀ i : ℤ, 0 ≤ i → i ≤ ((R.toNat : ℕ) : ℤ) → phaseBusy (T.nth i) = true := by
    intro i hi1 hi2
    rw [hRnat] at hi2
    exact (hregion i).mpr ⟨by omega, hi2⟩
  have hvirR : ∀ i : ℤ, ((R.toNat : ℕ) : ℤ) < i → phaseBusy (T.nth i) = false := by
    intro i hi
    rw [hRnat] at hi
    by_cases hb : phaseBusy (T.nth i) = true
    · have hc := (hregion i).mp hb
      omega
    · simpa using! hb
  have hpreR : ∀ i : ℤ, 0 ≤ i + (0 : ℤ) → i < 0 → phaseBusy (T.nth i) = false :=
    fun _ h1 h2 => absurd h2 (by omega)
  obtain ⟨T₁, hrun₁, hhome₁, hinp₁, hclean₁, hbelow₁⟩ :=
    sweepRight_erase bit R.toNat T 0 initial (by omega) hhome hinp hpreR hbusyR hvirR
  have hRnat0 : (0 : ℤ) + ((R.toNat : ℕ) : ℤ) = R := by
    rw [hRnat]
    omega
  rw [hRnat0] at hclean₁ hbelow₁
  obtain ⟨T₂, hrun₂, hhome₂, hinp₂, hdata₂⟩ :=
    sweepBackHomeL_return bit R.toNat T₁ initial (by simpa using! hhome₁)
      (by simpa using! hinp₁)
  rw [hRnat] at hdata₂
  have hbelow_T (j : ℤ) (hj : j < 0) :
      phaseBusy (T₁.nth (j - R)) = phaseBusy (T.nth j) := by
    have hb := hbelow₁ (j - R) (by omega)
    rw [hRnat] at hb
    have hjj : j - R + R = j := by omega
    rw [hjj] at hb
    exact hb
  have hbusy₂ (i : ℤ) (h1 : L ≤ i - 1) (h2 : i - 1 ≤ -1) : phaseBusy (T₂.nth i) = true := by
    rw [hdata₂ i, hbelow_T (i - 1) (by omega)]
    exact (hregion (i - 1)).mpr ⟨h1, by omega⟩
  have hvir₂ (i : ℤ) (habs : i - 1 < L) : phaseBusy (T₂.nth i) = false := by
    rw [hdata₂ i, hbelow_T (i - 1) (by omega)]
    by_cases hbx : phaseBusy (T.nth (i - 1)) = true
    · have hc := (hregion (i - 1)).mp hbx
      omega
    · simpa using! hbx
  have hclean₂ (i : ℤ) (hi : 0 < i) : phaseBusy (T₂.nth i) = false := by
    rw [hdata₂ i]
    exact hclean₁ (i - 1 - R) (by omega)
  by_cases hLz : L = 0
  · subst hLz
    have hvirhead : phaseBusy T₂.head = false := by
      rw [phaseBusy_head, hdata₂ 0, hbelow_T (0 - 1) (by omega)]
      by_cases hbx : phaseBusy (T.nth (0 - 1)) = true
      · have hc := (hregion (0 - 1)).mp hbx
        omega
      · simpa using! hbx
    have hstep3 := sweep_step_virgin_left bit T₂ hvirhead
    have hhome3 : PhaseHomeAt (T₂.move .right) 0 := by
      have h := phaseHomeAt_move_right T₂ (-1) hhome₂
      simpa using! h
    have hinp3 : PhaseInputSame initial (T₂.move .right) 0 := by
      have h := phaseInputSame_move_right initial T₂ (-1) hinp₂
      simpa using! h
    obtain ⟨T', hrun₄, hhome₄, hinp₄, hhalt₄, hdata₄⟩ :=
      sweepBackHomeR_return bit 0 (T₂.move .right) initial hhome3 hinp3
    refine ⟨T', ?_, hhalt₄, hhome₄, hinp₄, ?_⟩
    · rw [show (3 * R.toNat + 3 * (-(0 : ℤ)).toNat + 5 : ℕ)
          = (2 * R.toNat + 3) + ((R.toNat + 1) + (1 + 0)) by omega,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hrun₁, Option.bind_some,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hrun₂, Option.bind_some,
        show (1 + 0 : ℕ) = 1 by rfl,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep3]
      exact hrun₄
    · intro i
      rw [hdata₄ i, Turing.Tape.move_right_nth]
      have hn : i + ((0 : ℕ) : ℤ) + 1 = i + 1 := by push_cast; omega
      rw [hn]
      by_cases hi : 0 ≤ i
      · exact hclean₂ (i + 1) (by omega)
      · exact hvir₂ (i + 1) (by omega)
  · have hLneg : L < 0 := by omega
    have hLnat : (((-1 - L).toNat : ℕ) : ℤ) = -1 - L := Int.toNat_of_nonneg (by omega)
    have hLnat' : (((-L).toNat : ℕ) : ℤ) = -L := Int.toNat_of_nonneg (by omega)
    have hkk : (-L).toNat = (-1 - L).toNat + 1 := by
      have ha := hLnat'
      have hb := hLnat
      omega
    obtain ⟨T₃, hrun₃, hhome₃, hinp₃, hclean₃⟩ :=
      sweepLeft_erase bit (-1 - L).toNat T₂ (-1) initial hhome₂ hinp₂
        (fun i hi1 hi2 => hbusy₂ i (by rw [hLnat] at hi1; omega) (by omega))
        (fun i hi => hvir₂ i (by rw [hLnat] at hi; omega))
        hclean₂
    have hoffk : (-1 : ℤ) - (-1 - L) = L := by omega
    rw [hLnat] at hhome₃ hinp₃
    rw [hoffk] at hhome₃ hinp₃
    have hnegL : -(((-L).toNat : ℕ) : ℤ) = L := by rw [hLnat']; simp
    obtain ⟨T', hrun₄, hhome₄, hinp₄, hhalt₄, hdata₄⟩ :=
      sweepBackHomeR_return bit (-L).toNat T₃ initial (by rwa [hnegL]) (by rwa [hnegL])
    refine ⟨T', ?_, hhalt₄, hhome₄, hinp₄, ?_⟩
    · rw [show (3 * R.toNat + 3 * (-L).toNat + 5 : ℕ)
          = (2 * R.toNat + 3) + ((R.toNat + 1) + ((2 * (-1 - L).toNat + 3) + (-L).toNat)) by omega,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hrun₁, Option.bind_some,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hrun₂, Option.bind_some,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hrun₃, Option.bind_some]
      exact hrun₄
    · intro i
      rw [hdata₄ i]
      exact hclean₃ _

/-- With enough coins, resetting the busy interval `[L, R]` returns the stored bit with exactly
`3 * R.toNat + 3 * (-L).toNat + 5` reads and transitions, leaving a clean tape at home with
unchanged input. -/
theorem sweepReset_coin_run (bit : Bool) (T initial : Turing.Tape CellCore) (L R : ℤ)
    (coins : List Bool)
    (hhome : PhaseHomeAt T 0) (hinp : PhaseInputSame initial T 0)
    (hregion : ∀ i : ℤ, phaseBusy (T.nth i) = true ↔ L ≤ i ∧ i ≤ R)
    (hL : L ≤ 0) (hR : 0 ≤ R)
    (hlen : 3 * R.toNat + 3 * (-L).toNat + 5 ≤ coins.length) :
    ∃ T' : Turing.Tape CellCore,
      PhaseHomeAt T' 0 ∧ PhaseInputSame initial T' 0 ∧
      (∀ i : ℤ, phaseBusy (T'.nth i) = false) ∧
      coinTapeRunAux (fun _ => sweepResetTable) sweepResetAccept coins
          ⟨(.rightErase, bit), T⟩ =
        (some bit, 3 * R.toNat + 3 * (-L).toNat + 5) ∧
      coinTapeTransitionCountAux (fun _ => sweepResetTable) coins
          ⟨(.rightErase, bit), T⟩ =
        3 * R.toNat + 3 * (-L).toNat + 5 := by
  obtain ⟨T', hrun, hhalt, hhome', hinp', hclean⟩ :=
    sweepReset_run bit T initial L R hhome hinp hregion hL hR
  have hc := runFrom_coin_constant sweepResetTable sweepResetAccept
    (3 * R.toNat + 3 * (-L).toNat + 5) ⟨(.rightErase, bit), T⟩ ⟨(.backHomeR, bit), T'⟩
    coins hrun hhalt hlen
  exact ⟨T', hhome', hinp', hclean, hc⟩

/-- Recentering a tape at home preserves the initial contents of its unmarked work cells. -/
theorem phaseUnmarkedWork_shift (initial T final : Turing.Tape CellCore) (off : ℤ)
    (hdata : ∀ i : ℤ, final.nth i = T.nth (i - off))
    (h : PhaseUnmarkedWork initial T off) :
    PhaseUnmarkedWork initial final 0 := by
  intro i hi
  have hi' : (T.nth (i - off)).2.2.2 = none := by
    rw [← hdata i]
    exact hi
  rw [hdata i, h (i - off) hi', show i - off + off = i + 0 by omega]

/-- The homing distance computed from a side bit consistent with `off` equals `off`. -/
theorem side_homeDistance (sf : Bool) (off : ℤ) (hside : SideAt sf off) :
    homeDistance sf (if sf then (-off).toNat else off.toNat) = off := by
  cases sf with
  | false =>
      have h0 : ¬ (off < 0) := by
        intro hlt
        exact absurd (hside.1 hlt) (by simp)
      have hoff : (off.toNat : ℤ) = off := Int.toNat_of_nonneg (by omega)
      simp [homeDistance, hoff]
  | true =>
      have h0 : ¬ (0 < off) := by
        intro hgt
        exact absurd (hside.2 hgt) (by simp)
      have hoff : (((-off).toNat : ℕ) : ℤ) = -off := Int.toNat_of_nonneg (by omega)
      simp [homeDistance, hoff]

/-- Under the mark, work, and initial-content invariants, busy cells occupy exactly the absolute
interval from `lo` to `max hi (n - 1)` when the marked interval contains home. -/
theorem phaseBusy_region (T initial : Turing.Tape CellCore) (off lo hi : ℤ) (n : ℕ)
    (hmark : PhaseMarkAbs T off lo hi) (hwork : PhaseWorkMarked T off n)
    (hucopy : PhaseUnmarkedWork initial T off)
    (href : ∀ a : ℤ, 0 ≤ a → a < (n : ℤ) → (initial.nth a).2.1 ≠ none)
    (hcover : lo ≤ 0 ∧ 0 ≤ hi) (i : ℤ) :
    phaseBusy (T.nth i) = true ↔
      (lo ≤ i + off ∧ i + off ≤ max hi ((n : ℤ) - 1)) := by
  constructor
  · intro hb
    rcases Bool.or_eq_true_iff.mp hb with hw | hm
    · have hwne : (T.nth i).2.1 ≠ none := by
        intro hnone
        rw [hnone] at hw
        simp at hw
      rcases hwork i hwne with hmm | ⟨hw1, hw2⟩
      · have hc2 := (hmark i).mp hmm
        exact ⟨hc2.1, by omega⟩
      · exact ⟨by omega, by omega⟩
    · have hmne : (T.nth i).2.2.2 ≠ none := by
        intro hnone
        rw [hnone] at hm
        simp at hm
      have hc2 := (hmark i).mp hmne
      exact ⟨hc2.1, by omega⟩
  · intro hcon
    obtain ⟨h1, h2⟩ := hcon
    by_cases hval : (T.nth i).2.2.2 = none
    · have habsHi : ¬ (i + off ≤ hi) := by
        intro hle
        exact absurd hval ((hmark i).mpr ⟨h1, hle⟩)
      have habs : 0 ≤ i + off ∧ i + off < (n : ℤ) := by omega
      have hne := href (i + off) habs.1 habs.2
      have hworkEq : (T.nth i).2.1 = (initial.nth (i + off)).2.1 := hucopy i hval
      have hwsome : ((initial.nth (i + off)).2.1).isSome = true := by
        cases hv : (initial.nth (i + off)).2.1 with
        | none => exact absurd hv hne
        | some b => simp
      simp [phaseBusy, hworkEq, hwsome]
    · have hmsome : ((T.nth i).2.2.2).isSome = true := by
        cases hv : (T.nth i).2.2.2 with
        | none => exact absurd hv hval
        | some b => simp
      simp [phaseBusy, hmsome]

/-- A tape satisfying the phase invariants can first return home and then clear all work and
visitation tracks in the stated numbers of steps, preserving input and the stored result
bit. -/
theorem phaseHomeSweepReset (Tf initial : Turing.Tape CellCore)
    (off' lo' hi' : ℤ) (sf bit : Bool) (n : ℕ)
    (hhome : PhaseHomeAt Tf off') (hside : SideAt sf off')
    (hinp : PhaseInputSame initial Tf off')
    (hmark : PhaseMarkAbs Tf off' lo' hi') (hwork : PhaseWorkMarked Tf off' n)
    (hucopy : PhaseUnmarkedWork initial Tf off')
    (hcover : lo' ≤ 0 ∧ 0 ≤ hi')
    (href : ∀ a : ℤ, 0 ≤ a → a < (n : ℤ) → (initial.nth a).2.1 ≠ none) :
    ∃ Th T'' : Turing.Tape CellCore,
      (Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => markerHomeTable) false)
        (if sf then (-off').toNat else off'.toNat) ⟨(sf, bit), Tf⟩ =
          some ⟨(sf, bit), Th⟩ ∧
        Turing.TM0.step (liftMarkerTable (fun _ => markerHomeTable) false)
          ⟨(sf, bit), Th⟩ = none ∧
        PhaseHomeAt Th 0 ∧ PhaseInputSame initial Th 0 ∧
        PhaseMarkAbs Th 0 lo' hi' ∧ PhaseWorkMarked Th 0 n ∧
        PhaseUnmarkedWork initial Th 0) ∧
      (Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable
        (3 * (max hi' ((n : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5)
        ⟨(.rightErase, bit), Th⟩ =
          some ⟨(.backHomeR, bit), T''⟩ ∧
        Turing.TM0.step sweepResetTable ⟨(.backHomeR, bit), T''⟩ = none ∧
        PhaseHomeAt T'' 0 ∧ PhaseInputSame initial T'' 0 ∧
        ∀ i : ℤ, phaseBusy (T''.nth i) = false) := by
  have hdist : homeDistance sf (if sf then (-off').toNat else off'.toNat) = off' :=
    side_homeDistance sf off' hside
  obtain ⟨Th, hrunH, hhomeH, hhaltH, hdataH⟩ :=
    liftMarkerHome_run sf bit (if sf then (-off').toNat else off'.toNat) Tf
      (by rw [hdist]; exact hhome)
  have hdata' : ∀ i : ℤ, Th.nth i = Tf.nth (i - off') := by
    intro i
    rw [hdataH i, hdist]
  obtain ⟨hmarkH, hinpH, hworkH⟩ :=
    phaseShift_invariants Tf Th off' lo' hi' n initial hdata' hmark hinp hwork
  have hucopyH : PhaseUnmarkedWork initial Th 0 :=
    phaseUnmarkedWork_shift initial Tf Th off' hdata' hucopy
  have hregion : ∀ i : ℤ, phaseBusy (Th.nth i) = true ↔
      lo' ≤ i ∧ i ≤ max hi' ((n : ℤ) - 1) := by
    intro i
    simpa using! phaseBusy_region Th initial 0 lo' hi' n hmarkH hworkH hucopyH href hcover i
  obtain ⟨T'', hrunS, hhaltS, hhomeS, hinpS, hcleanS⟩ :=
    sweepReset_run bit Th initial lo' (max hi' ((n : ℤ) - 1)) hhomeH hinpH hregion
      hcover.1 (by omega)
  exact ⟨Th, T'', ⟨hrunH, hhaltH, hhomeH, hinpH, hmarkH, hworkH, hucopyH⟩,
    hrunS, hhaltS, hhomeS, hinpS, hcleanS⟩

/-- The nonnegative cells of a tape built by `Turing.Tape.mk₁` are given by default-valued list
indexing. -/
theorem phaseTape_mk₁_nth (l : List CellCore) (a : ℕ) :
    (Turing.Tape.mk₁ l).nth (a : ℤ) = l.getI a := by
  rw [← Turing.Tape.right₀_nth (Turing.Tape.mk₁ l) a]
  show (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk l)).right₀.nth a
      = l.getI a
  rw [Turing.Tape.mk'_right₀, Turing.ListBlank.nth_mk]

/-- Every negative cell of a tape built by `Turing.Tape.mk₁` contains the default phase symbol. -/
theorem phaseTape_mk₁_nth_neg (l : List CellCore) (a : ℕ) :
    (Turing.Tape.mk₁ l).nth (-(a : ℤ) - 1) = default := by
  have hi : (-(a : ℤ) - 1) = -((a + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hi]
  show (Turing.ListBlank.mk ([] : List CellCore)).nth a = _
  rw [Turing.ListBlank.nth_mk]
  simp

/-- Indexing the tape with duplicated input and work tracks gives the corresponding encoded
input bit, or the default cell beyond the list. -/
theorem phaseCopyList_nth (input : List Bool) (a : ℕ) :
    (Turing.Tape.mk₁ (input.map fun b => (some b, some b, false, none))).nth (a : ℤ) =
      Option.getD (input[a]?.map fun b => (some b, some b, false, none))
        (default : CellCore) := by
  induction input generalizing a with
  | nil =>
      cases a with
      | zero => rfl
      | succ a' =>
          simp only [List.map_nil]
          rw [phaseTape_mk₁_nth]
          rfl
  | cons b bs ih =>
      cases a with
      | zero => rfl
      | succ a' =>
          simp only [List.map_cons]
          rw [phaseTape_mk₁_nth, List.getI_cons_succ, ← phaseTape_mk₁_nth, ih a']
          simp

/-- The copied tape has a home marker exactly at zero, no visitation marks, and identical input
and work tracks containing the input at nonnegative positions and blanks at negative
positions. -/
theorem phaseCopyResult_nth (input : List Bool) (i : ℤ) :
    ((phaseCopyResult input).nth i).2.2.1 = decide (i = 0) ∧
    ((phaseCopyResult input).nth i).2.2.2 = none ∧
    (0 ≤ i → ((phaseCopyResult input).nth i).1 = input[i.toNat]? ∧
      ((phaseCopyResult input).nth i).2.1 = input[i.toNat]?) ∧
    (i < 0 → ((phaseCopyResult input).nth i).1 = none ∧
      ((phaseCopyResult input).nth i).2.1 = none) := by
  have hdef : phaseCopyResult input =
      (Turing.Tape.mk₁ (input.map fun b => (some b, some b, false, none))).write
        (input[0]?, input[0]?, true, none) := by
    show (markerCopyResult input).map phaseEmbedMap = _
    simp only [markerCopyResult, Turing.Tape.map_write, Turing.Tape.map_mk₁, List.map_map]
    cases input with
    | nil => rfl
    | cons b bs => rfl
  by_cases hi : 0 ≤ i
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = (a : ℤ) := ⟨Int.toNat i, (Int.toNat_of_nonneg hi).symm⟩
    subst ha
    cases a with
    | zero =>
        simp only [Nat.cast_zero]
        rw [hdef, phaseWriteNth_zero]
        refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩
    | succ a' =>
        rw [hdef, phaseWriteNth_of_ne _ _ _ (by omega), phaseCopyList_nth]
        have htoNat : ((a' + 1 : ℕ) : ℤ).toNat = a' + 1 := by omega
        rw [htoNat]
        have hdefcell : (default : CellCore) = (none, none, false, none) := rfl
        have hne : ¬ (((a' : ℤ) + 1) = 0) := by omega
        cases hget : input[a' + 1]? with
        | none =>
            refine ⟨by simp [hdefcell, hne], rfl,
              fun _ => ⟨by simp [hdefcell], by simp [hdefcell]⟩,
              fun h => absurd h (by omega)⟩
        | some b =>
            refine ⟨by simp [hne], rfl, fun _ => ⟨rfl, rfl⟩,
              fun h => absurd h (by omega)⟩
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = -((a : ℤ)) - 1 := by
      have hpos : (0 : ℤ) ≤ -i := by omega
      have h1 := Int.toNat_of_nonneg hpos
      refine ⟨Int.toNat (-i) - 1, ?_⟩
      omega
    subst ha
    have hcell : ((phaseCopyResult input).nth (-(a : ℤ) - 1)) = default := by
      rw [hdef, phaseWriteNth_of_ne _ _ _ (by omega),
        phaseTape_mk₁_nth_neg]
    rw [hcell]
    have hne : ¬ ((-(a : ℤ) - 1) = 0) := by omega
    have hdefcell : (default : CellCore) = (none, none, false, none) := rfl
    refine ⟨by simp [hne, hdefcell], rfl, fun h => absurd h (by omega),
      fun _ => ⟨by rw [hdefcell], by rw [hdefcell]⟩⟩

/-- The copied tape satisfies the home-marker invariant at offset zero. -/
theorem phaseCopyResult_home (input : List Bool) :
    PhaseHomeAt (phaseCopyResult input) 0 := by
  intro i
  rw [show i + (0:ℤ) = i by omega]
  exact (phaseCopyResult_nth input i).1

/-- The copied tape agrees with its own input track at offset zero. -/
theorem phaseCopyResult_input (input : List Bool) :
    PhaseInputSame (phaseCopyResult input) (phaseCopyResult input) 0 := by
  intro i
  rw [show i + (0:ℤ) = i by omega]

/-- The copied tape satisfies the unmarked-work invariant relative to itself at offset zero. -/
theorem phaseCopyResult_ucopy (input : List Bool) :
    PhaseUnmarkedWork (phaseCopyResult input) (phaseCopyResult input) 0 := by
  intro i _
  rw [show i + (0:ℤ) = i by omega]

/-- The copied tape has an empty marked interval, represented by the endpoints `1` and `0`. -/
theorem phaseCopyResult_mark (input : List Bool) :
    PhaseMarkAbs (phaseCopyResult input) 0 1 0 := by
  intro i
  exact ⟨fun h => absurd (phaseCopyResult_nth input i).2.1 h,
    fun h => absurd h (by omega)⟩

/-- The copied tape satisfies the marked-work invariant for the input length. -/
theorem phaseCopyResult_work (input : List Bool) :
    PhaseWorkMarked (phaseCopyResult input) 0 input.length := by
  intro i hw
  have hi0 : 0 ≤ i := by
    by_contra hlt
    exact hw ((phaseCopyResult_nth input i).2.2.2 (by omega)).2
  rw [((phaseCopyResult_nth input i).2.2.1 hi0).2] at hw
  have hlen : i.toNat < input.length := by
    by_contra hcon
    exact hw (List.getElem?_eq_none_iff.mpr (not_lt.mp hcon))
  have htoNat : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
  exact Or.inr ⟨by omega, by omega⟩

/-- Every cell within the copied input interval has a nonblank work symbol. -/
theorem phaseCopyResult_filled (input : List Bool) (a : ℤ) (h1 : 0 ≤ a)
    (h2 : a < (input.length : ℤ)) :
    ((phaseCopyResult input).nth a).2.1 ≠ none := by
  intro hnone
  rw [((phaseCopyResult_nth input a).2.2.1 h1).2] at hnone
  have hlen := List.getElem?_eq_none_iff.mp hnone
  have htoNat : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h1
  omega

/-- A source run that halts after consuming `w` has corresponding copy, marked-run, homing, and
reset phases with the stated costs and interval bounds. The final tape is clean at home,
retains the input track, and carries the source acceptance bit in the reset state. -/
theorem phaseCopyRunReset {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (w fs : List Bool) (q : Λ)
    (final : Turing.TM0.Cfg (Option Bool) Λ)
    (hstop : (coinConfigRunAux M w ⟨q, (phaseCopyResult input).map phaseWorkMap⟩).stopped
      = some final)
    (hread : (coinConfigRunAux M w ⟨q, (phaseCopyResult input).map phaseWorkMap⟩).reads
      = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (Tf Th T'' : Turing.Tape CellCore) (off' lo' hi' : ℤ),
      (Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => markerCopyTable) false)
          (3 * input.length + 3) (Turing.TM0.init (phaseInput input)) =
        some ⟨4, phaseCopyResult input⟩ ∧
        Turing.TM0.step (liftMarkerTable (fun _ => markerCopyTable) false)
          ⟨4, phaseCopyResult input⟩ = none) ∧
      PhaseHomeAt Tf off' ∧ SideAt sf off' ∧
      PhaseInputSame (phaseCopyResult input) Tf off' ∧
      PhaseMarkAbs Tf off' lo' hi' ∧ PhaseWorkMarked Tf off' input.length ∧
      PhaseUnmarkedWork (phaseCopyResult input) Tf off' ∧
      PhaseMarkGrows (phaseCopyResult input) Tf 0 off' ∧
      (Tf.nth (0 - off')).2.2.2 ≠ none ∧
      lo' ≤ 1 ∧ 0 ≤ hi' ∧ hi' ≤ 2 * w.length + 1 ∧ 1 - lo' ≤ 2 * w.length + 1 ∧
      -(w.length : ℤ) ≤ off' ∧ off' ≤ (w.length : ℤ) ∧
      Tf.map phaseWorkMap = final.Tape ∧
      (∀ (x : Bool) (rest : List Bool),
        coinConfigRunAux (markRunTable M) (pairCoins w fs ++ x :: rest)
            ⟨Sum.inl (q, false), phaseCopyResult input⟩ =
          ⟨some ⟨Sum.inr (Sum.inr (final.q, sf)), Tf⟩, 2 * w.length + 1, 2 * w.length + 1⟩ ∧
        (coinTapeRunAux (markRunTable M) (markRunAccept a) (pairCoins w fs ++ x :: rest)
          ⟨Sum.inl (q, false), phaseCopyResult input⟩).1 = some (a final.q)) ∧
      (Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (liftMarkerTable (fun _ => markerHomeTable) false)
          (if sf then (-off').toNat else off'.toNat) ⟨(sf, a final.q), Tf⟩ =
        some ⟨(sf, a final.q), Th⟩ ∧
        Turing.TM0.step (liftMarkerTable (fun _ => markerHomeTable) false)
          ⟨(sf, a final.q), Th⟩ = none ∧
        PhaseHomeAt Th 0 ∧ PhaseInputSame (phaseCopyResult input) Th 0 ∧
        PhaseMarkAbs Th 0 lo' hi' ∧ PhaseWorkMarked Th 0 input.length ∧
        PhaseUnmarkedWork (phaseCopyResult input) Th 0) ∧
      (Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom sweepResetTable
          (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5)
          ⟨(.rightErase, a final.q), Th⟩ =
        some ⟨(.backHomeR, a final.q), T''⟩ ∧
        Turing.TM0.step sweepResetTable ⟨(.backHomeR, a final.q), T''⟩ = none ∧
        PhaseHomeAt T'' 0 ∧ PhaseInputSame (phaseCopyResult input) T'' 0 ∧
        ∀ i : ℤ, phaseBusy (T''.nth i) = false) := by
  obtain ⟨sf, Tf, off', lo', hi', hhome', hside', hinp', hmark', hwork', hucopy', hgrow,
    hstartMark, hlo, hhi, hhiHi, hloLo, hoffLo, hoffHi, hproj, hcoin⟩ :=
    markRun_coin_run M a hc (phaseCopyResult input) input.length w fs q false
      (phaseCopyResult input) 0 1 0 (phaseCopyResult_home input)
      (⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩ : SideAt false 0)
      (phaseCopyResult_input input) (phaseCopyResult_mark input)
      (phaseCopyResult_work input) (phaseCopyResult_ucopy input)
      (by omega : (1:ℤ) - 1 ≤ 0 ∧ 0 ≤ (0:ℤ) + 1) final hstop hread hfs
  obtain ⟨hcover1, hcover2⟩ := (hmark' (0 - off')).mp hstartMark
  have hcover : lo' ≤ 0 ∧ 0 ≤ hi' := by omega
  obtain ⟨Th, T'', ⟨hrunH, hhaltH, hhome0, hinp0, hmark0, hwork0, hucopy0⟩,
    hrunS, hhaltS, hhomeS, hinpS, hcleanS⟩ :=
    phaseHomeSweepReset Tf (phaseCopyResult input) off' lo' hi' sf (a final.q)
      input.length hhome' hside' hinp' hmark' hwork' hucopy' hcover
      (phaseCopyResult_filled input)
  refine ⟨sf, Tf, Th, T'', off', lo', hi', phaseCopy_run input,
    hhome', hside', hinp', hmark', hwork', hucopy', hgrow, hstartMark,
    hlo, hhi, ?_, hloLo, ?_, ?_, hproj, hcoin,
    ⟨hrunH, hhaltH, hhome0, hinp0, hmark0, hwork0, hucopy0⟩,
    ⟨hrunS, hhaltS, hhomeS, hinpS, hcleanS⟩⟩
  · omega
  · omega
  · omega

/-- One Turing-machine step commutes with relabeling control states when the transition tables
agree at the current cell. -/
theorem TM0_step_relabel {Γ : Type*} [Inhabited Γ] {Λ₁ Λ₂ : Type*} [Inhabited Λ₁] [Inhabited Λ₂]
    {M : Bool → Turing.TM0.Machine Γ Λ₁} {M' : Bool → Turing.TM0.Machine Γ Λ₂}
    {f : Λ₁ → Λ₂} (c : Bool) (q : Λ₁) (T : Turing.Tape Γ)
    (h : M' c (f q) T.head = (M c q T.head).map fun p => (f p.1, p.2)) :
    Turing.TM0.step (M' c) ⟨f q, T⟩ =
      (Turing.TM0.step (M c) ⟨q, T⟩).map fun c' => ⟨f c'.q, c'.Tape⟩ := by
  rw [TM0_step_apply, TM0_step_apply, h]
  cases ht : M c q T.head with
  | none => rfl
  | some p => rw [Option.map_some, Option.map_some]; rfl

/-- For a machine with coin-independent halting, a stopped configuration run consuming the
entire coin list yields the same final configuration under `coinStepsAux`. -/
theorem coinStepsAux_of_aux {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ)
    (hcommon : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ (l : List Bool) (cfg final : Turing.TM0.Cfg Γ Λ),
      (coinConfigRunAux M l cfg).stopped = some final →
      (coinConfigRunAux M l cfg).reads = l.length →
      coinStepsAux M l cfg = some final := by
  intro l
  induction l with
  | nil =>
      intro cfg final h1 _
      simp only [coinConfigRunAux] at h1
      split at h1
      · obtain rfl : cfg = final := Option.some.inj h1
        rfl
      · exact absurd h1 (by simp)
  | cons c cs ih =>
      intro cfg final h1 h2
      have hch : coinHalt M cfg = false := by
        cases hh : coinHalt M cfg with
        | false => rfl
        | true =>
            simp [coinConfigRunAux, hh] at h2
      simp only [coinConfigRunAux, hch, Bool.false_eq_true, ↓reduceIte] at h1 h2
      cases hs : Turing.TM0.step (M c) cfg with
      | none =>
          have htab : M c cfg.q cfg.Tape.head = none :=
            (TM0_step_eq_none _ _).mp hs
          have hcoin : coinHalt M cfg = true := by
            cases c with
            | false => simp [coinHalt, htab, (hcommon cfg.q cfg.Tape.head).mp htab]
            | true => simp [coinHalt, htab, (hcommon cfg.q cfg.Tape.head).mpr htab]
          rw [hcoin] at hch
          exact absurd hch (by simp)
      | some next =>
          simp only [hs] at h1 h2
          rw [List.length_cons] at h2
          have hreads : (coinConfigRunAux M cs next).reads = cs.length := by omega
          rw [coinStepsAux, hs, Option.bind_some]
          exact ih next final h1 hreads

/-- For a constant transition table, executing a coin list with `coinStepsAux` equals running
the deterministic machine for the list length. -/
theorem coinStepsAux_const {Γ : Type} {Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (N : Turing.TM0.Machine Γ Λ) :
    ∀ (l : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      coinStepsAux (fun _ => N) l cfg = Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom N l.length cfg := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro cfg
      rw [coinStepsAux, List.length_cons, show cs.length + 1 = 1 + cs.length by omega,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one]
      simp only [ih]

/-- Successful finite coin-step execution is preserved by a control-state relabeling that agrees
on every live source transition. -/
theorem coinStepsAux_sim {Γ : Type*} [Inhabited Γ] {Λ₁ Λ₂ : Type*} [Inhabited Λ₁] [Inhabited Λ₂]
    (M : Bool → Turing.TM0.Machine Γ Λ₁) (M' : Bool → Turing.TM0.Machine Γ Λ₂)
    (f : Λ₁ → Λ₂)
    (hagree : ∀ (c : Bool) (q : Λ₁) (s : Γ), M c q s ≠ none →
      M' c (f q) s = (M c q s).map fun p => (f p.1, p.2)) :
    ∀ (l : List Bool) (cfg final : Turing.TM0.Cfg Γ Λ₁),
      coinStepsAux M l cfg = some final →
      coinStepsAux M' l ⟨f cfg.q, cfg.Tape⟩ = some ⟨f final.q, final.Tape⟩ := by
  intro l
  induction l with
  | nil =>
      intro cfg final h
      simp only [coinStepsAux] at h
      obtain rfl : cfg = final := Option.some.inj h
      rfl
  | cons c cs ih =>
      intro cfg final h
      rw [coinStepsAux, Option.bind_eq_some_iff] at h
      obtain ⟨next, hs, hrest⟩ := h
      have htab : M c cfg.q cfg.Tape.head ≠ none := by
        intro hnone
        have hstepnone : Turing.TM0.step (M c) cfg = none := by
          simp [TM0_step_apply, hnone]
        rw [hstepnone] at hs
        exact absurd hs (by simp)
      rw [coinStepsAux,
        TM0_step_relabel c cfg.q cfg.Tape (hagree c cfg.q cfg.Tape.head htab), hs,
        Option.map_some, Option.bind_some]
      exact ih next final hrest

/-- Interleaving a coin list with at least as many filler coins doubles its length. -/
theorem pairCoins_length (w fs : List Bool) (h : w.length ≤ fs.length) :
    (pairCoins w fs).length = 2 * w.length := by
  induction w generalizing fs with
  | nil => rfl
  | cons c cs ih =>
      cases fs with
      | nil => simp at h
      | cons f fs' =>
          simp only [List.length_cons] at h
          simp only [pairCoins, List.length_cons, ih fs' (by omega)]
          omega

/-- Control states for the copy, marked execution, homing, and reset phases of the compiler. -/
abbrev ControlCore (Λ : Type*) :=
  Sum (Fin 5) (Sum (MarkRunControl Λ) (Sum HomeState SweepState))

instance {Λ : Type} [Inhabited Λ] : Inhabited (ControlCore Λ) :=
  ⟨Sum.inl default⟩

/-- Dispatch transitions among copying, marked source execution, homing, and reset, passing the
source acceptance bit to the final phases. -/
def phaseDispatchTable {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) : Turing.TM0.Machine CellCore (ControlCore Λ) :=
  fun q s =>
    match q with
    | .inl qc =>
        match liftMarkerTable (fun _ => markerCopyTable) c qc s with
        | none => some (.inr (.inl (.inl (q₀, false))), Turing.TM0.Stmt.write s)
        | some (q', stmt) => some (.inl q', stmt)
    | .inr (.inl (.inr (.inr (qf, sf)))) =>
        some (.inr (.inr (.inl (sf, a qf))), Turing.TM0.Stmt.write s)
    | .inr (.inl p) => (markRunTable M c p s).map fun p' => (.inr (.inl p'.1), p'.2)
    | .inr (.inr (.inl hb)) =>
        match liftMarkerTable (fun _ => markerHomeTable) c hb s with
        | none => some (.inr (.inr (.inr (.rightErase, hb.2))), Turing.TM0.Stmt.write s)
        | some (q', stmt) => some (.inr (.inr (.inl q')), stmt)
    | .inr (.inr (.inr ss)) =>
        (sweepResetTable ss s).map fun p' => (.inr (.inr (.inr p'.1)), p'.2)

/-- Extract the stored result bit in reset states and return `false` in all earlier phases. -/
def phaseDispatchAccept {Λ : Type*} : ControlCore Λ → Bool
  | .inr (.inr (.inr ss)) => ss.2
  | _ => false

/-- The lifted copy table is independent of the supplied coin bit. -/
theorem liftMarkerCopy_const (c : Bool) (q : Fin 5) (s : CellCore) :
    liftMarkerTable (fun _ => markerCopyTable) c q s =
      liftMarkerTable (fun _ => markerCopyTable) false q s := rfl

/-- The lifted homing table is independent of the supplied coin bit. -/
theorem liftMarkerHome_const (c : Bool) (q : HomeState) (s : CellCore) :
    liftMarkerTable (fun _ => markerHomeTable) c q s =
      liftMarkerTable (fun _ => markerHomeTable) false q s := rfl

/-- On a live copy state, the dispatch table agrees with the lifted copy table after embedding
its control labels. -/
theorem phaseDispatch_copy_live {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (q : Fin 5) (s : CellCore)
    (h : liftMarkerTable (fun _ => markerCopyTable) c q s ≠ none) :
    phaseDispatchTable M a q₀ c (Sum.inl q) s =
      (liftMarkerTable (fun _ => markerCopyTable) c q s).map
        fun p => (Sum.inl p.1, p.2) := by
  simp only [phaseDispatchTable]
  cases htab : liftMarkerTable (fun _ => markerCopyTable) c q s with
  | none => exact absurd htab h
  | some p => rfl

/-- At the completed copy tape, dispatch leaves copy state `4` and enters live source state `q₀`
without changing the head symbol. -/
theorem phaseDispatch_copy_switch {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (input : List Bool) :
    phaseDispatchTable M a q₀ c (Sum.inl 4) (phaseCopyResult input).head =
      some (Sum.inr (Sum.inl (Sum.inl (q₀, false))),
        Turing.TM0.Stmt.write (phaseCopyResult input).head) := by
  have hnone : liftMarkerTable (fun _ => markerCopyTable) c 4
      (phaseCopyResult input).head = none := by
    rw [liftMarkerCopy_const]
    exact (TM0_step_eq_none _ _).mp (phaseCopy_run input).2
  simp only [phaseDispatchTable, hnone]

/-- On a live marked-run transition, dispatch agrees with the marked-run table after embedding
its control labels. -/
theorem phaseDispatch_mark_live {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (p : MarkRunControl Λ) (s : CellCore)
    (h : markRunTable M c p s ≠ none) :
    phaseDispatchTable M a q₀ c (Sum.inr (Sum.inl p)) s =
      (markRunTable M c p s).map fun p' => (Sum.inr (Sum.inl p'.1), p'.2) := by
  cases p with
  | inl q => simp only [phaseDispatchTable]
  | inr pp =>
      cases pp with
      | inl pp' => simp only [phaseDispatchTable]
      | inr p' => simp [markRunTable] at h

/-- Dispatch moves from a final marked-run state to homing, retaining the side bit and storing
the source acceptance bit without changing the tape. -/
theorem phaseDispatch_mark_switch {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (qf : Λ) (sf : Bool) (T : Turing.Tape CellCore) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c)
        ⟨Sum.inr (Sum.inl (Sum.inr (Sum.inr (qf, sf)))), T⟩ =
      some ⟨Sum.inr (Sum.inr (Sum.inl (sf, a qf))), T⟩ := by
  simp [TM0_step_apply, phaseDispatchTable, TM0StmtApply, Turing.Tape.write_self]

/-- On a live homing transition, dispatch agrees with the lifted homing table after embedding
its control labels. -/
theorem phaseDispatch_home_live {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (hb : HomeState) (s : CellCore)
    (h : liftMarkerTable (fun _ => markerHomeTable) c hb s ≠ none) :
    phaseDispatchTable M a q₀ c (Sum.inr (Sum.inr (Sum.inl hb))) s =
      (liftMarkerTable (fun _ => markerHomeTable) c hb s).map
        fun p => (Sum.inr (Sum.inr (Sum.inl p.1)), p.2) := by
  simp only [phaseDispatchTable]
  cases htab : liftMarkerTable (fun _ => markerHomeTable) c hb s with
  | none => exact absurd htab h
  | some p => rfl

/-- At the home marker, dispatch switches from homing to rightward reset erasure without
changing the tape or stored bit. -/
theorem phaseDispatch_home_switch {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (side bit : Bool) (T : Turing.Tape CellCore)
    (h : T.head.2.2.1 = true) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c)
        ⟨Sum.inr (Sum.inr (Sum.inl (side, bit))), T⟩ =
      some ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.rightErase, bit))), T⟩ := by
  have hnone : liftMarkerTable (fun _ => markerHomeTable) c (side, bit) T.head = none := by
    rw [liftMarkerHome_const]
    exact (TM0_step_eq_none _ _).mp (liftMarkerHome_step_home (side, bit) T h)
  simp [TM0_step_apply, phaseDispatchTable, hnone, TM0StmtApply, Turing.Tape.write_self]

/-- In reset states, dispatch agrees with the sweep-reset table after embedding its control
labels. -/
theorem phaseDispatch_reset {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (ss : SweepState) (s : CellCore) :
    phaseDispatchTable M a q₀ c (Sum.inr (Sum.inr (Sum.inr ss))) s =
      (sweepResetTable ss s).map
        fun p' => (Sum.inr (Sum.inr (Sum.inr p'.1)), p'.2) := by
  simp only [phaseDispatchTable]

/-- Halting of the phase-dispatch machine is independent of the supplied coin bit. -/
theorem phaseDispatch_commonHalt {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ) :
    ∀ (q : ControlCore Λ) (s : CellCore),
      (phaseDispatchTable M a q₀ false q s = none) ↔
        (phaseDispatchTable M a q₀ true q s = none) := by
  intro q s
  cases q with
  | inl qc =>
      simp only [phaseDispatchTable, liftMarkerCopy_const]
  | inr q2 =>
      cases q2 with
      | inl p =>
          cases p with
          | inl p' =>
              simp only [phaseDispatchTable, Option.map_eq_none_iff]
              exact markRun_commonHalt M (Sum.inl p') s
          | inr pp =>
              cases pp with
              | inl pp' =>
                  simp only [phaseDispatchTable, Option.map_eq_none_iff]
                  exact markRun_commonHalt M (Sum.inr (Sum.inl pp')) s
              | inr p'' =>
                  simp only [phaseDispatchTable]
      | inr q3 =>
          cases q3 with
          | inl hb =>
              simp only [phaseDispatchTable, liftMarkerHome_const]
          | inr ss =>
              simp only [phaseDispatchTable, Option.map_eq_none_iff]

/-- Dispatch executes a complete copy–run–home–reset sequence for a fully consumed, halting
source coin word. It returns the source acceptance bit with the stated equal read and
transition counts, final cleanliness, and intermediate workspace bounds. -/
theorem phaseDispatchRunReset {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (q₀ : Λ) (input : List Bool) (w fs : List Bool)
    (final : Turing.TM0.Cfg (Option Bool) Λ)
    (hstop : (coinConfigRunAux M w ⟨q₀, (phaseCopyResult input).map phaseWorkMap⟩).stopped
      = some final)
    (hread : (coinConfigRunAux M w ⟨q₀, (phaseCopyResult input).map phaseWorkMap⟩).reads
      = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (Tf T'' : Turing.Tape CellCore) (off' lo' hi' : ℤ),
      (PhaseHomeAt T'' 0 ∧ PhaseInputSame (phaseCopyResult input) T'' 0 ∧
        (∀ i : ℤ, phaseBusy (T''.nth i) = false) ∧
        Tf.map phaseWorkMap = final.Tape ∧
        PhaseMarkAbs Tf off' lo' hi' ∧
        -(w.length : ℤ) ≤ off' ∧ off' ≤ (w.length : ℤ) ∧
        lo' ≤ 1 ∧ 0 ≤ hi' ∧ hi' ≤ 2 * w.length + 1 ∧ 1 - lo' ≤ 2 * w.length + 1) ∧
      ∀ (jcopy jhome jreset tail : List Bool) (c₁ c₂ c₃ x : Bool),
        jcopy.length = 3 * input.length + 3 →
        jhome.length = (if sf then (-off').toNat else off'.toNat) →
        jreset.length = 3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5 →
        (coinConfigRunAux (phaseDispatchTable M a q₀)
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩) =
          ⟨some ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩,
            (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1 +
              (if sf then (-off').toNat else off'.toNat) + 1 +
              (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5),
            (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1 +
              (if sf then (-off').toNat else off'.toNat) + 1 +
              (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5)⟩ ∧
        (coinTapeRunAux (phaseDispatchTable M a q₀) phaseDispatchAccept
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩) =
          (some (a final.q),
            (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1 +
              (if sf then (-off').toNat else off'.toNat) + 1 +
              (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5)) ∧
        coinStepsAux (phaseDispatchTable M a q₀)
            (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
            ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ =
          some ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩ ∧
        coinHalt (phaseDispatchTable M a q₀)
            ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩ = true := by
  obtain ⟨sf, Tf, Th, T'', off', lo', hi', copySeg, hhome', hside', hinp', hmark', hwork',
    hucopy', hgrow, hstartMark, hlo, hhi, hhiHi, hloLo, hoffLo, hoffHi, hproj, hcoin,
    ⟨hrunH, hhaltH, hhome0, hinp0, hmark0, hwork0, hucopy0⟩,
    ⟨hrunS, hhaltS, hhomeS, hinpS, hcleanS⟩⟩ :=
    phaseCopyRunReset M a hc input w fs q₀ final hstop hread hfs
  refine ⟨sf, Tf, T'', off', lo', hi',
    ⟨hhomeS, hinpS, hcleanS, hproj, hmark', hoffLo, hoffHi, hlo, hhi, hhiHi, hloLo⟩, ?_⟩
  intro jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset

  have hcopyAgree : ∀ (c : Bool) (q : Fin 5) (s : CellCore),
      liftMarkerTable (fun _ => markerCopyTable) false q s ≠ none →
        phaseDispatchTable M a q₀ c (Sum.inl q) s =
          (liftMarkerTable (fun _ => markerCopyTable) false q s).map
            fun p => (Sum.inl p.1, p.2) := by
    intro c q s h
    rw [phaseDispatch_copy_live M a q₀ c q s (by rw [liftMarkerCopy_const]; exact h),
      liftMarkerCopy_const]
  have t1 : coinStepsAux (phaseDispatchTable M a q₀) jcopy
      ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ =
      some ⟨Sum.inl (4 : Fin 5), phaseCopyResult input⟩ :=
    coinStepsAux_sim (fun _ => liftMarkerTable (fun _ => markerCopyTable) false)
      (phaseDispatchTable M a q₀) Sum.inl hcopyAgree jcopy
      (Turing.TM0.init (phaseInput input)) ⟨(4 : Fin 5), phaseCopyResult input⟩
      (by rw [coinStepsAux_const, hjcopy]; exact copySeg.1)
  have hstep2 : Turing.TM0.step (phaseDispatchTable M a q₀ c₁)
      ⟨Sum.inl (4 : Fin 5), phaseCopyResult input⟩ =
      some ⟨Sum.inr (Sum.inl (Sum.inl (q₀, false))), phaseCopyResult input⟩ := by
    rw [TM0_step_apply, phaseDispatch_copy_switch]
    simp [TM0StmtApply, Turing.Tape.write_self]
  have hmarkAux1 := (hcoin x []).1
  have hmarkTrace : coinStepsAux (markRunTable M) (pairCoins w fs ++ [x])
      ⟨Sum.inl (q₀, false), phaseCopyResult input⟩ =
      some ⟨Sum.inr (Sum.inr (final.q, sf)), Tf⟩ := by
    refine coinStepsAux_of_aux (markRunTable M) (markRun_commonHalt M) _ _ _ ?_ ?_
    · rw [hmarkAux1]
    · rw [hmarkAux1]
      simp [pairCoins_length w fs hfs]
  have t3 : coinStepsAux (phaseDispatchTable M a q₀) (pairCoins w fs ++ [x])
      ⟨Sum.inr (Sum.inl (Sum.inl (q₀, false))), phaseCopyResult input⟩ =
      some ⟨Sum.inr (Sum.inl (Sum.inr (Sum.inr (final.q, sf)))), Tf⟩ :=
    coinStepsAux_sim (markRunTable M) (phaseDispatchTable M a q₀)
      (fun p => Sum.inr (Sum.inl p)) (phaseDispatch_mark_live M a q₀)
      (pairCoins w fs ++ [x]) ⟨Sum.inl (q₀, false), phaseCopyResult input⟩
      ⟨Sum.inr (Sum.inr (final.q, sf)), Tf⟩ hmarkTrace
  have hstep4 := phaseDispatch_mark_switch M a q₀ c₂ final.q sf Tf
  have hhomeAgree : ∀ (c : Bool) (hb : HomeState) (s : CellCore),
      liftMarkerTable (fun _ => markerHomeTable) false hb s ≠ none →
        phaseDispatchTable M a q₀ c (Sum.inr (Sum.inr (Sum.inl hb))) s =
          (liftMarkerTable (fun _ => markerHomeTable) false hb s).map
            fun p => (Sum.inr (Sum.inr (Sum.inl p.1)), p.2) := by
    intro c hb s h
    rw [phaseDispatch_home_live M a q₀ c hb s (by rw [liftMarkerHome_const]; exact h),
      liftMarkerHome_const]
  have t5 : coinStepsAux (phaseDispatchTable M a q₀) jhome
      ⟨Sum.inr (Sum.inr (Sum.inl (sf, a final.q))), Tf⟩ =
      some ⟨Sum.inr (Sum.inr (Sum.inl (sf, a final.q))), Th⟩ :=
    coinStepsAux_sim (fun _ => liftMarkerTable (fun _ => markerHomeTable) false)
      (phaseDispatchTable M a q₀) (fun hb => Sum.inr (Sum.inr (Sum.inl hb))) hhomeAgree
      jhome ⟨(sf, a final.q), Tf⟩ ⟨(sf, a final.q), Th⟩
      (by rw [coinStepsAux_const, hjhome]; exact hrunH)
  have hhead : Th.head.2.2.1 = true := by
    simpa using! phaseHomeAt_head Th 0 hhome0
  have hstep6 := phaseDispatch_home_switch M a q₀ c₃ sf (a final.q) Th hhead
  have hresetAgree : ∀ (c : Bool) (ss : SweepState) (s : CellCore),
      sweepResetTable ss s ≠ none →
        phaseDispatchTable M a q₀ c (Sum.inr (Sum.inr (Sum.inr ss))) s =
          (sweepResetTable ss s).map
            fun p' => (Sum.inr (Sum.inr (Sum.inr p'.1)), p'.2) :=
    fun _ _ _ _ => phaseDispatch_reset M a q₀ _ _ _
  have t7 : coinStepsAux (phaseDispatchTable M a q₀) jreset
      ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.rightErase, a final.q))), Th⟩ =
      some ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩ :=
    coinStepsAux_sim (fun _ => sweepResetTable) (phaseDispatchTable M a q₀)
      (fun ss => Sum.inr (Sum.inr (Sum.inr ss))) hresetAgree jreset
      ⟨(SweepPhase.rightErase, a final.q), Th⟩
      ⟨(SweepPhase.backHomeR, a final.q), T''⟩
      (by rw [coinStepsAux_const, hjreset]; exact hrunS)

  have hchain : coinStepsAux (phaseDispatchTable M a q₀)
      (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
      ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ =
      some ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩ := by
    rw [coinStepsAux_append, t1, Option.bind_some]
    rw [coinStepsAux, hstep2, Option.bind_some]
    rw [coinStepsAux_append, t3, Option.bind_some]
    rw [coinStepsAux, hstep4, Option.bind_some]
    rw [coinStepsAux_append, t5, Option.bind_some]
    rw [coinStepsAux, hstep6, Option.bind_some]
    exact t7

  have hnone : sweepResetTable (SweepPhase.backHomeR, a final.q) T''.head = none :=
    (TM0_step_eq_none _ _).mp hhaltS
  have hcoinHalt : coinHalt (phaseDispatchTable M a q₀)
      ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩ = true := by
    simp [coinHalt, phaseDispatchTable, hnone]
  obtain ⟨s1, s2, s3⟩ := coinStepsAux_stopped (phaseDispatchTable M a q₀)
    (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
    ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩
    ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩ hchain hcoinHalt
  have hlen : (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))).length
      = (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1 +
          (if sf then (-off').toNat else off'.toNat) + 1 +
          (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5) := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      pairCoins_length w fs hfs, hjcopy, hjhome, hjreset]
    omega
  have hne : (coinConfigRunAux (phaseDispatchTable M a q₀)
      (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
      ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩).stopped ≠ none := by
    rw [s1]; simp
  have haux : coinConfigRunAux (phaseDispatchTable M a q₀)
      ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))) ++ tail)
      ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ =
      ⟨some ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, a final.q))), T''⟩,
        (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1 +
          (if sf then (-off').toNat else off'.toNat) + 1 +
          (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5),
        (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1 +
          (if sf then (-off').toNat else off'.toNat) + 1 +
          (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5)⟩ := by
    rw [coinConfigRunAux_append _ _ _ _ hne]
    show (⟨(coinConfigRunAux (phaseDispatchTable M a q₀)
          (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
          ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩).stopped,
        (coinConfigRunAux (phaseDispatchTable M a q₀)
          (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
          ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩).reads,
        (coinConfigRunAux (phaseDispatchTable M a q₀)
          (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
          ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩).transitions⟩ :
        CoinRunResult CellCore (ControlCore Λ)) = _
    rw [s1, s2, s3, hlen]
  refine ⟨haux, ?_, hchain, hcoinHalt⟩
  rw [← (coinConfigRunAux_readout (phaseDispatchTable M a q₀) phaseDispatchAccept _ _).1,
    haux]
  simp [phaseDispatchAccept]

/-- A natural-number list encoding the finite control and transition data of a phase machine. -/
abbrev CodeCore := List ℕ

/-- Read the encoded control bound from the first entry, defaulting to zero for an empty code. -/
def phase1ControlSize (p : CodeCore) : ℕ := p.getD 0 0

/-- Encode the input, work, home, and visitation tracks of a phase cell by a mixed-radix natural
number. -/
def phase1CellIndex (s : CellCore) : ℕ :=
  18 * symbolIndex s.1 + 6 * symbolIndex s.2.1 + 3 * s.2.2.1.toNat + symbolIndex s.2.2.2

/-- Extract the input-track digit of an encoded phase cell by division by `18`. -/
def phase1InDigit (n : ℕ) : ℕ := n / 18
/-- Extract the ternary work-track digit of an encoded phase cell. -/
def phase1WorkDigit (n : ℕ) : ℕ := n / 6 % 3
/-- Extract the binary home-marker digit of an encoded phase cell. -/
def phase1HomeDigit (n : ℕ) : ℕ := n / 3 % 2
/-- Extract the ternary visitation-track digit of an encoded phase cell. -/
def phase1MarkDigit (n : ℕ) : ℕ := n % 3

/-- Decode the four mixed-radix digits of a natural number into a phase cell. -/
def phase1DecodeCell (n : ℕ) : CellCore :=
  (decodeSymbol (phase1InDigit n), decodeSymbol (phase1WorkDigit n),
    1 ≤ phase1HomeDigit n, decodeSymbol (phase1MarkDigit n))

/-- Every encoded phase cell has index less than `54`. -/
theorem phase1CellIndex_lt (s : CellCore) : phase1CellIndex s < 54 := by
  obtain ⟨a, b, hb, m⟩ := s
  have h1 := symbolIndex_lt a
  have h2 := symbolIndex_lt b
  have h3 := symbolIndex_lt m
  cases hb <;> simp only [phase1CellIndex, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- The digit projections of an encoded phase cell recover the indices of its four tracks. -/
theorem phase1Digits (s : CellCore) :
    phase1InDigit (phase1CellIndex s) = symbolIndex s.1 ∧
      phase1WorkDigit (phase1CellIndex s) = symbolIndex s.2.1 ∧
      phase1HomeDigit (phase1CellIndex s) = s.2.2.1.toNat ∧
      phase1MarkDigit (phase1CellIndex s) = symbolIndex s.2.2.2 := by
  obtain ⟨a, b, hb, m⟩ := s
  have h1 := symbolIndex_lt a
  have h2 := symbolIndex_lt b
  have h3 := symbolIndex_lt m
  cases hb <;>
    simp only [phase1InDigit, phase1WorkDigit, phase1HomeDigit, phase1MarkDigit, phase1CellIndex,
      Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Decoding the index of a phase cell recovers the original cell. -/
theorem phase1DecodeCell_index (s : CellCore) :
    phase1DecodeCell (phase1CellIndex s) = s := by
  obtain ⟨a, b, hb, m⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := phase1Digits (a, b, hb, m)
  simp only [phase1DecodeCell, h1, h2, h4]
  cases hb <;> simp [h3, decodeSymbol_symbolIndex, Bool.toNat_false, Bool.toNat_true]

/-- Encode a phase-tape action by `0` for moving left, `1` for moving right, and `2` plus the
cell index for writing. -/
def phase1ActionIndex : Turing.TM0.Stmt CellCore → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write s => 2 + phase1CellIndex s

/-- Decode an action residue modulo `56` into a movement or phase-cell write. -/
def phase1DecodeAction (n : ℕ) : Turing.TM0.Stmt CellCore :=
  if n % 56 = 0 then .move .left else
    if n % 56 = 1 then .move .right else .write (phase1DecodeCell (n % 56 - 2))

/-- Every encoded phase-tape action has index less than `56`. -/
theorem phase1ActionIndex_lt (stmt : Turing.TM0.Stmt CellCore) :
    phase1ActionIndex stmt < 56 := by
  cases stmt with
  | move d => cases d <;> simp only [phase1ActionIndex] <;> omega
  | write s =>
      simp only [phase1ActionIndex]
      have := phase1CellIndex_lt s
      omega

/-- Decoding an encoded phase-tape action recovers that action. -/
theorem phase1DecodeAction_index (stmt : Turing.TM0.Stmt CellCore) :
    phase1DecodeAction (phase1ActionIndex stmt) = stmt := by
  cases stmt with
  | move d =>
      cases d <;> simp [phase1DecodeAction, phase1ActionIndex]
  | write s =>
      have h1 : (2 + phase1CellIndex s) % 56 = 2 + phase1CellIndex s := by
        have h2 := phase1CellIndex_lt s
        omega
      have h2 : ¬ (2 + phase1CellIndex s = 0) := by omega
      have h3 : ¬ (2 + phase1CellIndex s = 1) := by omega
      rw [phase1DecodeAction, phase1ActionIndex, h1, ite_eq_right h2, ite_eq_right h3,
        Nat.add_sub_cancel_left, phase1DecodeCell_index]

/-- Encode an optional transition using zero for halting and a base-`56` control-and-action code
for a live transition. -/
def phase1EncodeTransition (K : ℕ) :
    Option (Fin (K + 1) × Turing.TM0.Stmt CellCore) → ℕ
  | none => 0
  | some (q, stmt) => 56 * q.val + phase1ActionIndex stmt + 1

/-- Decode a natural-number transition code into an optional bounded control label and
phase-tape action. -/
def phase1DecodeTransition (K n : ℕ) :
    Option (Fin (K + 1) × Turing.TM0.Stmt CellCore) :=
  match n with
  | 0 => none
  | n + 1 => some (⟨n / 56 % (K + 1), Nat.mod_lt _ (by omega)⟩, phase1DecodeAction n)

/-- Adding a multiple of `56` to an encoded action does not change its decoded action. -/
theorem phase1DecodeAction_mul56 (k : ℕ) (stmt : Turing.TM0.Stmt CellCore) :
    phase1DecodeAction (56 * k + phase1ActionIndex stmt) = stmt := by
  cases stmt with
  | move d =>
      cases d with
      | left =>
          simp only [phase1ActionIndex, Nat.add_zero, Nat.mul_mod_right, phase1DecodeAction,
            ite_true]
      | right =>
          have h1 : (56 * k + 1) % 56 = 1 := by omega
          simp only [phase1ActionIndex, phase1DecodeAction, h1]
          simp
  | write s =>
      have hlt := phase1CellIndex_lt s
      have h1 : (56 * k + (2 + phase1CellIndex s)) % 56 = 2 + phase1CellIndex s := by omega
      have h2 : ¬ (2 + phase1CellIndex s = 0) := by omega
      have h3 : ¬ (2 + phase1CellIndex s = 1) := by omega
      rw [phase1ActionIndex, phase1DecodeAction, h1, ite_eq_right h2, ite_eq_right h3,
        Nat.add_sub_cancel_left, phase1DecodeCell_index]

/-- Decoding an encoded optional phase transition recovers the original transition. -/
theorem phase1DecodeTransition_encode {K : ℕ}
    (p : Option (Fin (K + 1) × Turing.TM0.Stmt CellCore)) :
    phase1DecodeTransition K (phase1EncodeTransition K p) = p := by
  cases p with
  | none => rfl
  | some ps =>
      obtain ⟨q, stmt⟩ := ps
      have hq : q.val < K + 1 := q.isLt
      rw [phase1EncodeTransition,
        show 56 * q.val + phase1ActionIndex stmt + 1
            = (56 * q.val + phase1ActionIndex stmt) + 1 from by omega,
        phase1DecodeTransition]
      have hact : phase1ActionIndex stmt < 56 := phase1ActionIndex_lt stmt
      have h1 : (56 * q.val + phase1ActionIndex stmt) / 56 = q.val := by omega
      simp only [h1, phase1DecodeAction_mul56, Nat.mod_eq_of_lt hq]

/-- Flatten a coin bit, control label, and phase-cell index into a transition-row index. -/
def phase1RowIndex (K : ℕ) (c : Bool) (l sIdx : ℕ) : ℕ :=
  (c.toNat * (K + 1) + l) * 54 + sIdx

/-- A row indexed by a valid control label and phase-cell index is less than `108 * (K + 1)`. -/
theorem phase1RowIndex_lt {K : ℕ} (c : Bool) (l : ℕ) (hl : l < K + 1) (sIdx : ℕ)
    (hs : sIdx < 54) : phase1RowIndex K c l sIdx < 108 * (K + 1) := by
  cases c <;>
    simp only [phase1RowIndex, Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Adding a multiple of a natural-number modulus leaves the remainder unchanged. -/
theorem add_mul_mod_self' (m b c : ℕ) : (m * b + c) % b = c % b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]

/-- Arithmetic projections of a flattened row index recover its control label, coin bit, and
phase-cell index. -/
theorem phase1RowIndex_coordinates {K : ℕ} (c : Bool) (l : Fin (K + 1)) (s : CellCore) :
    phase1RowIndex K c l.val (phase1CellIndex s) / 54 % (K + 1) = l.val ∧
      decide (K + 1 ≤ phase1RowIndex K c l.val (phase1CellIndex s) / 54) = c ∧
      phase1RowIndex K c l.val (phase1CellIndex s) % 54 = phase1CellIndex s := by
  have hs := phase1CellIndex_lt s
  have hl : l.val < K + 1 := l.isLt
  have hdiv : phase1RowIndex K c l.val (phase1CellIndex s) / 54 = c.toNat * (K + 1) + l.val := by
    cases c <;>
      simp only [phase1RowIndex, Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.zero_add,
        Nat.one_mul] <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiv, add_mul_mod_self', Nat.mod_eq_of_lt hl]
  · cases c with
    | false =>
        have h1 : (l.val * 54 + phase1CellIndex s) / 54 = l.val := by omega
        simp only [phase1RowIndex, Bool.toNat_false, Nat.zero_mul, Nat.zero_add, h1]
        exact decide_eq_false_iff_not.mpr (by omega)
    | true =>
        have h1 : ((1 * (K + 1) + l.val) * 54 + phase1CellIndex s) / 54 = 1 * (K + 1) + l.val := by
          omega
        simp only [phase1RowIndex, Bool.toNat_true, h1]
        exact decide_eq_true (by omega)
  · cases c <;>
      simp only [phase1RowIndex, Bool.toNat_false, Bool.toNat_true, Nat.zero_mul, Nat.zero_add,
        Nat.one_mul] <;> omega

/-- Assign indices `0` through `5` to the six sweep phases. -/
def sweepIdx : SweepPhase → ℕ
  | .rightErase => 0 | .backHomeL => 1 | .leftErase => 2
  | .backHomeR => 3 | .stepRight => 4 | .stepLeft => 5

/-- The compiled control bound `10 * Q + 30` for a source control bound `Q`. -/
def phase1Bound (Q : ℕ) : ℕ := 10 * Q + 30

/-- The base label `5` of live marked-run states. -/
def phase1LiveBase (_Q : ℕ) : ℕ := 5

/-- The base label of pending marked-run states after the live-state block. -/
def phase1PendingBase (Q : ℕ) : ℕ := 5 + 2 * (Q + 1)

/-- The base label of final marked-run states after the pending-state block. -/
def phase1MarkHaltBase (Q : ℕ) : ℕ := 5 + 8 * (Q + 1)

/-- The base label of homing states after the marked-run state blocks. -/
def phase1HomeBase (Q : ℕ) : ℕ := 5 + 10 * (Q + 1)

/-- The base label of sweep-reset states after the four homing states. -/
def phase1ResetBase (Q : ℕ) : ℕ := 5 + 10 * (Q + 1) + 4

/-- Encode structured phase-control states as natural-number labels in consecutive
phase-specific blocks. -/
def phase1ControlLabel (Q : ℕ) : ControlCore (Fin (Q + 1)) → ℕ
  | .inl q => q.val
  | .inr (.inl (.inl (q, b))) => phase1LiveBase Q + 2 * q.val + b.toNat
  | .inr (.inl (.inr (.inl ((q, b), none)))) =>
      phase1PendingBase Q + 3 * (2 * q.val + b.toNat)
  | .inr (.inl (.inr (.inl ((q, b), some .left)))) =>
      phase1PendingBase Q + 3 * (2 * q.val + b.toNat) + 1
  | .inr (.inl (.inr (.inl ((q, b), some .right)))) =>
      phase1PendingBase Q + 3 * (2 * q.val + b.toNat) + 2
  | .inr (.inl (.inr (.inr (q, b)))) => phase1MarkHaltBase Q + 2 * q.val + b.toNat
  | .inr (.inr (.inl (left, bit))) => phase1HomeBase Q + 2 * left.toNat + bit.toNat
  | .inr (.inr (.inr (p, b))) => phase1ResetBase Q + 2 * sweepIdx p + b.toNat

/-- Every encoded phase-control label lies below `phase1Bound Q + 1`. -/
theorem phase1ControlLabel_lt (Q : ℕ) (p : ControlCore (Fin (Q + 1))) :
    phase1ControlLabel Q p < phase1Bound Q + 1 := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by intro b; cases b <;> simp
  have hunf : ∀ p : ControlCore (Fin (Q + 1)),
      phase1ControlLabel Q p < phase1Bound Q + 1 →
        phase1ControlLabel Q p < phase1Bound Q + 1 := fun _ h => h
  rcases p with q | p | p | p
  · have := q.isLt
    simp only [phase1ControlLabel, phase1Bound]
    omega
  · rcases p with p | p
    · have := p.1.isLt; have := hb p.2
      simp only [phase1ControlLabel, phase1Bound, phase1LiveBase]
      omega
    · rcases p with p | p
      · rcases p with ⟨⟨q, b⟩, d⟩
        have := q.isLt; have := hb b
        cases d with
        | none => simp only [phase1ControlLabel, phase1Bound, phase1PendingBase]; omega
        | some d' =>
            cases d' with
            | left => simp only [phase1ControlLabel, phase1Bound, phase1PendingBase]; omega
            | right => simp only [phase1ControlLabel, phase1Bound, phase1PendingBase]; omega
      · have := p.1.isLt; have := hb p.2
        simp only [phase1ControlLabel, phase1Bound, phase1MarkHaltBase]
        omega
  · rcases p with ⟨left, bit⟩
    have := hb left; have := hb bit
    simp only [phase1ControlLabel, phase1Bound, phase1HomeBase]
    omega
  · rcases p with ⟨sp, b⟩
    have := hb b
    have hs : sweepIdx sp ≤ 5 := by cases sp <;> simp [sweepIdx]
    simp only [phase1ControlLabel, phase1Bound, phase1ResetBase]
    omega

/-- Package an encoded phase-control label as a finite index bounded by the compiled control
size. -/
def phase1ControlFin (Q : ℕ) (p : ControlCore (Fin (Q + 1))) :
    Fin (phase1Bound Q + 1) := ⟨phase1ControlLabel Q p, phase1ControlLabel_lt Q p⟩

/-- The initial copy state is encoded by control label zero. -/
theorem phase1ControlLabel_inl_zero (Q : ℕ) :
    phase1ControlLabel Q (Sum.inl (default : Fin 5)) = 0 := rfl

/-- Look up a source transition's natural-number code using its coin, control, and symbol
coordinates, defaulting to zero. -/
def phase1SourceNat (code : Code) (c q aIdx : ℕ) : ℕ :=
  code.getD (1 + (controlSize code + 1) + (c * (controlSize code + 1) + q) * 3 + aIdx) 0

/-- A decoded source-table lookup equals decoding the corresponding natural-number transition
entry. -/
theorem table_eq_sourceNat (code : Code) (c : Bool) (q : ℕ) (hq : q < controlSize code + 1)
    (a : Option Bool) :
    table code c ⟨q, hq⟩ a
      = decodeTransition (controlSize code) (phase1SourceNat code c.toNat q (symbolIndex a)) := by
  have hidx : 1 + (controlSize code + 1)
      + ((c.toNat * (controlSize code + 1) + q) * 3 + symbolIndex a)
      = 1 + (controlSize code + 1)
        + (c.toNat * (controlSize code + 1) + q) * 3 + symbolIndex a := by omega
  simp only [table, rowIndex, phase1SourceNat, hidx]

/-- Compute the encoded copy-phase transition from a numeric control label and phase-cell index. -/
def phase1CopyRowNat (l sIdx : ℕ) : ℕ :=
  if l = 0 then 56 * 1 + (2 + 18 * (sIdx / 18) + 6 * (sIdx / 6 % 3) + 3 + sIdx % 3) + 1
  else if l = 1 then
    if sIdx / 18 = 0 then 56 * 3 + (2 + sIdx) + 1
    else 56 * 2 + (2 + 18 * (sIdx / 18) + 6 * (sIdx / 18) + 3 * (sIdx / 3 % 2) + sIdx % 3) + 1
  else if l = 2 then 56 * 1 + 1 + 1
  else if l = 3 then
    if sIdx / 3 % 2 = 1 then 56 * 4 + (2 + sIdx) + 1 else 56 * 3 + 0 + 1
  else 56 * 5 + (2 + sIdx) + 1

/-- Compute the encoded live marked-run transition using the source code and numeric coin,
label, and cell coordinates. -/
def phase1MarkLiveRowNat (code : Code) (c l sIdx : ℕ) : ℕ :=
  let Q := controlSize code
  let q := (l - 5) / 2
  let bD := (l - 5) % 2
  let h := phase1SourceNat code c q (sIdx / 6 % 3)
  if h = 0 then
    56 * (5 + 8 * (Q + 1) + 2 * q + bD)
      + (2 + 18 * (sIdx / 18) + 6 * (sIdx / 6 % 3) + 3 * (sIdx / 3 % 2) + 2) + 1
  else
    let q' := (h - 1) / 5 % (Q + 1)
    let act := (h - 1) % 5
    if act ≤ 1 then
      if act = 0 then
        56 * (5 + 2 * (Q + 1) + 3 * (2 * q' + (if sIdx / 3 % 2 = 1 then 1 else bD)) + 1)
          + (2 + 18 * (sIdx / 18) + 6 * (sIdx / 6 % 3) + 3 * (sIdx / 3 % 2) + 2) + 1
      else
        56 * (5 + 2 * (Q + 1) + 3 * (2 * q' + (if sIdx / 3 % 2 = 1 then 0 else bD)) + 2)
          + (2 + 18 * (sIdx / 18) + 6 * (sIdx / 6 % 3) + 3 * (sIdx / 3 % 2) + 2) + 1
    else
      56 * (5 + 2 * (Q + 1) + 3 * (2 * q' + bD))
        + (2 + 18 * (sIdx / 18) + 6 * (act - 2) + 3 * (sIdx / 3 % 2) + 2) + 1

/-- Compute the encoded pending-state transition, completing its stored write or movement. -/
def phase1PendingRowNat (Q : ℕ) (l sIdx : ℕ) : ℕ :=
  let q := (l - (5 + 2 * (Q + 1))) / 6
  let bD := (l - (5 + 2 * (Q + 1))) / 3 % 2
  let dIdx := (l - (5 + 2 * (Q + 1))) % 3
  if dIdx = 0 then 56 * (5 + 2 * q + bD) + (2 + sIdx) + 1
  else if dIdx = 1 then 56 * (5 + 2 * q + bD) + 0 + 1
  else 56 * (5 + 2 * q + bD) + 1 + 1

/-- Compute the encoded transition from a final marked-run state to homing with the source
result bit latched. -/
def phase1MarkHaltRowNat (code : Code) (l sIdx : ℕ) : ℕ :=
  let Q := controlSize code
  let q := (l - (5 + 8 * (Q + 1))) / 2
  let sfD := (l - (5 + 8 * (Q + 1))) % 2
  let latch := if code.getD (1 + q) 0 % 2 = 1 then 1 else 0
  56 * (5 + 10 * (Q + 1) + 2 * sfD + latch) + (2 + sIdx) + 1

/-- Compute the encoded homing transition, moving toward home or switching to reset at the home
marker. -/
def phase1HomeRowNat (Q : ℕ) (l sIdx : ℕ) : ℕ :=
  let left := (l - (5 + 10 * (Q + 1))) / 2
  let bit := (l - (5 + 10 * (Q + 1))) % 2
  if sIdx / 3 % 2 = 1 then 56 * (5 + 10 * (Q + 1) + 4 + bit) + (2 + sIdx) + 1
  else if left = 1 then 56 * l + 1 + 1
  else 56 * l + 0 + 1

/-- Compute the encoded sweep-reset transition from the sweep phase and cell digits. -/
def phase1ResetRowNat (Q : ℕ) (l sIdx : ℕ) : ℕ :=
  let p := (l - (5 + 10 * (Q + 1) + 4)) / 2
  let bD := (l - (5 + 10 * (Q + 1) + 4)) % 2
  let busy := sIdx / 6 % 3 ≠ 0 || sIdx % 3 ≠ 0
  let erase := 2 + 18 * (sIdx / 18) + 3 * (sIdx / 3 % 2)
  if p = 0 then
    if busy then 56 * (5 + 10 * (Q + 1) + 4 + 2 * 4 + bD) + erase + 1
    else 56 * (5 + 10 * (Q + 1) + 4 + 2 * 1 + bD) + 0 + 1
  else if p = 1 then
    if sIdx / 3 % 2 = 1 then 56 * (5 + 10 * (Q + 1) + 4 + 2 * 2 + bD) + 0 + 1
    else 56 * (5 + 10 * (Q + 1) + 4 + 2 * 1 + bD) + 0 + 1
  else if p = 2 then
    if busy then 56 * (5 + 10 * (Q + 1) + 4 + 2 * 5 + bD) + erase + 1
    else 56 * (5 + 10 * (Q + 1) + 4 + 2 * 3 + bD) + 1 + 1
  else if p = 3 then
    if sIdx / 3 % 2 = 1 then 0
    else 56 * (5 + 10 * (Q + 1) + 4 + 2 * 3 + bD) + 1 + 1
  else if p = 4 then 56 * (5 + 10 * (Q + 1) + 4 + 0 + bD) + 1 + 1
  else 56 * (5 + 10 * (Q + 1) + 4 + 2 * 2 + bD) + 0 + 1

/-- Read the stored result bit from a numeric reset label, returning `false` before the reset
block. -/
def phase1ReadoutNat (code : Code) (l : ℕ) : Bool :=
  if 5 + 10 * (controlSize code + 1) + 4 ≤ l then
    decide ((l - (5 + 10 * (controlSize code + 1) + 4)) % 2 = 1)
  else false

/-- Compute a compiled transition row by recovering its coin, control, and cell coordinates and
selecting the appropriate phase rule. -/
def phase1RowNat (code : Code) (i : ℕ) : ℕ :=
  let K := phase1Bound (controlSize code)
  let sIdx := i % 54
  let l := i / 54 % (K + 1)
  let cD := if K + 1 ≤ i / 54 then 1 else 0
  if l < 5 then phase1CopyRowNat l sIdx
  else if l < 5 + 2 * (controlSize code + 1) then phase1MarkLiveRowNat code cD l sIdx
  else if l < 5 + 8 * (controlSize code + 1) then phase1PendingRowNat (controlSize code) l sIdx
  else if l < 5 + 10 * (controlSize code + 1) then phase1MarkHaltRowNat code l sIdx
  else if l < 5 + 10 * (controlSize code + 1) + 4 then phase1HomeRowNat (controlSize code) l sIdx
  else phase1ResetRowNat (controlSize code) l sIdx

/-- Decode a phase machine's transition-table entry at the given coin, bounded label, and cell. -/
def phase1Table (p : CodeCore) (c : Bool) (q : Fin (phase1ControlSize p + 1))
    (s : CellCore) :
    Option (Fin (phase1ControlSize p + 1) × Turing.TM0.Stmt CellCore) :=
  phase1DecodeTransition (phase1ControlSize p)
    (p.getD (1 + (phase1ControlSize p + 1)
      + phase1RowIndex (phase1ControlSize p) c q.val (phase1CellIndex s)) 0)

/-- Decode a phase machine's Boolean readout from the parity of its stored control-label entry. -/
def phase1Readout (p : CodeCore) (q : Fin (phase1ControlSize p + 1)) : Bool :=
  p.getD (1 + q.val) 0 % 2 == 1

/-- Compile a source code into a finite table implementing copying, marked execution, homing,
and reset. -/
def tmCopyRunResetCompile (code : Code) : CodeCore :=
  phase1Bound (controlSize code)
    :: ((List.range (phase1Bound (controlSize code) + 1)).map
          (fun l => (phase1ReadoutNat code l).toNat)
        ++ (List.range (108 * (phase1Bound (controlSize code) + 1))).map
          (fun i => phase1RowNat code i))

/-- The compiled code has control bound `phase1Bound (controlSize code)`. -/
theorem phase1ControlSize_compile (code : Code) :
    phase1ControlSize (tmCopyRunResetCompile code) = phase1Bound (controlSize code) := rfl

/-- Indexing a mapped initial range within bounds returns the mapped function at that index. -/
theorem phase1MapRangeGetD (f : ℕ → ℕ) {m i : ℕ} (hi : i < m) :
    (List.map f (List.range m)).getD i 0 = f i := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- Looking up an in-range transition row in the compiled code returns `phase1RowNat code i`. -/
theorem tmCopyRunResetCompile_row (code : Code) (i : ℕ)
    (hi : i < 108 * (phase1Bound (controlSize code) + 1)) :
    (tmCopyRunResetCompile code).getD (1 + (phase1Bound (controlSize code) + 1) + i) 0
      = phase1RowNat code i := by
  have hidx : 1 + (phase1Bound (controlSize code) + 1) + i
      = (phase1Bound (controlSize code) + 1) + i + 1 := by omega
  rw [tmCopyRunResetCompile, hidx, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  exact phase1MapRangeGetD _ hi

/-- A compiled transition-table lookup is obtained by decoding the corresponding generated
numeric row. -/
theorem phase1Table_compile_lookup (code : Code) (c : Bool)
    (l : Fin (phase1Bound (controlSize code) + 1)) (s : CellCore) :
    phase1Table (tmCopyRunResetCompile code) c l s =
      phase1DecodeTransition (phase1Bound (controlSize code))
        (phase1RowNat code
          (phase1RowIndex (phase1Bound (controlSize code)) c l.val (phase1CellIndex s))) := by
  have hrow := phase1RowIndex_lt (K := phase1Bound (controlSize code)) c l.val l.isLt
    (phase1CellIndex s) (phase1CellIndex_lt s)
  simp only [phase1Table, phase1ControlSize_compile]
  rw [tmCopyRunResetCompile_row code _ hrow]

/-- Updating the work symbol and setting the visitation mark has the stated mixed-radix
cell-index formula. -/
theorem phase1CellIndex_write (a w : Option Bool) (hb : Bool) (m b : Option Bool) :
    phase1CellIndex (a, b, hb, some true)
      = 18 * (phase1CellIndex (a, w, hb, m) / 18) + 6 * symbolIndex b
        + 3 * (phase1CellIndex (a, w, hb, m) / 3 % 2) + 2 := by
  have h1 := symbolIndex_lt a
  have h2 := symbolIndex_lt w
  have h3 := symbolIndex_lt m
  have h4 := symbolIndex_lt b
  have h5 : symbolIndex (some true) = 2 := rfl
  simp only [phase1CellIndex, h5]
  cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Copying the input track into the work track has the stated mixed-radix cell-index formula. -/
theorem phase1CellIndex_fill (a w : Option Bool) (hb : Bool) (m : Option Bool) :
    phase1CellIndex (a, a, hb, m)
      = 18 * (phase1CellIndex (a, w, hb, m) / 18) + 6 * (phase1CellIndex (a, w, hb, m) / 18)
        + 3 * (phase1CellIndex (a, w, hb, m) / 3 % 2)
        + phase1CellIndex (a, w, hb, m) % 3 := by
  have h1 := symbolIndex_lt a
  have h2 := symbolIndex_lt w
  have h3 := symbolIndex_lt m
  simp only [phase1CellIndex]
  cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Clearing the work and visitation tracks has the stated mixed-radix cell-index formula. -/
theorem phase1CellIndex_erase (a w : Option Bool) (hb : Bool) (m : Option Bool) :
    phase1CellIndex (a, none, hb, none)
      = 18 * (phase1CellIndex (a, w, hb, m) / 18)
        + 3 * (phase1CellIndex (a, w, hb, m) / 3 % 2) := by
  have h1 := symbolIndex_lt a
  have h2 := symbolIndex_lt w
  have h3 := symbolIndex_lt m
  have h6 : symbolIndex none = 0 := rfl
  simp only [phase1CellIndex, h6]
  cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- A phase cell is busy exactly when its encoded work digit or visitation digit is nonzero. -/
theorem phaseBusy_digits (a w : Option Bool) (hb : Bool) (m : Option Bool) :
    phaseBusy (a, w, hb, m) = true ↔
      phase1CellIndex (a, w, hb, m) / 6 % 3 ≠ 0 ∨ phase1CellIndex (a, w, hb, m) % 3 ≠ 0 := by
  rcases a with _ | _ | _ <;> rcases w with _ | _ | _ <;> rcases m with _ | _ | _ <;>
    cases hb <;> simp [phaseBusy, phase1CellIndex, symbolIndex]

/-- Evaluating the compiled row generator at flattened valid coordinates selects the
corresponding phase-specific row formula. -/
theorem phase1RowNat_rowIndex (code : Code) (c : Bool) (l : ℕ)
    (hl : l < phase1Bound (controlSize code) + 1) (sIdx : ℕ) (hs : sIdx < 54) :
    phase1RowNat code (phase1RowIndex (phase1Bound (controlSize code)) c l sIdx)
      = (if l < 5 then phase1CopyRowNat l sIdx
        else if l < 5 + 2 * (controlSize code + 1)
          then phase1MarkLiveRowNat code c.toNat l sIdx
        else if l < 5 + 8 * (controlSize code + 1) then phase1PendingRowNat (controlSize code) l sIdx
        else if l < 5 + 10 * (controlSize code + 1) then phase1MarkHaltRowNat code l sIdx
        else if l < 5 + 10 * (controlSize code + 1) + 4
          then phase1HomeRowNat (controlSize code) l sIdx
        else phase1ResetRowNat (controlSize code) l sIdx) := by
  simp only [phase1RowNat, phase1RowIndex]
  have h1 : ((c.toNat * (phase1Bound (controlSize code) + 1) + l) * 54 + sIdx) % 54 = sIdx := by
    omega
  have hdiv : ((c.toNat * (phase1Bound (controlSize code) + 1) + l) * 54 + sIdx) / 54
      = c.toNat * (phase1Bound (controlSize code) + 1) + l := by
    omega
  simp only [h1, hdiv]
  cases c with
  | false =>
      have hn : ¬ (phase1Bound (controlSize code) + 1 ≤ l) := by omega
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hl, ite_eq_right hn]
  | true =>
      have hp : phase1Bound (controlSize code) + 1
          ≤ phase1Bound (controlSize code) + 1 + l := Nat.le_add_right _ _
      simp only [Bool.toNat_true, Nat.one_mul, Nat.add_mod, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt hl, ite_eq_left hp]

/-- Setting the home marker has the stated mixed-radix cell-index formula. -/
theorem phase1CellIndex_homeSet (a w : Option Bool) (hb : Bool) (m : Option Bool) :
    phase1CellIndex (a, w, true, m)
      = 18 * (phase1CellIndex (a, w, hb, m) / 18)
        + 6 * (phase1CellIndex (a, w, hb, m) / 6 % 3)
        + 3 + phase1CellIndex (a, w, hb, m) % 3 := by
  have h1 := symbolIndex_lt a
  have h2 := symbolIndex_lt w
  have h3 := symbolIndex_lt m
  simp only [phase1CellIndex]
  cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega


/-- The compiled transition table agrees with the structured phase-dispatch table after encoding
its control labels. -/
theorem phase1Table_compile (code : Code) (c : Bool)
    (p : ControlCore (Fin (controlSize code + 1))) (s : CellCore) :
    phase1Table (tmCopyRunResetCompile code) c
        (phase1ControlFin (controlSize code) p) s
      = (phaseDispatchTable (table code) (readout code) default c p s).map
          fun t => (phase1ControlFin (controlSize code) t.1, t.2) := by
  obtain ⟨a, w, hb, m⟩ := s
  have hiw := symbolIndex_lt w
  have him := symbolIndex_lt m
  have d6 : phase1CellIndex (a, w, hb, m) / 6 % 3 = symbolIndex w := by
    simp only [phase1CellIndex]
    cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have d3 : phase1CellIndex (a, w, hb, m) / 3 % 2 = hb.toNat := by
    simp only [phase1CellIndex]
    cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hlt := phase1ControlLabel_lt (controlSize code) p
  rw [phase1Table_compile_lookup]
  simp only [phase1ControlFin, Fin.val_mk, Fin.val_mk]
  rw [phase1RowNat_rowIndex code c _ hlt _ (phase1CellIndex_lt _)]
  rcases p with qc | pr | hst | ss
  · fin_cases qc
    · simp only [phase1ControlLabel]
      rw [ite_eq_left (by simp)]
      simp only [phase1CopyRowNat]
      rw [ite_eq_left (by simp)]
      simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
        Option.map_some]
      have henc : 56 * 1 + (2 + 18 * (phase1CellIndex (a, w, hb, m) / 18)
              + 6 * (phase1CellIndex (a, w, hb, m) / 6 % 3) + 3
              + phase1CellIndex (a, w, hb, m) % 3) + 1
          = phase1EncodeTransition (phase1Bound (controlSize code))
              (some (phase1ControlFin (controlSize code) (Sum.inl (⟨1, by omega⟩ : Fin 5)),
                Turing.TM0.Stmt.write (a, w, true, m))) := by
        simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
          phase1ControlLabel]
        rw [phase1CellIndex_homeSet a w hb m]
        omega
      rw [henc, phase1DecodeTransition_encode]
      rfl
    · simp only [phase1ControlLabel]
      rw [ite_eq_left (by simp)]
      simp only [phase1CopyRowNat]
      rw [ite_eq_right (by simp), ite_eq_left (by simp)]
      rcases a with _ | a'
      · simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
          Option.isSome_none]
        have h0 : phase1CellIndex (none, w, hb, m) / 18 = 0 := by
          have hsn : symbolIndex (none : Option Bool) = 0 := rfl
          simp only [phase1CellIndex, hsn]
          cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        rw [h0, ite_eq_left rfl]
        have henc : 56 * 3 + (2 + phase1CellIndex (none, w, hb, m)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code) (Sum.inl (⟨3, by omega⟩ : Fin 5)),
                  Turing.TM0.Stmt.write (none, w, hb, m))) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
          Option.isSome_some]
        have h0 : ¬ (phase1CellIndex (some a', w, hb, m) / 18 = 0) := by
          cases a' <;> cases hb <;>
            simp only [phase1CellIndex, symbolIndex, Bool.toNat_false, Bool.toNat_true] <;>
            omega
        rw [ite_eq_right h0]
        have henc : 56 * 2 + (2 + 18 * (phase1CellIndex (some a', w, hb, m) / 18)
              + 6 * (phase1CellIndex (some a', w, hb, m) / 18)
              + 3 * (phase1CellIndex (some a', w, hb, m) / 3 % 2)
              + phase1CellIndex (some a', w, hb, m) % 3) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code) (Sum.inl (⟨2, by omega⟩ : Fin 5)),
                  Turing.TM0.Stmt.write (some a', some a', hb, m))) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel]
          rw [phase1CellIndex_fill (some a') w hb m]
          omega
        rw [henc, phase1DecodeTransition_encode]
        rfl
    · simp only [phase1ControlLabel]
      rw [ite_eq_left (by simp)]
      simp only [phase1CopyRowNat]
      rw [ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_left (by simp)]
      simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable, Option.map_some]
      have henc : 56 * 1 + 1 + 1
          = phase1EncodeTransition (phase1Bound (controlSize code))
              (some (phase1ControlFin (controlSize code) (Sum.inl (⟨1, by omega⟩ : Fin 5)),
                Turing.TM0.Stmt.move Turing.Dir.right)) := by
        simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
          phase1ControlLabel]
      rw [henc, phase1DecodeTransition_encode]
      rfl
    · simp only [phase1ControlLabel]
      rw [ite_eq_left (by simp)]
      simp only [phase1CopyRowNat]
      rw [ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_left (by simp)]
      cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] at d3
      · simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker]
        rw [d3, ite_eq_right (by omega)]
        have henc : 56 * 3 + 0 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code) (Sum.inl (⟨3, by omega⟩ : Fin 5)),
                  Turing.TM0.Stmt.move Turing.Dir.left)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker]
        rw [d3, ite_eq_left rfl]
        have henc : 56 * 4 + (2 + phase1CellIndex (a, w, true, m)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code) (Sum.inl (⟨4, by omega⟩ : Fin 5)),
                  Turing.TM0.Stmt.write (a, w, true, m))) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel]
        rw [henc, phase1DecodeTransition_encode]
        rfl
    · simp only [phase1ControlLabel]
      rw [ite_eq_left (by simp)]
      simp only [phase1CopyRowNat]
      rw [ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_right (by simp)]
      simp only [phaseDispatchTable, liftMarkerTable, markerCopyTable]
      have hd0 : (default : Fin (controlSize code + 1)).val = 0 := rfl
      have henc : 56 * 5 + (2 + phase1CellIndex (a, w, hb, m)) + 1
          = phase1EncodeTransition (phase1Bound (controlSize code))
              (some (phase1ControlFin (controlSize code)
                  (Sum.inr (Sum.inl (Sum.inl ((default : Fin (controlSize code + 1)), false)))),
                Turing.TM0.Stmt.write (a, w, hb, m))) := by
        simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
          phase1ControlLabel, phase1LiveBase, hd0, Bool.toNat_false]
      rw [henc, phase1DecodeTransition_encode]
      rfl
  · rcases pr with ⟨q, b⟩ | pp | ⟨q, b⟩
    · rcases q with ⟨qv, hq⟩
      have hbt : b.toNat ≤ 1 := by cases b <;> simp
      cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] at d3
      all_goals
        simp only [phase1ControlLabel, phase1LiveBase]
      all_goals
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      all_goals
        simp only [phase1MarkLiveRowNat]
      all_goals
        have hq2 : (5 + 2 * qv + b.toNat - 5) / 2 = qv
            ∧ (5 + 2 * qv + b.toNat - 5) % 2 = b.toNat := by
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      all_goals
        rw [hq2.1, hq2.2, d6]
      all_goals
        simp only [phaseDispatchTable, markRunTable]
      all_goals
        rw [table_eq_sourceNat code c qv hq w]
      · cases hsrc : phase1SourceNat code c.toNat qv (symbolIndex w) with
        | zero =>
            rw [ite_eq_left rfl]
            have henc : 56 * (5 + 8 * (controlSize code + 1) + 2 * qv + b.toNat)
                  + (2 + 18 * (phase1CellIndex (a, w, false, m) / 18) + 6 * symbolIndex w
                    + 3 * (phase1CellIndex (a, w, false, m) / 3 % 2) + 2) + 1
                = phase1EncodeTransition (phase1Bound (controlSize code))
                    (some (phase1ControlFin (controlSize code)
                        (Sum.inr (Sum.inl (Sum.inr (Sum.inr (⟨qv, hq⟩, b))))),
                      Turing.TM0.Stmt.write (a, w, false, some true))) := by
              simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                phase1ControlLabel, phase1MarkHaltBase]
              rw [phase1CellIndex_write a w false m w]
              omega
            rw [henc, phase1DecodeTransition_encode]
            rfl
        | succ n =>
            rw [ite_eq_right (by omega)]
            have hn1 : n + 1 - 1 = n := by omega
            rw [hn1]
            have hn5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
            rcases hn5 with hn | hn | hn | hn | hn
            · rw [hn, ite_eq_left (by omega), ite_eq_left rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1))
                      + (if phase1CellIndex (a, w, false, m) / 3 % 2 = 1 then 1 else b.toNat))
                    + 1)
                  + (2 + 18 * (phase1CellIndex (a, w, false, m) / 18) + 6 * symbolIndex w
                    + 3 * (phase1CellIndex (a, w, false, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              some Turing.Dir.left))))),
                        Turing.TM0.Stmt.write (a, w, false, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w false m w, d3, ite_eq_right (by omega)]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.move Turing.Dir.left) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_left (by omega), ite_eq_right (by omega)]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1))
                      + (if phase1CellIndex (a, w, false, m) / 3 % 2 = 1 then 0 else b.toNat))
                    + 2)
                  + (2 + 18 * (phase1CellIndex (a, w, false, m) / 18) + 6 * symbolIndex w
                    + 3 * (phase1CellIndex (a, w, false, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              some Turing.Dir.right))))),
                        Turing.TM0.Stmt.write (a, w, false, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w false m w, d3, ite_eq_right (by omega)]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.move Turing.Dir.right) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_right (by omega),
                show (2 - 2 : ℕ) = symbolIndex none from rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1)) + b.toNat))
                  + (2 + 18 * (phase1CellIndex (a, w, false, m) / 18) + 6 * symbolIndex none
                    + 3 * (phase1CellIndex (a, w, false, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              none))))),
                        Turing.TM0.Stmt.write (a, none, false, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w false m none]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.write none) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_right (by omega),
                show (3 - 2 : ℕ) = symbolIndex (some false) from rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1)) + b.toNat))
                  + (2 + 18 * (phase1CellIndex (a, w, false, m) / 18)
                    + 6 * symbolIndex (some false)
                    + 3 * (phase1CellIndex (a, w, false, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              none))))),
                        Turing.TM0.Stmt.write (a, some false, false, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w false m (some false)]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.write (some false)) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_right (by omega),
                show (4 - 2 : ℕ) = symbolIndex (some true) from rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1)) + b.toNat))
                  + (2 + 18 * (phase1CellIndex (a, w, false, m) / 18)
                    + 6 * symbolIndex (some true)
                    + 3 * (phase1CellIndex (a, w, false, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              none))))),
                        Turing.TM0.Stmt.write (a, some true, false, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w false m (some true)]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.write (some true)) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
      · cases hsrc : phase1SourceNat code c.toNat qv (symbolIndex w) with
        | zero =>
            rw [ite_eq_left rfl]
            have henc : 56 * (5 + 8 * (controlSize code + 1) + 2 * qv + b.toNat)
                  + (2 + 18 * (phase1CellIndex (a, w, true, m) / 18) + 6 * symbolIndex w
                    + 3 * (phase1CellIndex (a, w, true, m) / 3 % 2) + 2) + 1
                = phase1EncodeTransition (phase1Bound (controlSize code))
                    (some (phase1ControlFin (controlSize code)
                        (Sum.inr (Sum.inl (Sum.inr (Sum.inr (⟨qv, hq⟩, b))))),
                      Turing.TM0.Stmt.write (a, w, true, some true))) := by
              simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                phase1ControlLabel, phase1MarkHaltBase]
              rw [phase1CellIndex_write a w true m w]
              omega
            rw [henc, phase1DecodeTransition_encode]
            rfl
        | succ n =>
            rw [ite_eq_right (by omega)]
            have hn1 : n + 1 - 1 = n := by omega
            rw [hn1]
            have hn5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
            rcases hn5 with hn | hn | hn | hn | hn
            · rw [hn, ite_eq_left (by omega), ite_eq_left rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1))
                      + (if phase1CellIndex (a, w, true, m) / 3 % 2 = 1 then 1 else b.toNat))
                    + 1)
                  + (2 + 18 * (phase1CellIndex (a, w, true, m) / 18) + 6 * symbolIndex w
                    + 3 * (phase1CellIndex (a, w, true, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), true),
                              some Turing.Dir.left))))),
                        Turing.TM0.Stmt.write (a, w, true, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w true m w, d3, ite_eq_left rfl,
                  show true.toNat = 1 from rfl]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.move Turing.Dir.left) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_left (by omega), ite_eq_right (by omega)]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1))
                      + (if phase1CellIndex (a, w, true, m) / 3 % 2 = 1 then 0 else b.toNat))
                    + 2)
                  + (2 + 18 * (phase1CellIndex (a, w, true, m) / 18) + 6 * symbolIndex w
                    + 3 * (phase1CellIndex (a, w, true, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), false),
                              some Turing.Dir.right))))),
                        Turing.TM0.Stmt.write (a, w, true, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w true m w, d3, ite_eq_left rfl,
                  show false.toNat = 0 from rfl]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.move Turing.Dir.right) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_right (by omega),
                show (2 - 2 : ℕ) = symbolIndex none from rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1)) + b.toNat))
                  + (2 + 18 * (phase1CellIndex (a, w, true, m) / 18) + 6 * symbolIndex none
                    + 3 * (phase1CellIndex (a, w, true, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              none))))),
                        Turing.TM0.Stmt.write (a, none, true, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w true m none]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.write none) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_right (by omega),
                show (3 - 2 : ℕ) = symbolIndex (some false) from rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1)) + b.toNat))
                  + (2 + 18 * (phase1CellIndex (a, w, true, m) / 18)
                    + 6 * symbolIndex (some false)
                    + 3 * (phase1CellIndex (a, w, true, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              none))))),
                        Turing.TM0.Stmt.write (a, some false, true, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w true m (some false)]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.write (some false)) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
            · rw [hn, ite_eq_right (by omega),
                show (4 - 2 : ℕ) = symbolIndex (some true) from rfl]
              have henc : 56 * (5 + 2 * (controlSize code + 1)
                    + 3 * (2 * (n / 5 % (controlSize code + 1)) + b.toNat))
                  + (2 + 18 * (phase1CellIndex (a, w, true, m) / 18)
                    + 6 * symbolIndex (some true)
                    + 3 * (phase1CellIndex (a, w, true, m) / 3 % 2) + 2) + 1
                  = phase1EncodeTransition (phase1Bound (controlSize code))
                      (some (phase1ControlFin (controlSize code)
                          (Sum.inr (Sum.inl (Sum.inr (Sum.inl
                            (((⟨n / 5 % (controlSize code + 1),
                              Nat.mod_lt _ (by omega)⟩ : Fin (controlSize code + 1)), b),
                              none))))),
                        Turing.TM0.Stmt.write (a, some true, true, some true))) := by
                simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
                  phase1ControlLabel, phase1PendingBase]
                rw [phase1CellIndex_write a w true m (some true)]
                omega
              have hdec : decodeTransition (controlSize code) (n + 1)
                  = some (⟨n / 5 % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩,
                    Turing.TM0.Stmt.write (some true)) := by
                simp only [decodeTransition, decodeAction, hn]
              rw [henc, phase1DecodeTransition_encode, hdec]
              rfl
    · obtain ⟨⟨q, b⟩, d⟩ := pp
      rcases q with ⟨qv, hq⟩
      have hbt : b.toNat ≤ 1 := by cases b <;> simp
      rcases d with _ | d | d
      · simp only [phase1ControlLabel, phase1PendingBase, phase1LiveBase]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
        simp only [phase1PendingRowNat]
        have hq3 : (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat)
              - (5 + 2 * (controlSize code + 1))) / 6 = qv
            ∧ (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat)
              - (5 + 2 * (controlSize code + 1))) / 3 % 2 = b.toNat
            ∧ (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat)
              - (5 + 2 * (controlSize code + 1))) % 3 = 0 := by
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        obtain ⟨e1, e2, e3⟩ := hq3
        rw [e1, e2, e3, ite_eq_left rfl]
        simp only [phaseDispatchTable, markRunTable, Option.map_some]
        have henc : 56 * (5 + 2 * qv + b.toNat) + (2 + phase1CellIndex (a, w, hb, m)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inl (Sum.inl ((⟨qv, hq⟩ : Fin (controlSize code + 1)), b)))),
                  Turing.TM0.Stmt.write (a, w, hb, m))) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1LiveBase]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · simp only [phase1ControlLabel, phase1PendingBase, phase1LiveBase]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
        simp only [phase1PendingRowNat]
        have hq3 : (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat) + 1
              - (5 + 2 * (controlSize code + 1))) / 6 = qv
            ∧ (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat) + 1
              - (5 + 2 * (controlSize code + 1))) / 3 % 2 = b.toNat
            ∧ (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat) + 1
              - (5 + 2 * (controlSize code + 1))) % 3 = 1 := by
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        obtain ⟨e1, e2, e3⟩ := hq3
        rw [e1, e2, e3, ite_eq_right (by omega), ite_eq_left rfl]
        simp only [phaseDispatchTable, markRunTable, Option.map_some]
        have henc : 56 * (5 + 2 * qv + b.toNat) + 0 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inl (Sum.inl ((⟨qv, hq⟩ : Fin (controlSize code + 1)), b)))),
                  Turing.TM0.Stmt.move Turing.Dir.left)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1LiveBase]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · simp only [phase1ControlLabel, phase1PendingBase, phase1LiveBase]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
        simp only [phase1PendingRowNat]
        have hq3 : (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat) + 2
              - (5 + 2 * (controlSize code + 1))) / 6 = qv
            ∧ (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat) + 2
              - (5 + 2 * (controlSize code + 1))) / 3 % 2 = b.toNat
            ∧ (5 + 2 * (controlSize code + 1) + 3 * (2 * qv + b.toNat) + 2
              - (5 + 2 * (controlSize code + 1))) % 3 = 2 := by
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        obtain ⟨e1, e2, e3⟩ := hq3
        rw [e1, e2, e3, ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [phaseDispatchTable, markRunTable, Option.map_some]
        have henc : 56 * (5 + 2 * qv + b.toNat) + 1 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inl (Sum.inl ((⟨qv, hq⟩ : Fin (controlSize code + 1)), b)))),
                  Turing.TM0.Stmt.move Turing.Dir.right)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1LiveBase]
        rw [henc, phase1DecodeTransition_encode]
        rfl
    · rcases q with ⟨qv, hq⟩
      have hbt : b.toNat ≤ 1 := by cases b <;> simp
      simp only [phase1ControlLabel, phase1MarkHaltBase, phase1HomeBase]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      simp only [phase1MarkHaltRowNat]
      have hq4 : (5 + 8 * (controlSize code + 1) + 2 * qv + b.toNat
            - (5 + 8 * (controlSize code + 1))) / 2 = qv
          ∧ (5 + 8 * (controlSize code + 1) + 2 * qv + b.toNat
            - (5 + 8 * (controlSize code + 1))) % 2 = b.toNat := by
        cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      obtain ⟨e1, e2⟩ := hq4
      rw [e1, e2]
      rcases Nat.mod_two_eq_zero_or_one (code.getD (1 + qv) 0) with hv | hv
      · rw [hv, ite_eq_right (by omega)]
        simp only [phaseDispatchTable, Option.map_some]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 2 * b.toNat + 0)
              + (2 + phase1CellIndex (a, w, hb, m)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inl (b, readout code ⟨qv, hq⟩)))),
                  Turing.TM0.Stmt.write (a, w, hb, m))) := by
          have hro : readout code ⟨qv, hq⟩ = false := by
            rw [readout, hv]
            rfl
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1HomeBase, hro, Bool.toNat_false]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · rw [hv, ite_eq_left rfl]
        simp only [phaseDispatchTable, Option.map_some]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 2 * b.toNat + 1)
              + (2 + phase1CellIndex (a, w, hb, m)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inl (b, readout code ⟨qv, hq⟩)))),
                  Turing.TM0.Stmt.write (a, w, hb, m))) := by
          have hro : readout code ⟨qv, hq⟩ = true := by
            rw [readout, hv]
            rfl
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1HomeBase, hro, Bool.toNat_true]
        rw [henc, phase1DecodeTransition_encode]
        rfl
  · obtain ⟨hleft, hbit⟩ := hst
    have hbt : hbit.toNat ≤ 1 := by cases hbit <;> simp
    have hlt2 : hleft.toNat ≤ 1 := by cases hleft <;> simp
    cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] at d3
    all_goals
      simp only [phase1ControlLabel, phase1HomeBase]
    all_goals
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega)]
    all_goals
      simp only [phase1HomeRowNat]
    · have hl2 : (5 + 10 * (controlSize code + 1) + 2 * hleft.toNat + hbit.toNat
            - (5 + 10 * (controlSize code + 1))) / 2 = hleft.toNat := by
        cases hleft <;> cases hbit <;>
          simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      rw [hl2, d3, ite_eq_right (by omega)]
      cases hleft with
      | false =>
          rw [ite_eq_right (by decide : ¬ (false.toNat = 1))]
          simp only [phaseDispatchTable, liftMarkerTable, markerHomeTable, phaseMarker]
          have henc : 56 * (5 + 10 * (controlSize code + 1) + 2 * false.toNat + hbit.toNat)
                + 0 + 1
              = phase1EncodeTransition (phase1Bound (controlSize code))
                  (some (phase1ControlFin (controlSize code)
                      (Sum.inr (Sum.inr (Sum.inl (false, hbit)))),
                    Turing.TM0.Stmt.move Turing.Dir.left)) := by
            simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
              phase1ControlLabel, phase1HomeBase, Bool.toNat_false]
          rw [henc, phase1DecodeTransition_encode]
          rfl
      | true =>
          rw [ite_eq_left (by decide : true.toNat = 1)]
          simp only [phaseDispatchTable, liftMarkerTable, markerHomeTable, phaseMarker]
          have henc : 56 * (5 + 10 * (controlSize code + 1) + 2 * true.toNat + hbit.toNat)
                + 1 + 1
              = phase1EncodeTransition (phase1Bound (controlSize code))
                  (some (phase1ControlFin (controlSize code)
                      (Sum.inr (Sum.inr (Sum.inl (true, hbit)))),
                    Turing.TM0.Stmt.move Turing.Dir.right)) := by
            simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
              phase1ControlLabel, phase1HomeBase, Bool.toNat_true]
          rw [henc, phase1DecodeTransition_encode]
          rfl
    · have hb2 : (5 + 10 * (controlSize code + 1) + 2 * hleft.toNat + hbit.toNat
            - (5 + 10 * (controlSize code + 1))) % 2 = hbit.toNat := by
        cases hleft <;> cases hbit <;>
          simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
      rw [hb2, d3, ite_eq_left rfl]
      simp only [phaseDispatchTable, liftMarkerTable, markerHomeTable, phaseMarker]
      have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + hbit.toNat)
            + (2 + phase1CellIndex (a, w, true, m)) + 1
          = phase1EncodeTransition (phase1Bound (controlSize code))
              (some (phase1ControlFin (controlSize code)
                  (Sum.inr (Sum.inr (Sum.inr (SweepPhase.rightErase, hbit)))),
                Turing.TM0.Stmt.write (a, w, true, m))) := by
        simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
          phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [henc, phase1DecodeTransition_encode]
      rfl
  · obtain ⟨sp, b⟩ := ss
    have hbt : b.toNat ≤ 1 := by cases b <;> simp
    have hbt2 : ∀ k : ℕ, k ≤ 5 →
        (5 + 10 * (controlSize code + 1) + 4 + 2 * k + b.toNat
            - (5 + 10 * (controlSize code + 1) + 4)) / 2 = k
          ∧ (5 + 10 * (controlSize code + 1) + 4 + 2 * k + b.toNat
            - (5 + 10 * (controlSize code + 1) + 4)) % 2 = b.toNat := by
      intro k hk
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    rcases sp with _ | _ | _ | _ | _ | _
    · obtain ⟨e1, e2⟩ := hbt2 0 (by omega)
      simp only [phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phase1ResetRowNat]
      rw [e1, e2, ite_eq_left rfl]
      cases hbusy : phaseBusy (a, w, hb, m)
      · have hP : ¬ (phase1CellIndex (a, w, hb, m) / 6 % 3 ≠ 0
            ∨ phase1CellIndex (a, w, hb, m) % 3 ≠ 0) := by
          intro hp
          rw [(phaseBusy_digits a w hb m).mpr hp] at hbusy
          exact absurd hbusy (by simp)
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rw [ite_eq_right hP]
        simp only [phaseDispatchTable, sweepResetTable, eraseCellP]
        rw [hbusy, ite_eq_right (by simp)]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 1 + b.toNat) + 0 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeL, b)))),
                  Turing.TM0.Stmt.move Turing.Dir.left)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · have hP : phase1CellIndex (a, w, hb, m) / 6 % 3 ≠ 0
            ∨ phase1CellIndex (a, w, hb, m) % 3 ≠ 0 :=
            (phaseBusy_digits a w hb m).mp hbusy
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rw [ite_eq_left hP]
        simp only [phaseDispatchTable, sweepResetTable, eraseCellP]
        rw [hbusy, ite_eq_left (by simp)]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 4 + b.toNat)
              + (2 + 18 * (phase1CellIndex (a, w, hb, m) / 18)
                + 3 * (phase1CellIndex (a, w, hb, m) / 3 % 2)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.stepRight, b)))),
                  Turing.TM0.Stmt.write (a, none, hb, none))) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
          rw [phase1CellIndex_erase a w hb m]
          omega
        rw [henc, phase1DecodeTransition_encode]
        rfl
    · obtain ⟨e1, e2⟩ := hbt2 1 (by omega)
      simp only [phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phase1ResetRowNat]
      rw [e1, e2, ite_eq_right (by omega), ite_eq_left rfl]
      cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] at d3
      · rw [d3, ite_eq_right (by omega)]
        simp only [phaseDispatchTable, sweepResetTable]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 1 + b.toNat) + 0 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeL, b)))),
                  Turing.TM0.Stmt.move Turing.Dir.left)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · rw [d3, ite_eq_left rfl]
        simp only [phaseDispatchTable, sweepResetTable]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 2 + b.toNat) + 0 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.leftErase, b)))),
                  Turing.TM0.Stmt.move Turing.Dir.left)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
        rw [henc, phase1DecodeTransition_encode]
        rfl
    · obtain ⟨e1, e2⟩ := hbt2 2 (by omega)
      simp only [phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phase1ResetRowNat]
      rw [e1, e2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      cases hbusy : phaseBusy (a, w, hb, m)
      · have hP : ¬ (phase1CellIndex (a, w, hb, m) / 6 % 3 ≠ 0
            ∨ phase1CellIndex (a, w, hb, m) % 3 ≠ 0) := by
          intro hp
          rw [(phaseBusy_digits a w hb m).mpr hp] at hbusy
          exact absurd hbusy (by simp)
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rw [ite_eq_right hP]
        simp only [phaseDispatchTable, sweepResetTable, eraseCellP]
        rw [hbusy, ite_eq_right (by simp)]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 3 + b.toNat) + 1 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, b)))),
                  Turing.TM0.Stmt.move Turing.Dir.right)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · have hP : phase1CellIndex (a, w, hb, m) / 6 % 3 ≠ 0
            ∨ phase1CellIndex (a, w, hb, m) % 3 ≠ 0 :=
            (phaseBusy_digits a w hb m).mp hbusy
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rw [ite_eq_left hP]
        simp only [phaseDispatchTable, sweepResetTable, eraseCellP]
        rw [hbusy, ite_eq_left (by simp)]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 5 + b.toNat)
              + (2 + 18 * (phase1CellIndex (a, w, hb, m) / 18)
                + 3 * (phase1CellIndex (a, w, hb, m) / 3 % 2)) + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.stepLeft, b)))),
                  Turing.TM0.Stmt.write (a, none, hb, none))) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
          rw [phase1CellIndex_erase a w hb m]
          omega
        rw [henc, phase1DecodeTransition_encode]
        rfl
    · obtain ⟨e1, e2⟩ := hbt2 3 (by omega)
      simp only [phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phase1ResetRowNat]
      rw [e1, e2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      cases hb <;> simp only [Bool.toNat_false, Bool.toNat_true] at d3
      · rw [d3, ite_eq_right (by omega)]
        simp only [phaseDispatchTable, sweepResetTable]
        have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 3 + b.toNat) + 1 + 1
            = phase1EncodeTransition (phase1Bound (controlSize code))
                (some (phase1ControlFin (controlSize code)
                    (Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, b)))),
                  Turing.TM0.Stmt.move Turing.Dir.right)) := by
          simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
            phase1ControlLabel, phase1ResetBase, sweepIdx]
        rw [henc, phase1DecodeTransition_encode]
        rfl
      · rw [d3, ite_eq_left rfl]
        simp only [phaseDispatchTable, sweepResetTable]
        rfl
    · obtain ⟨e1, e2⟩ := hbt2 4 (by omega)
      simp only [phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phase1ResetRowNat]
      rw [e1, e2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
      simp only [phaseDispatchTable, sweepResetTable, Option.map_some]
      have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 0 + b.toNat) + 1 + 1
          = phase1EncodeTransition (phase1Bound (controlSize code))
              (some (phase1ControlFin (controlSize code)
                  (Sum.inr (Sum.inr (Sum.inr (SweepPhase.rightErase, b)))),
                Turing.TM0.Stmt.move Turing.Dir.right)) := by
        simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
          phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [henc, phase1DecodeTransition_encode]
      rfl
    · obtain ⟨e1, e2⟩ := hbt2 5 (by omega)
      simp only [phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phase1ResetRowNat]
      rw [e1, e2, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      simp only [phaseDispatchTable, sweepResetTable, Option.map_some]
      have henc : 56 * (5 + 10 * (controlSize code + 1) + 4 + 2 * 2 + b.toNat) + 0 + 1
          = phase1EncodeTransition (phase1Bound (controlSize code))
              (some (phase1ControlFin (controlSize code)
                  (Sum.inr (Sum.inr (Sum.inr (SweepPhase.leftErase, b)))),
                Turing.TM0.Stmt.move Turing.Dir.left)) := by
        simp only [phase1EncodeTransition, phase1ActionIndex, phase1ControlFin, Fin.val_mk,
          phase1ControlLabel, phase1ResetBase, sweepIdx]
      rw [henc, phase1DecodeTransition_encode]
      rfl

/-- Embed a structured phase configuration into the compiled finite control space, preserving
its tape. -/
def phase1EmbedCfg (Q : ℕ) (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (Q + 1)))) :
    Turing.TM0.Cfg CellCore (Fin (phase1Bound Q + 1)) :=
  ⟨phase1ControlFin Q cfg.q, cfg.Tape⟩

/-- The control state of an embedded configuration is its encoded finite control label. -/
theorem phase1EmbedCfg_q (Q : ℕ) (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (Q + 1)))) :
    (phase1EmbedCfg Q cfg).q = phase1ControlFin Q cfg.q := rfl

/-- One compiled-machine step commutes with embedding a structured phase-dispatch configuration. -/
theorem tmCompile_step (code : Code) (c : Bool)
    (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (controlSize code + 1)))) :
    Turing.TM0.step (phase1Table (tmCopyRunResetCompile code) c)
        (phase1EmbedCfg (controlSize code) cfg)
      = (Turing.TM0.step (phaseDispatchTable (table code) (readout code) default c) cfg).map
          (phase1EmbedCfg (controlSize code)) := by
  obtain ⟨q, T⟩ := cfg
  simp only [phase1EmbedCfg, TM0_step_apply, phase1Table_compile code c]
  cases phaseDispatchTable (table code) (readout code) default c q T.head <;> rfl

/-- Embedding a phase-dispatch configuration preserves the coin-halting predicate in the
compiled machine. -/
theorem tmCompile_coinHalt (code : Code)
    (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (controlSize code + 1)))) :
    coinHalt (phase1Table (tmCopyRunResetCompile code))
        (phase1EmbedCfg (controlSize code) cfg)
      = coinHalt (phaseDispatchTable (table code) (readout code) default) cfg := by
  obtain ⟨q, T⟩ := cfg
  simp only [coinHalt, phase1EmbedCfg, phase1Table_compile code false,
    phase1Table_compile code true]
  cases phaseDispatchTable (table code) (readout code) default false q T.head <;>
    cases phaseDispatchTable (table code) (readout code) default true q T.head <;> rfl

/-- The numeric readout at an encoded structured control label equals its phase-dispatch
acceptance bit. -/
theorem phase1ReadoutNat_accept (code : Code) (p : ControlCore (Fin (controlSize code + 1))) :
    phase1ReadoutNat code (phase1ControlLabel (controlSize code) p) = phaseDispatchAccept p := by
  have hb : ∀ b : Bool, b.toNat ≤ 1 := by intro b; cases b <;> simp
  rcases p with qc | pr | hst | ss
  · have hq := qc.isLt
    simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept]
    rw [ite_eq_right (by omega)]
  · rcases pr with ⟨q, b⟩ | pp | ⟨q, b⟩
    · have hq := q.isLt; have hbb := hb b
      simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept, phase1LiveBase]
      rw [ite_eq_right (by omega)]
    · obtain ⟨⟨q, b⟩, d⟩ := pp
      have hq := q.isLt; have hbb := hb b
      cases d with
      | none =>
          simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept, phase1PendingBase]
          rw [ite_eq_right (by omega)]
      | some d' =>
          cases d' with
          | left =>
              simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept,
                phase1PendingBase]
              rw [ite_eq_right (by omega)]
          | right =>
              simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept,
                phase1PendingBase]
              rw [ite_eq_right (by omega)]
    · have hq := q.isLt; have hbb := hb b
      simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept, phase1MarkHaltBase]
      rw [ite_eq_right (by omega)]
  · obtain ⟨left, bit⟩ := hst
    have hbl := hb left; have hbt := hb bit
    simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept, phase1HomeBase]
    rw [ite_eq_right (by omega)]
  · obtain ⟨sp, b⟩ := ss
    have hs : sweepIdx sp ≤ 5 := by cases sp <;> simp [sweepIdx]
    have hbb := hb b
    simp only [phase1ControlLabel, phase1ReadoutNat, phaseDispatchAccept, phase1ResetBase]
    rw [ite_eq_left (by omega)]
    have hsub : 5 + 10 * (controlSize code + 1) + 4 + 2 * sweepIdx sp + b.toNat
          - (5 + 10 * (controlSize code + 1) + 4) = 2 * sweepIdx sp + b.toNat := by omega
    have hmod : (2 * sweepIdx sp + b.toNat) % 2 = b.toNat := by omega
    simp only [hsub, hmod]
    cases b <;> rfl

/-- The compiled code's readout agrees with the phase-dispatch acceptance bit on encoded control
labels. -/
theorem tmCompile_readout (code : Code)
    (p : ControlCore (Fin (controlSize code + 1))) :
    phase1Readout (tmCopyRunResetCompile code) (phase1ControlFin (controlSize code) p)
      = phaseDispatchAccept p := by
  have hlt := phase1ControlLabel_lt (controlSize code) p
  have hl := phase1ReadoutNat_accept code p
  have h1 : phase1Readout (tmCopyRunResetCompile code) (phase1ControlFin (controlSize code) p)
      = ((tmCopyRunResetCompile code).getD (1 + phase1ControlLabel (controlSize code) p) 0 % 2
          == 1) := rfl
  rw [h1, tmCopyRunResetCompile, show 1 + phase1ControlLabel (controlSize code) p
      = phase1ControlLabel (controlSize code) p + 1 from Nat.add_comm _ _, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by simpa [List.length_map, List.length_range] using! hlt),
    phase1MapRangeGetD _ hlt, hl]
  cases phaseDispatchAccept p <;> rfl

/-- Compiled and structured configuration runs have equal read and transition counts, and their
stopped configurations correspond under embedding. -/
theorem tmCompile_coinConfigRunAux (code : Code) (coins : List Bool)
    (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (controlSize code + 1)))) :
    (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code)) coins
        (phase1EmbedCfg (controlSize code) cfg)).reads
      = (coinConfigRunAux (phaseDispatchTable (table code) (readout code) default) coins cfg).reads
      ∧ (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code)) coins
        (phase1EmbedCfg (controlSize code) cfg)).transitions
      = (coinConfigRunAux (phaseDispatchTable (table code) (readout code) default) coins cfg).transitions
      ∧ (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code)) coins
        (phase1EmbedCfg (controlSize code) cfg)).stopped
      = (coinConfigRunAux (phaseDispatchTable (table code) (readout code) default) coins cfg).stopped.map
          (phase1EmbedCfg (controlSize code)) := by
  induction coins generalizing cfg with
  | nil =>
      simp only [coinConfigRunAux]
      rw [tmCompile_coinHalt code cfg]
      by_cases hh : coinHalt (phaseDispatchTable (table code) (readout code) default) cfg = true
      · simp only [hh, ite_true]
        exact ⟨trivial, trivial, rfl⟩
      · simp only [ite_eq_right hh]
        exact ⟨trivial, trivial, rfl⟩
  | cons c cs ih =>
      simp only [coinConfigRunAux]
      rw [tmCompile_coinHalt code cfg]
      by_cases hh : coinHalt (phaseDispatchTable (table code) (readout code) default) cfg = true
      · simp only [hh, ite_true]
        exact ⟨trivial, trivial, rfl⟩
      · simp only [ite_eq_right hh, tmCompile_step code c cfg]
        cases Turing.TM0.step
            (phaseDispatchTable (table code) (readout code) default c) cfg with
        | none =>
            simp only [Option.map_none]
            exact ⟨trivial, trivial, rfl⟩
        | some next =>
            simp only [Option.map_some]
            obtain ⟨h1, h2, h3⟩ := ih next
            rw [h1, h2, h3]
            exact ⟨rfl, rfl, rfl⟩

/-- Compiled and structured phase-dispatch runs return the same acceptance result and read count
on every coin list. -/
theorem tmCompile_coinTapeRunAux (code : Code) (coins : List Bool)
    (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (controlSize code + 1)))) :
    coinTapeRunAux (phase1Table (tmCopyRunResetCompile code))
        (phase1Readout (tmCopyRunResetCompile code)) coins
        (phase1EmbedCfg (controlSize code) cfg)
      = coinTapeRunAux (phaseDispatchTable (table code) (readout code) default)
          phaseDispatchAccept coins cfg := by
  induction coins generalizing cfg with
  | nil =>
      simp only [coinTapeRunAux]
      rw [tmCompile_coinHalt code cfg]
      by_cases hh : coinHalt (phaseDispatchTable (table code) (readout code) default) cfg = true
      · simp only [hh, ite_true, phase1EmbedCfg_q, tmCompile_readout code cfg.q]
      · simp only [ite_eq_right hh]
  | cons c cs ih =>
      simp only [coinTapeRunAux]
      rw [tmCompile_coinHalt code cfg]
      by_cases hh : coinHalt (phaseDispatchTable (table code) (readout code) default) cfg = true
      · simp only [hh, ite_true, phase1EmbedCfg_q, tmCompile_readout code cfg.q]
      · simp only [ite_eq_right hh, tmCompile_step code c cfg]
        cases Turing.TM0.step
            (phaseDispatchTable (table code) (readout code) default c) cfg with
        | none =>
            simp only [phase1EmbedCfg_q, tmCompile_readout code cfg.q, Option.map_none]
        | some next =>
            simp only [Option.map_some]
            rw [ih next]

/-- For a source code with common halting, a fully consumed halting source word yields a
compiled copy–run–reset execution with the same acceptance bit. The statement supplies exact
read and transition counts, a clean final tape at home, and bounds on the marked execution
interval. -/
theorem tmCopyRunResetCompile_run (code : Code) (hc : commonHalt code)
    (input : List Bool) (w fs : List Bool)
    (final : Turing.TM0.Cfg (Option Bool) (Fin (controlSize code + 1)))
    (hstop : (coinConfigRunAux (table code) w
        ⟨default, (phaseCopyResult input).map phaseWorkMap⟩).stopped = some final)
    (hread : (coinConfigRunAux (table code) w
        ⟨default, (phaseCopyResult input).map phaseWorkMap⟩).reads = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (Tf T'' : Turing.Tape CellCore) (off' lo' hi' : ℤ),
      (PhaseHomeAt T'' 0 ∧ PhaseInputSame (phaseCopyResult input) T'' 0 ∧
        (∀ i : ℤ, phaseBusy (T''.nth i) = false) ∧
        Tf.map phaseWorkMap = final.Tape ∧
        PhaseMarkAbs Tf off' lo' hi' ∧
        -(w.length : ℤ) ≤ off' ∧ off' ≤ (w.length : ℤ) ∧
        lo' ≤ 1 ∧ 0 ≤ hi' ∧ hi' ≤ 2 * w.length + 1 ∧ 1 - lo' ≤ 2 * w.length + 1) ∧
      ∀ (jcopy jhome jreset tail : List Bool) (c₁ c₂ c₃ x : Bool),
        jcopy.length = 3 * input.length + 3 →
        jhome.length = (if sf then (-off').toNat else off'.toNat) →
        jreset.length = 3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5 →
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput input))).stopped
          = some (phase1EmbedCfg (controlSize code)
              ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, readout code final.q))), T''⟩) ∧
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput input))).reads
          = (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1
              + (if sf then (-off').toNat else off'.toNat) + 1
              + (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5) ∧
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput input))).transitions
          = (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1
              + (if sf then (-off').toNat else off'.toNat) + 1
              + (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5) ∧
        (coinTapeRunAux (phase1Table (tmCopyRunResetCompile code))
            (phase1Readout (tmCopyRunResetCompile code))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput input)))
          = (some (readout code final.q),
              (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1
                + (if sf then (-off').toNat else off'.toNat) + 1
                + (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5)) := by
  obtain ⟨sf, Tf, T'', off', lo', hi', hprop, hrun⟩ :=
    phaseDispatchRunReset (table code) (readout code) hc default input w fs final hstop hread hfs
  refine ⟨sf, Tf, T'', off', lo', hi', hprop, ?_⟩
  intro jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset
  obtain ⟨hc1, hc2, -, -⟩ := hrun jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset
  have hsim := tmCompile_coinConfigRunAux code
    ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))) ++ tail)
    ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩
  obtain ⟨hr1, hr2, hr3⟩ := hsim
  rw [hc1] at hr1 hr2 hr3
  have hts := tmCompile_coinTapeRunAux code
    ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))) ++ tail)
    ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩
  exact ⟨hr3, hr1, hr2, hts.trans hc2⟩

/-- The coin and transition budget `6 * n + 15 * m + 16` for copying an input of length `n` and
simulating a source word of length `m`. -/
def tmCopyRunResetCoinBudget (n m : ℕ) : ℕ := 6 * n + 15 * m + 16

/-- The compiled execution associated with a fully consumed halting source word uses at most
`tmCopyRunResetCoinBudget input.length w.length` reads and transitions, with the stated
bounds on the marked interval. -/
theorem tmCopyRunResetCompile_coinBudget_bound (code : Code) (hc : commonHalt code)
    (input : List Bool) (w fs : List Bool)
    (final : Turing.TM0.Cfg (Option Bool) (Fin (controlSize code + 1)))
    (hstop : (coinConfigRunAux (table code) w
        ⟨default, (phaseCopyResult input).map phaseWorkMap⟩).stopped = some final)
    (hread : (coinConfigRunAux (table code) w
        ⟨default, (phaseCopyResult input).map phaseWorkMap⟩).reads = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (off' lo' hi' : ℤ),
      (-(2 * w.length : ℤ) ≤ lo' ∧ hi' ≤ 2 * w.length + 1) ∧
      ∀ (jcopy jhome jreset tail : List Bool) (c₁ c₂ c₃ x : Bool),
        jcopy.length = 3 * input.length + 3 →
        jhome.length = (if sf then (-off').toNat else off'.toNat) →
        jreset.length = 3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5 →
        ((coinConfigRunAux (phase1Table (tmCopyRunResetCompile code))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput input))).reads
          ≤ tmCopyRunResetCoinBudget input.length w.length ∧
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile code))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput input))).transitions
          ≤ tmCopyRunResetCoinBudget input.length w.length) := by
  obtain ⟨sf, Tf, T'', off', lo', hi', hprop, hrun⟩ :=
    tmCopyRunResetCompile_run code hc input w fs final hstop hread hfs
  obtain ⟨_, _, _, _, _, hoffLo, hoffHi, hlo, hhi, hhiHi, hloLo⟩ := hprop
  refine ⟨sf, off', lo', hi', ⟨by omega, by omega⟩, ?_⟩
  intro jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset
  obtain ⟨_, hreads, htrans, _⟩ :=
    hrun jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset
  have hOff : (if sf then (-off').toNat else off'.toNat) ≤ w.length := by
    cases sf with
    | false => exact Int.toNat_le.2 (by omega)
    | true => exact Int.toNat_le.2 (by omega)
  have hMax : (max hi' ((input.length : ℤ) - 1)).toNat ≤ 2 * w.length + 1 + input.length := by
    apply Int.toNat_le.2
    apply max_le <;> omega
  have hLo : (-lo').toNat ≤ 2 * w.length := Int.toNat_le.2 (by omega)
  have hbud : tmCopyRunResetCoinBudget input.length w.length
      = 6 * input.length + 15 * w.length + 16 := rfl
  constructor
  · rw [hreads, hbud]; omega
  · rw [htrans, hbud]; omega

/-- Follow a finite coin prefix, keeping the current configuration once halting or an
unavailable transition is encountered. -/
def coinPrefixCfg {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    List Bool → Turing.TM0.Cfg Γ Λ → Turing.TM0.Cfg Γ Λ
  | [], cfg => cfg
  | c :: cs, cfg =>
    if coinHalt M cfg then cfg else
    match Turing.TM0.step (M c) cfg with
    | none => cfg
    | some next => coinPrefixCfg M cs next

/-- Following any coin prefix from a coin-halting configuration leaves that configuration
unchanged. -/
theorem coinPrefixCfg_halted {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) {cfg : Turing.TM0.Cfg Γ Λ}
    (h : coinHalt M cfg = true) (l : List Bool) : coinPrefixCfg M l cfg = cfg := by
  cases l with
  | nil => rfl
  | cons c cs => simp only [coinPrefixCfg, h, ite_true]

/-- For a machine with coin-independent halting, following concatenated prefixes equals
following them successively. -/
theorem coinPrefixCfg_append {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ)
    (hM : ∀ (q : Λ) (s : Γ), (M false q s = none) ↔ (M true q s = none)) :
    ∀ (as bs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      coinPrefixCfg M (as ++ bs) cfg = coinPrefixCfg M bs (coinPrefixCfg M as cfg) := by
  intro as bs cfg
  induction as generalizing bs cfg with
  | nil => rfl
  | cons a as' ih =>
    by_cases hh : coinHalt M cfg = true
    · simp only [List.cons_append, coinPrefixCfg, hh, ite_true]
      exact (coinPrefixCfg_halted M hh bs).symm
    · have hch : coinHalt M cfg = false := by
        cases hc : coinHalt M cfg with
        | false => rfl
        | true => exact absurd hc hh
      have hstep : Turing.TM0.step (M a) cfg ≠ none := by
        intro hnone
        have htab : M a cfg.q cfg.Tape.head = none := (TM0_step_eq_none _ _).mp hnone
        have hch : coinHalt M cfg = true := by
          cases a with
          | false =>
              simpa [coinHalt] using! ⟨htab, (hM cfg.q cfg.Tape.head).mp htab⟩
          | true =>
              simpa [coinHalt] using! ⟨(hM cfg.q cfg.Tape.head).mpr htab, htab⟩
        rw [hch] at hh
        exact absurd hh (by simp)
      simp only [List.cons_append, coinPrefixCfg, hch, Bool.false_eq_true, ↓reduceIte]
      cases hs : Turing.TM0.step (M a) cfg with
      | none => exact absurd hs hstep
      | some next => exact ih bs next

/-- A successful `coinStepsAux` trace determines the same configuration under prefix execution. -/
theorem coinPrefixCfg_of_trace {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    ∀ (l : List Bool) (cfg final : Turing.TM0.Cfg Γ Λ),
      coinStepsAux M l cfg = some final → coinPrefixCfg M l cfg = final := by
  intro l cfg final
  induction l generalizing cfg with
  | nil => intro h; exact Option.some.inj h
  | cons c cs ih =>
    intro h
    rw [coinStepsAux, Option.bind_eq_some_iff] at h
    obtain ⟨next, hs, hrest⟩ := h
    have hch : coinHalt M cfg = false := by
      cases hc : coinHalt M cfg with
      | false => rfl
      | true =>
          have hnone := Qatlib.Concepts.ClassicalTape.TapeCompilation.coinHalt_step_none M cfg hc c
          rw [hnone] at hs
          exact absurd hs (by simp)
    simp only [coinPrefixCfg, hch, Bool.false_eq_true, ↓reduceIte, hs]
    exact ih next hrest

/-- A configuration run with no coins performs zero reads. -/
theorem coinConfigRunAux_nil_reads {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (coinConfigRunAux M [] cfg).reads = 0 := by
  simp only [coinConfigRunAux]; split <;> rfl

/-- A configuration run with no coins performs zero transitions. -/
theorem coinConfigRunAux_nil_transitions {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (coinConfigRunAux M [] cfg).transitions = 0 := by
  simp only [coinConfigRunAux]; split <;> rfl

/-- A successful step from a live configuration consumes the first coin and adds one read and
transition to the remaining run. -/
theorem coinConfigRunAux_cons_some {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    {M : Bool → Turing.TM0.Machine Γ Λ} {c : Bool} {cs : List Bool}
    {cfg next : Turing.TM0.Cfg Γ Λ}
    (hchf : coinHalt M cfg = false) (hstep : Turing.TM0.step (M c) cfg = some next) :
    coinConfigRunAux M (c :: cs) cfg =
      ⟨(coinConfigRunAux M cs next).stopped,
        (coinConfigRunAux M cs next).reads + 1,
        (coinConfigRunAux M cs next).transitions + 1⟩ := by
  simp only [coinConfigRunAux, hchf, hstep]
  rw [ite_eq_right (by simp)]

/-- A configuration run reads at most the number of coins supplied. -/
theorem coinConfigRunAux_reads_le {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    ∀ (l : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      (coinConfigRunAux M l cfg).reads ≤ l.length := by
  intro l cfg
  induction l generalizing cfg with
  | nil => rw [coinConfigRunAux_nil_reads]; exact Nat.zero_le _
  | cons c cs ih =>
    by_cases hh : coinHalt M cfg = true
    · simp only [coinConfigRunAux, hh, ite_true]
      exact Nat.zero_le _
    · have hch : coinHalt M cfg = false := by
        cases hc : coinHalt M cfg with
        | false => rfl
        | true => exact absurd hc hh
      rw [coinConfigRunAux, ite_eq_right hh]
      cases hs : Turing.TM0.step (M c) cfg with
      | none => exact Nat.succ_le_succ (Nat.zero_le _)
      | some next =>
          have h := ih next
          show (coinConfigRunAux M cs next).reads + 1 ≤ cs.length + 1
          omega

/-- For coin-independent halting, a run on concatenated coin lists continues from the prefix
configuration, with additive read and transition counts. -/
theorem coinConfigRunAux_app {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ)
    (hM : ∀ (q : Λ) (s : Γ), (M false q s = none) ↔ (M true q s = none)) :
    ∀ (pre suf : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      (coinConfigRunAux M (pre ++ suf) cfg).stopped
        = (coinConfigRunAux M suf (coinPrefixCfg M pre cfg)).stopped ∧
      (coinConfigRunAux M (pre ++ suf) cfg).reads
        = (coinConfigRunAux M pre cfg).reads
          + (coinConfigRunAux M suf (coinPrefixCfg M pre cfg)).reads ∧
      (coinConfigRunAux M (pre ++ suf) cfg).transitions
        = (coinConfigRunAux M pre cfg).transitions
          + (coinConfigRunAux M suf (coinPrefixCfg M pre cfg)).transitions := by
  intro pre suf cfg
  induction pre generalizing cfg with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩
    · show (coinConfigRunAux M suf cfg).reads = (coinConfigRunAux M [] cfg).reads
          + (coinConfigRunAux M suf cfg).reads
      rw [coinConfigRunAux_nil_reads]; omega
    · show (coinConfigRunAux M suf cfg).transitions = (coinConfigRunAux M [] cfg).transitions
          + (coinConfigRunAux M suf cfg).transitions
      rw [coinConfigRunAux_nil_transitions]; omega
  | cons c cs ih =>
    by_cases hh : coinHalt M cfg = true
    · have hL : coinConfigRunAux M (c :: (cs ++ suf)) cfg = ⟨some cfg, 0, 0⟩ := by
        simp only [coinConfigRunAux, hh, ite_true]
      have hP : coinConfigRunAux M (c :: cs) cfg = ⟨some cfg, 0, 0⟩ := by
        simp only [coinConfigRunAux, hh, ite_true]
      have hC : coinConfigRunAux M suf cfg = ⟨some cfg, 0, 0⟩ := by
        cases suf with
        | nil => simp only [coinConfigRunAux, hh, ite_true]
        | cons c' cs' => simp only [coinConfigRunAux, hh, ite_true]
      have hpc : coinPrefixCfg M (c :: cs) cfg = cfg := by
        simp only [coinPrefixCfg, hh, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · show (coinConfigRunAux M (c :: (cs ++ suf)) cfg).stopped
            = (coinConfigRunAux M suf (coinPrefixCfg M (c :: cs) cfg)).stopped
        rw [hpc, hL, hC]
      · show (coinConfigRunAux M (c :: (cs ++ suf)) cfg).reads
            = (coinConfigRunAux M (c :: cs) cfg).reads
              + (coinConfigRunAux M suf (coinPrefixCfg M (c :: cs) cfg)).reads
        rw [hpc, hL, hP, hC]
        rfl
      · show (coinConfigRunAux M (c :: (cs ++ suf)) cfg).transitions
            = (coinConfigRunAux M (c :: cs) cfg).transitions
              + (coinConfigRunAux M suf (coinPrefixCfg M (c :: cs) cfg)).transitions
        rw [hpc, hL, hP, hC]
        rfl
    · have hch : coinHalt M cfg = false := by
        cases hc : coinHalt M cfg with
        | false => rfl
        | true => exact absurd hc hh
      cases hs : Turing.TM0.step (M c) cfg with
      | none =>
          have htab : M c cfg.q cfg.Tape.head = none := (TM0_step_eq_none _ _).mp hs
          have hc2 : coinHalt M cfg = true := by
            cases c with
            | false => simp [coinHalt, htab, (hM cfg.q cfg.Tape.head).mp htab]
            | true => simp [coinHalt, htab, (hM cfg.q cfg.Tape.head).mpr htab]
          exact absurd hc2 hh
      | some next =>
          have hL := coinConfigRunAux_cons_some hch hs (cs := cs ++ suf)
          have hP := coinConfigRunAux_cons_some hch hs (cs := cs)
          have hpc : coinPrefixCfg M (c :: cs) cfg = coinPrefixCfg M cs next := by
            simp only [coinPrefixCfg, hch, Bool.false_eq_true, ↓reduceIte, hs]
          obtain ⟨h1, h2, h3⟩ := ih next
          refine ⟨?_, ?_, ?_⟩
          · show (coinConfigRunAux M (c :: (cs ++ suf)) cfg).stopped
                = (coinConfigRunAux M suf (coinPrefixCfg M (c :: cs) cfg)).stopped
            rw [hpc, hL, h1]
          · show (coinConfigRunAux M (c :: (cs ++ suf)) cfg).reads
                = (coinConfigRunAux M (c :: cs) cfg).reads
                  + (coinConfigRunAux M suf (coinPrefixCfg M (c :: cs) cfg)).reads
            rw [hpc, hL, hP]
            show (coinConfigRunAux M (cs ++ suf) next).reads + 1
                = (coinConfigRunAux M cs next).reads + 1
                  + (coinConfigRunAux M suf (coinPrefixCfg M cs next)).reads
            rw [h2]
            omega
          · show (coinConfigRunAux M (c :: (cs ++ suf)) cfg).transitions
                = (coinConfigRunAux M (c :: cs) cfg).transitions
                  + (coinConfigRunAux M suf (coinPrefixCfg M (c :: cs) cfg)).transitions
            rw [hpc, hL, hP]
            show (coinConfigRunAux M (cs ++ suf) next).transitions + 1
                = (coinConfigRunAux M cs next).transitions + 1
                  + (coinConfigRunAux M suf (coinPrefixCfg M cs next)).transitions
            rw [h3]
            omega

/-- The tape has the prescribed home marker, its head lies in `[Wlo, Whi]`, and every busy cell
lies in that absolute interval. -/
def EnvCore (T : Turing.Tape CellCore) (off Wlo Whi : ℤ) : Prop :=
  PhaseHomeAt T off ∧ Wlo ≤ off ∧ off ≤ Whi ∧
    ∀ i : ℤ, phaseBusy (T.nth i) = true → Wlo ≤ i + off ∧ i + off ≤ Whi

/-- The initialized phase-input tape has no home markers. -/
theorem phaseInputTape_home (input : List Bool) (i : ℤ) :
    ((Turing.Tape.mk₁ (phaseInput input)).nth i).2.2.1 = false := by
  by_cases hi : 0 ≤ i
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = (a : ℤ) := ⟨Int.toNat i, (Int.toNat_of_nonneg hi).symm⟩
    subst ha
    rw [phaseTape_mk₁_nth]
    by_cases han : a < input.length
    · rw [List.getI_eq_getElem (phaseInput input) (by simpa [phaseInput] using! han)]; simp
        [phaseInput]
    · rw [List.getI_eq_default (phaseInput input) (by simpa [phaseInput] using! han)]; rfl
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = -((a : ℤ)) - 1 := by
      have hpos : (0 : ℤ) ≤ -i := by omega
      have h1 := Int.toNat_of_nonneg hpos
      exact ⟨Int.toNat (-i) - 1, by omega⟩
    subst ha
    rw [phaseTape_mk₁_nth_neg]
    rfl

/-- An initialized input-track cell is nonblank exactly at positions in the input interval. -/
theorem phaseInputTape_window (input : List Bool) (p : ℤ) :
    ((Turing.Tape.mk₁ (phaseInput input)).nth p).1.isSome = true ↔
      (0 ≤ p ∧ p < (input.length : ℤ)) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, p = (a : ℤ) := ⟨Int.toNat p, (Int.toNat_of_nonneg hp).symm⟩
    subst ha
    rw [phaseTape_mk₁_nth]
    by_cases han : a < input.length
    · rw [List.getI_eq_getElem (phaseInput input) (by simpa [phaseInput] using! han)]
      have hlen : a < (phaseInput input).length := by simpa [phaseInput] using! han
      have hcell : (phaseInput input)[a] = (some input[a], none, false, none) := by
        simp [phaseInput]
      rw [hcell]
      exact ⟨fun _ => ⟨hp, by exact_mod_cast han⟩, fun _ => by simp⟩
    · rw [List.getI_eq_default (phaseInput input) (by simpa [phaseInput] using! han)]
      have hdef : (default : CellCore) = (none, none, false, none) := rfl
      rw [hdef]
      refine ⟨fun h => absurd h (by simp), fun hcon => absurd (by exact_mod_cast hcon.2) han⟩
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, p = -((a : ℤ)) - 1 := by
      have hpos : (0 : ℤ) ≤ -p := by omega
      have h1 := Int.toNat_of_nonneg hpos
      exact ⟨Int.toNat (-p) - 1, by omega⟩
    subst ha
    rw [phaseTape_mk₁_nth_neg]
    have hdef : (default : CellCore) = (none, none, false, none) := rfl
    rw [hdef]
    refine ⟨fun h => absurd h (by simp), fun hcon => absurd hcon.1 (by omega)⟩

/-- Writing a symbol with the same home-marker bit preserves the home-marker invariant. -/
theorem phaseHomeAt_write_head (T : Turing.Tape CellCore) (s : CellCore) (off : ℤ)
    (h : PhaseHomeAt T off) (hs : s.2.2.1 = T.head.2.2.1) :
    PhaseHomeAt (T.write s) off := by
  intro i
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left rfl, hs]
    exact h 0
  · rw [ite_eq_right hi]
    exact h i

/-- Writing a symbol with the same input-track entry preserves the input-track invariant. -/
theorem phaseInputSame_write_head (initial T : Turing.Tape CellCore) (s : CellCore)
    (off : ℤ) (h : PhaseInputSame initial T off) (hs : s.1 = T.head.1) :
    PhaseInputSame initial (T.write s) off := by
  intro i
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · subst hi
    rw [ite_eq_left rfl, hs]
    exact h 0
  · rw [ite_eq_right hi]
    exact h i

/-- A write preserves a busy-cell envelope if every old busy cell and any new busy head cell lie
within that envelope. -/
theorem phaseEnvBusy_write (T : Turing.Tape CellCore) (s : CellCore) (off Wlo Whi : ℤ)
    (h : ∀ i : ℤ, phaseBusy (T.nth i) = true → Wlo ≤ i + off ∧ i + off ≤ Whi)
    (h0 : phaseBusy s = true → Wlo ≤ 0 + off ∧ 0 + off ≤ Whi) :
    ∀ i : ℤ, phaseBusy ((T.write s).nth i) = true → Wlo ≤ i + off ∧ i + off ≤ Whi := by
  intro i hi
  rw [Turing.Tape.write_nth] at hi
  by_cases h0i : i = 0
  · subst h0i
    rw [ite_eq_left rfl] at hi
    exact h0 hi
  · rw [ite_eq_right h0i] at hi
    exact h i hi

/-- Moving right preserves a busy-cell envelope after increasing the head offset by one. -/
theorem phaseEnvBusy_move_right (T : Turing.Tape CellCore) (off Wlo Whi : ℤ)
    (h : ∀ i : ℤ, phaseBusy (T.nth i) = true → Wlo ≤ i + off ∧ i + off ≤ Whi) :
    ∀ i : ℤ, phaseBusy ((T.move .right).nth i) = true → Wlo ≤ i + (off + 1) ∧ i + (off + 1) ≤ Whi := by
  intro i hi
  rw [phaseBusy_move_right] at hi
  obtain ⟨h1, h2⟩ := h (i + 1) hi
  exact ⟨by omega, by omega⟩

/-- Moving left preserves a busy-cell envelope after decreasing the head offset by one. -/
theorem phaseEnvBusy_move_left (T : Turing.Tape CellCore) (off Wlo Whi : ℤ)
    (h : ∀ i : ℤ, phaseBusy (T.nth i) = true → Wlo ≤ i + off ∧ i + off ≤ Whi) :
    ∀ i : ℤ, phaseBusy ((T.move .left).nth i) = true → Wlo ≤ i + (off - 1) ∧ i + (off - 1) ≤ Whi := by
  intro i hi
  rw [phaseBusy_move_left] at hi
  obtain ⟨h1, h2⟩ := h (i - 1) hi
  exact ⟨by omega, by omega⟩

/-- Every cell of the initialized phase-input tape is clean according to `phaseBusy`. -/
theorem phaseInputTape_busy (input : List Bool) (i : ℤ) :
    phaseBusy ((Turing.Tape.mk₁ (phaseInput input)).nth i) = false := by
  by_cases hi : 0 ≤ i
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = (a : ℤ) := ⟨Int.toNat i, (Int.toNat_of_nonneg hi).symm⟩
    subst ha
    rw [phaseTape_mk₁_nth]
    by_cases han : a < input.length
    · rw [List.getI_eq_getElem (phaseInput input) (by simpa [phaseInput] using! han)]
      simp [phaseBusy, phaseInput]
    · rw [List.getI_eq_default (phaseInput input) (by simpa [phaseInput] using! han)]
      rfl
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = -((a : ℤ)) - 1 := by
      have hpos : (0 : ℤ) ≤ -i := by omega
      exact ⟨Int.toNat (-i) - 1, by omega⟩
    subst ha
    rw [phaseTape_mk₁_nth_neg]
    rfl

/-- Every copy-phase configuration of the dispatch machine is live for the coin-halting
predicate. -/
theorem dispatchCopy_coinHalt {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (_c : Bool) (q : Fin 5) (T : Turing.Tape CellCore) :
    coinHalt (phaseDispatchTable M a q₀) ⟨Sum.inl q, T⟩ = false := by
  have hsome : ∀ (c' : Bool), phaseDispatchTable M a q₀ c' (Sum.inl q) T.head ≠ none := by
    intro c'
    simp only [phaseDispatchTable]
    cases liftMarkerTable (fun _ => markerCopyTable) c' q T.head <;> simp
  simp [coinHalt, hsome]

/-- Copy state `0` sets the home marker and advances to copy state `1`. -/
theorem dispatchCopy_step_zero {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (T : Turing.Tape CellCore) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 0, T⟩ =
      some ⟨Sum.inl 1, T.write (T.head.1, T.head.2.1, true, T.head.2.2.2)⟩ := by
  simp [TM0_step_apply, phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
    TM0StmtApply]

/-- At a nonblank input symbol, copy state `1` copies the input entry into the work track and
advances to state `2`. -/
theorem dispatchCopy_step_one_some {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (T : Turing.Tape CellCore) (h : T.head.1.isSome = true) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 1, T⟩ =
      some ⟨Sum.inl 2, T.write (T.head.1, T.head.1, T.head.2.2.1, T.head.2.2.2)⟩ := by
  simp [TM0_step_apply, phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
    fillCell, TM0StmtApply, h]

/-- At a blank input symbol, copy state `1` enters state `3` without changing the tape. -/
theorem dispatchCopy_step_one_none {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (T : Turing.Tape CellCore) (h : T.head.1.isSome = false) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 1, T⟩ =
      some ⟨Sum.inl 3, T⟩ := by
  have hstep : Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 1, T⟩ =
      some ⟨Sum.inl 3, T.write (T.head.1, T.head.2.1, T.head.2.2.1, T.head.2.2.2)⟩ := by
    simp [TM0_step_apply, phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
      TM0StmtApply, h]
  rw [hstep]
  rfl

/-- Copy state `2` moves right and returns to state `1`. -/
theorem dispatchCopy_step_two {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (T : Turing.Tape CellCore) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 2, T⟩ =
      some ⟨Sum.inl 1, T.move .right⟩ := by
  simp [TM0_step_apply, phaseDispatchTable, liftMarkerTable, markerCopyTable, TM0StmtApply]

/-- At home, copy state `3` enters state `4` without changing the tape. -/
theorem dispatchCopy_step_three_home {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (T : Turing.Tape CellCore) (h : T.head.2.2.1 = true) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 3, T⟩ =
      some ⟨Sum.inl 4, T⟩ := by
  have hstep : Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 3, T⟩ =
      some ⟨Sum.inl 4, T.write (T.head.1, T.head.2.1, true, T.head.2.2.2)⟩ := by
    simp [TM0_step_apply, phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
      TM0StmtApply, h]
  rw [hstep]
  have hcell : (T.head.1, T.head.2.1, true, T.head.2.2.2) = T.head := by rw [← h]
  rw [hcell, Turing.Tape.write_self]

/-- Away from home, copy state `3` continues moving left. -/
theorem dispatchCopy_step_three_away {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (c : Bool) (T : Turing.Tape CellCore) (h : T.head.2.2.1 = false) :
    Turing.TM0.step (phaseDispatchTable M a q₀ c) ⟨Sum.inl 3, T⟩ =
      some ⟨Sum.inl 3, T.move .left⟩ := by
  simp [TM0_step_apply, phaseDispatchTable, liftMarkerTable, markerCopyTable, phaseMarker,
    TM0StmtApply, h]

/-- Prefix execution after a successful live step continues with the remaining coins from the
successor configuration. -/
theorem coinPrefixCfg_cons_some {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    {M : Bool → Turing.TM0.Machine Γ Λ} {c : Bool} {cs : List Bool}
    {cfg next : Turing.TM0.Cfg Γ Λ}
    (hch : coinHalt M cfg = false) (hstep : Turing.TM0.step (M c) cfg = some next) :
    coinPrefixCfg M (c :: cs) cfg = coinPrefixCfg M cs next := by
  simp only [coinPrefixCfg, hch, Bool.false_eq_true, ↓reduceIte, hstep]

/-- The initialized phase-input tape has blank work and visitation tracks at every position. -/
theorem phaseInputTape_work (input : List Bool) (i : ℤ) :
    ((Turing.Tape.mk₁ (phaseInput input)).nth i).2.1 = none ∧
      ((Turing.Tape.mk₁ (phaseInput input)).nth i).2.2.2 = none := by
  by_cases hi : 0 ≤ i
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = (a : ℤ) := ⟨Int.toNat i, (Int.toNat_of_nonneg hi).symm⟩
    subst ha
    rw [phaseTape_mk₁_nth]
    by_cases han : a < input.length
    · rw [List.getI_eq_getElem (phaseInput input) (by simpa [phaseInput] using! han)]
      simp [phaseInput]
    · rw [List.getI_eq_default (phaseInput input) (by simpa [phaseInput] using! han)]
      exact ⟨rfl, rfl⟩
  · obtain ⟨a, ha⟩ : ∃ a : ℕ, i = -((a : ℤ)) - 1 := by
      have hpos : (0 : ℤ) ≤ -i := by omega
      exact ⟨Int.toNat (-i) - 1, by omega⟩
    subst ha
    rw [phaseTape_mk₁_nth_neg]
    exact ⟨rfl, rfl⟩

/-- The copy-phase invariant records the control phase, elapsed-step equations, input and
home-marker preservation, and confinement of busy cells to the input interval. -/
structure CopyPhaseInv {Λ : Type} [Inhabited Λ] (input : List Bool)
    (cfg : Turing.TM0.Cfg CellCore (ControlCore Λ)) (k off : ℤ) : Prop where
  inl : ∃ q : Fin 5, cfg.q = Sum.inl q
  busy : ∀ i : ℤ, phaseBusy (cfg.Tape.nth i) = true → 0 ≤ i + off ∧ i + off < (input.length : ℤ)
  q0 : cfg.q = Sum.inl 0 → k = 0 ∧ cfg.Tape = Turing.Tape.mk₁ (phaseInput input)
  anchors : cfg.q ≠ Sum.inl 0 → PhaseHomeAt cfg.Tape off ∧
    PhaseInputSame (Turing.Tape.mk₁ (phaseInput input)) cfg.Tape off ∧
    0 ≤ off ∧ off ≤ (input.length : ℤ)
  q1 : cfg.q = Sum.inl 1 → k = 1 + 2 * off
  q2 : cfg.q = Sum.inl 2 → k = 2 + 2 * off ∧ off ≤ (input.length : ℤ) - 1
  q3 : cfg.q = Sum.inl 3 → k = 2 + 2 * (input.length : ℤ) + ((input.length : ℤ) - off)
  q4 : cfg.q = Sum.inl 4 → k = 3 * (input.length : ℤ) + 3

/-- A coin prefix that stays within the copy-phase time bound preserves `CopyPhaseInv` and
increments its elapsed-step parameter by the prefix length. -/
theorem dispatchCopyPrefix {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (input : List Bool) :
    ∀ (cs : List Bool) (cfg : Turing.TM0.Cfg CellCore (ControlCore Λ)) (k off : ℤ),
      ↑cs.length + k ≤ 3 * input.length + 3 → CopyPhaseInv input cfg k off →
    ∃ (cfg' : Turing.TM0.Cfg CellCore (ControlCore Λ)) (off' : ℤ),
      coinPrefixCfg (phaseDispatchTable M a q₀) cs cfg = cfg' ∧
      CopyPhaseInv input cfg' (↑cs.length + k) off' := by
  intro cs
  induction cs with
  | nil =>
    intro cfg k off _ hinv
    refine ⟨cfg, off, rfl, ?_⟩
    have hconv : ((↑ ([] : List Bool).length : ℤ) + k) = k := by simp
    rw [hconv]
    exact hinv
  | cons c cs' ih =>
    intro cfg k off hlen hinv
    obtain ⟨q, hq⟩ := hinv.inl
    obtain ⟨qc, Tc⟩ := cfg
    have hq' : qc = Sum.inl q := hq
    subst hq'
    have hch : coinHalt (phaseDispatchTable M a q₀) ⟨Sum.inl q, Tc⟩ = false :=
      dispatchCopy_coinHalt M a q₀ c q Tc
    have hlen' : ↑cs'.length + (k + 1) ≤ 3 * input.length + 3 := by
      simp only [List.length_cons] at hlen
      push_cast at hlen ⊢
      omega
    fin_cases q
    · obtain ⟨k0, hT⟩ := hinv.q0 rfl
      subst k0
      have hstep := dispatchCopy_step_zero M a q₀ c Tc
      subst hT
      have hw1 : (Turing.Tape.mk₁ (phaseInput input)).head.2.1 = none :=
        (phaseInputTape_work input 0).1
      have hw2 : (Turing.Tape.mk₁ (phaseInput input)).head.2.2.2 = none :=
        (phaseInputTape_work input 0).2
      have hbusy1 : ∀ i : ℤ, phaseBusy
          (((Turing.Tape.mk₁ (phaseInput input)).write
            ((Turing.Tape.mk₁ (phaseInput input)).head.1,
              (Turing.Tape.mk₁ (phaseInput input)).head.2.1, true,
              (Turing.Tape.mk₁ (phaseInput input)).head.2.2.2)).nth i) = true →
            0 ≤ i + 0 ∧ i + 0 < (input.length : ℤ) := by
        intro i hi
        rw [Turing.Tape.write_nth] at hi
        by_cases h0i : i = 0
        · subst h0i
          rw [ite_eq_left rfl] at hi
          simp only [phaseBusy, hw1, hw2, Bool.or_self] at hi
          exact absurd hi (by simp)
        · rw [ite_eq_right h0i] at hi
          exact absurd hi (by rw [phaseInputTape_busy input i]; simp)
      have hhome1 : PhaseHomeAt
          ((Turing.Tape.mk₁ (phaseInput input)).write
            ((Turing.Tape.mk₁ (phaseInput input)).head.1,
              (Turing.Tape.mk₁ (phaseInput input)).head.2.1, true,
              (Turing.Tape.mk₁ (phaseInput input)).head.2.2.2)) 0 := by
        intro i
        rw [Turing.Tape.write_nth]
        by_cases hi : i = 0
        · subst hi; simp
        · rw [ite_eq_right hi, phaseInputTape_home]
          simp [hi]
      have hbase : PhaseInputSame (Turing.Tape.mk₁ (phaseInput input))
          (Turing.Tape.mk₁ (phaseInput input)) 0 := by
        intro i
        rw [add_zero]
      have hinp1 : PhaseInputSame (Turing.Tape.mk₁ (phaseInput input))
          ((Turing.Tape.mk₁ (phaseInput input)).write
            ((Turing.Tape.mk₁ (phaseInput input)).head.1,
              (Turing.Tape.mk₁ (phaseInput input)).head.2.1, true,
              (Turing.Tape.mk₁ (phaseInput input)).head.2.2.2)) 0 :=
        phaseInputSame_write_head _ _ _ 0 hbase (by rfl)
      obtain ⟨cfg'', off'', hpfx, hinv''⟩ :=
        ih ⟨Sum.inl 1, (Turing.Tape.mk₁ (phaseInput input)).write
          ((Turing.Tape.mk₁ (phaseInput input)).head.1,
            (Turing.Tape.mk₁ (phaseInput input)).head.2.1, true,
            (Turing.Tape.mk₁ (phaseInput input)).head.2.2.2)⟩ (0 + 1) 0 hlen'
          ⟨⟨1, rfl⟩, hbusy1, by simp,
            by
              intro _
              exact ⟨hhome1, hinp1, by norm_num, by exact_mod_cast Nat.zero_le _⟩,
            by
              intro _
              norm_num,
            by simp, by simp, by simp⟩
      have hp1 : coinPrefixCfg (phaseDispatchTable M a q₀) (c :: cs')
          ⟨Sum.inl (0 : Fin 5), Turing.Tape.mk₁ (phaseInput input)⟩ = cfg'' := by
        exact (coinPrefixCfg_cons_some hch hstep).trans hpfx
      have hp2 : CopyPhaseInv input cfg'' (((c :: cs').length : ℤ) + 0) off'' := by
        have hEq : ((c :: cs').length : ℤ) + 0 = ((cs'.length : ℤ)) + (0 + 1) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
        rw [hEq]
        exact hinv''
      exact ⟨cfg'', off'', hp1, hp2⟩
    · obtain ⟨hhome, hinp, hofflo, hoffhi⟩ := hinv.anchors (by simp)
      have hk1 := hinv.q1 rfl
      have hhead : Tc.head.1 = ((Turing.Tape.mk₁ (phaseInput input)).nth (0 + off)).1 := hinp 0
      rw [zero_add] at hhead
      by_cases hsome : Tc.head.1.isSome = true
      · have hwin : 0 ≤ off ∧ off < (input.length : ℤ) := by
          have := (phaseInputTape_window input off).mp (by rw [← hhead]; exact hsome)
          simpa using! this
        have hstep := dispatchCopy_step_one_some M a q₀ c Tc hsome
        have hbusyOld : ∀ i : ℤ, phaseBusy (Tc.nth i) = true →
            0 ≤ i + off ∧ i + off ≤ ((input.length : ℤ)) - 1 := by
          intro i hi
          obtain ⟨h1, h2⟩ := hinv.busy i hi
          exact ⟨h1, by omega⟩
        have hheadbusy : phaseBusy (Tc.head.1, Tc.head.1, Tc.head.2.2.1, Tc.head.2.2.2) = true →
            0 ≤ 0 + off ∧ 0 + off ≤ ((input.length : ℤ)) - 1 := by
          intro hpb
          rcases Bool.or_eq_true_iff.mp hpb with h | h
          · rw [h] at hsome
            exact ⟨by omega, by omega⟩
          · obtain ⟨h1, h2⟩ := hinv.busy 0 (by simp [phaseBusy, h])
            exact ⟨by omega, by omega⟩
        have hbusy1 : ∀ i : ℤ, phaseBusy
            ((Tc.write (Tc.head.1, Tc.head.1, Tc.head.2.2.1, Tc.head.2.2.2)).nth i) = true →
            0 ≤ i + off ∧ i + off < (input.length : ℤ) := by
          intro i hi
          obtain ⟨h1, h2⟩ := phaseEnvBusy_write Tc _ off 0 ((input.length : ℤ) - 1)
            hbusyOld hheadbusy i hi
          exact ⟨h1, by omega⟩
        obtain ⟨cfg'', off'', hpfx, hinv''⟩ :=
          ih ⟨Sum.inl 2, Tc.write (Tc.head.1, Tc.head.1, Tc.head.2.2.1, Tc.head.2.2.2)⟩
            (k + 1) off hlen'
            ⟨⟨2, rfl⟩, hbusy1, by simp,
              by
                intro _
                exact ⟨phaseHomeAt_write_head Tc _ off hhome (by rfl),
                  phaseInputSame_write_head _ _ _ off hinp (by rfl), hofflo, hoffhi⟩,
              by simp,
              by
                intro _
                refine ⟨?_, by omega⟩
                rw [hk1]
                omega,
              by simp, by simp⟩
        have hp1 : coinPrefixCfg (phaseDispatchTable M a q₀) (c :: cs')
            ⟨Sum.inl (1 : Fin 5), Tc⟩ = cfg'' := by
          exact (coinPrefixCfg_cons_some hch hstep).trans hpfx
        have hp2 : CopyPhaseInv input cfg'' (((c :: cs').length : ℤ) + k) off'' := by
          have hEq : ((c :: cs').length : ℤ) + k = ((cs'.length : ℤ)) + (k + 1) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
          rw [hEq]
          exact hinv''
        exact ⟨cfg'', off'', hp1, hp2⟩
      · have hn : Tc.head.1.isSome = false := by simpa using! hsome
        have hoff : off = (input.length : ℤ) := by
          by_contra hne
          have hwin : 0 ≤ off ∧ off < (input.length : ℤ) := by omega
          exact hsome (by rw [hhead]; exact (phaseInputTape_window input off).mpr hwin)
        have hstep := dispatchCopy_step_one_none M a q₀ c Tc hn
        obtain ⟨cfg'', off'', hpfx, hinv''⟩ :=
          ih ⟨Sum.inl 3, Tc⟩ (k + 1) off hlen'
            ⟨⟨3, rfl⟩, hinv.busy, by simp,
              by
                intro _
                exact ⟨hhome, hinp, hofflo, hoffhi⟩,
              by simp, by simp,
              by
                intro _
                rw [hk1, hoff]
                omega,
              by simp⟩
        have hp1 : coinPrefixCfg (phaseDispatchTable M a q₀) (c :: cs')
            ⟨Sum.inl (1 : Fin 5), Tc⟩ = cfg'' := by
          exact (coinPrefixCfg_cons_some hch hstep).trans hpfx
        have hp2 : CopyPhaseInv input cfg'' (((c :: cs').length : ℤ) + k) off'' := by
          have hEq : ((c :: cs').length : ℤ) + k = ((cs'.length : ℤ)) + (k + 1) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
          rw [hEq]
          exact hinv''
        exact ⟨cfg'', off'', hp1, hp2⟩
    · obtain ⟨hhome, hinp, hofflo, hoffhi⟩ := hinv.anchors (by simp)
      obtain ⟨hk2, hoffn⟩ := hinv.q2 rfl
      have hstep := dispatchCopy_step_two M a q₀ c Tc
      have hbusyOld : ∀ i : ℤ, phaseBusy (Tc.nth i) = true →
          0 ≤ i + off ∧ i + off ≤ ((input.length : ℤ)) - 1 := by
        intro i hi
        obtain ⟨h1, h2⟩ := hinv.busy i hi
        exact ⟨h1, by omega⟩
      have hbusy1 : ∀ i : ℤ, phaseBusy ((Tc.move .right).nth i) = true →
          0 ≤ i + (off + 1) ∧ i + (off + 1) < (input.length : ℤ) := by
        intro i hi
        obtain ⟨h1, h2⟩ := phaseEnvBusy_move_right Tc off 0 ((input.length : ℤ) - 1)
          hbusyOld i hi
        exact ⟨h1, by omega⟩
      obtain ⟨cfg'', off'', hpfx, hinv''⟩ :=
        ih ⟨Sum.inl 1, Tc.move .right⟩ (k + 1) (off + 1) hlen'
          ⟨⟨1, rfl⟩, hbusy1, by simp,
            by
              intro _
              exact ⟨phaseHomeAt_move_right Tc off hhome,
                phaseInputSame_move_right _ Tc off hinp, by omega, by omega⟩,
            by
              intro _
              rw [hk2]
              omega,
            by simp, by simp, by simp⟩
      have hp1 : coinPrefixCfg (phaseDispatchTable M a q₀) (c :: cs')
          ⟨Sum.inl (2 : Fin 5), Tc⟩ = cfg'' := by
        exact (coinPrefixCfg_cons_some hch hstep).trans hpfx
      have hp2 : CopyPhaseInv input cfg'' (((c :: cs').length : ℤ) + k) off'' := by
        have hEq : ((c :: cs').length : ℤ) + k = ((cs'.length : ℤ)) + (k + 1) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
        rw [hEq]
        exact hinv''
      exact ⟨cfg'', off'', hp1, hp2⟩
    · obtain ⟨hhome, hinp, hofflo, hoffhi⟩ := hinv.anchors (by simp)
      have hk3 := hinv.q3 rfl
      have hheadhome : Tc.head.2.2.1 = decide (off = 0) := phaseHomeAt_head Tc off hhome
      by_cases ho : off = 0
      · subst ho
        have hstep := dispatchCopy_step_three_home M a q₀ c Tc (by simp [hheadhome])
        obtain ⟨cfg'', off'', hpfx, hinv''⟩ :=
          ih ⟨Sum.inl 4, Tc⟩ (k + 1) 0 hlen'
            ⟨⟨4, rfl⟩, hinv.busy, by simp,
              by
                intro _
                exact ⟨hhome, hinp, hofflo, hoffhi⟩,
              by simp, by simp, by simp,
              by
                intro _
                rw [hk3]
                omega⟩
        have hp1 : coinPrefixCfg (phaseDispatchTable M a q₀) (c :: cs')
            ⟨Sum.inl (3 : Fin 5), Tc⟩ = cfg'' := by
          exact (coinPrefixCfg_cons_some hch hstep).trans hpfx
        have hp2 : CopyPhaseInv input cfg'' (((c :: cs').length : ℤ) + k) off'' := by
          have hEq : ((c :: cs').length : ℤ) + k = ((cs'.length : ℤ)) + (k + 1) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
          rw [hEq]
          exact hinv''
        exact ⟨cfg'', off'', hp1, hp2⟩
      · have hstep := dispatchCopy_step_three_away M a q₀ c Tc (by
          simp [hheadhome, ho])
        have hbusyOld : ∀ i : ℤ, phaseBusy (Tc.nth i) = true →
            0 ≤ i + off ∧ i + off ≤ ((input.length : ℤ)) - 1 := by
          intro i hi
          obtain ⟨h1, h2⟩ := hinv.busy i hi
          exact ⟨h1, by omega⟩
        have hbusy1 : ∀ i : ℤ, phaseBusy ((Tc.move .left).nth i) = true →
            0 ≤ i + (off - 1) ∧ i + (off - 1) < (input.length : ℤ) := by
          intro i hi
          obtain ⟨h1, h2⟩ := phaseEnvBusy_move_left Tc off 0 ((input.length : ℤ) - 1)
            hbusyOld i hi
          exact ⟨h1, by omega⟩
        obtain ⟨cfg'', off'', hpfx, hinv''⟩ :=
          ih ⟨Sum.inl 3, Tc.move .left⟩ (k + 1) (off - 1) hlen'
            ⟨⟨3, rfl⟩, hbusy1, by simp,
              by
                intro _
                exact ⟨phaseHomeAt_move_left Tc off hhome,
                  phaseInputSame_move_left _ Tc off hinp, by omega, by omega⟩,
              by simp, by simp,
              by
                intro _
                rw [hk3]
                omega,
              by simp⟩
        have hp1 : coinPrefixCfg (phaseDispatchTable M a q₀) (c :: cs')
            ⟨Sum.inl (3 : Fin 5), Tc⟩ = cfg'' := by
          exact (coinPrefixCfg_cons_some hch hstep).trans hpfx
        have hp2 : CopyPhaseInv input cfg'' (((c :: cs').length : ℤ) + k) off'' := by
          have hEq : ((c :: cs').length : ℤ) + k = ((cs'.length : ℤ)) + (k + 1) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
          rw [hEq]
          exact hinv''
        exact ⟨cfg'', off'', hp1, hp2⟩
    · have h4 := hinv.q4 rfl
      simp only [List.length_cons] at hlen
      push_cast at hlen
      omega

/-- During any prefix of the copy phase, busy cells remain in the input interval. After a
nonempty prefix, the home and input invariants hold and the head offset lies between zero
and the input length. -/
theorem dispatchCopyPrefixEnv {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (q₀ : Λ)
    (input : List Bool) (cs : List Bool) (hle : cs.length ≤ 3 * input.length + 3) :
    ∃ (cfg : Turing.TM0.Cfg CellCore (ControlCore Λ)) (off : ℤ),
      coinPrefixCfg (phaseDispatchTable M a q₀) cs
          ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ = cfg ∧
      (∀ i : ℤ, phaseBusy (cfg.Tape.nth i) = true →
        0 ≤ i + off ∧ i + off < (input.length : ℤ)) ∧
      (cs ≠ [] → PhaseHomeAt cfg.Tape off ∧
        PhaseInputSame (Turing.Tape.mk₁ (phaseInput input)) cfg.Tape off ∧
        0 ≤ off ∧ off ≤ (input.length : ℤ)) := by
  obtain ⟨cfg', off', hpfx, hinv⟩ :=
    dispatchCopyPrefix M a q₀ input cs ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ 0 0
      (by exact_mod_cast hle)
      ⟨⟨default, rfl⟩,
        by
          intro i hi
          rw [phaseInputTape_busy input i] at hi
          simp at hi,
        by
          intro _
          exact ⟨rfl, rfl⟩,
        by
          intro h
          exact absurd h (by simp),
        by
          intro h
          exact absurd (Sum.inl.inj h) (by decide),
        by
          intro h
          exact absurd (Sum.inl.inj h) (by decide),
        by
          intro h
          exact absurd (Sum.inl.inj h) (by decide),
        by
          intro h
          exact absurd (Sum.inl.inj h) (by decide)⟩
  refine ⟨cfg', off', hpfx, hinv.busy, ?_⟩
  intro hcs
  have hq0 : cfg'.q ≠ Sum.inl 0 := by
    intro h
    obtain ⟨hcount, _⟩ := hinv.q0 h
    cases cs with
    | nil => exact hcs rfl
    | cons c cs'' =>
        simp only [List.length_cons] at hcount
        push_cast at hcount
        omega
  exact hinv.anchors hq0

/-- The tape component of a successful Turing-machine step is either a head write or a single
tape movement. -/
theorem tm0_step_tape_cases {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) {cfg next : Turing.TM0.Cfg Γ Λ}
    (h : Turing.TM0.step M cfg = some next) :
    (∃ s : Γ, next.Tape = cfg.Tape.write s) ∨
    (∃ d : Turing.Dir, next.Tape = cfg.Tape.move d) := by
  obtain ⟨qn, Tn⟩ := next
  rw [TM0_step_apply, Option.map_eq_some_iff] at h
  obtain ⟨⟨q', stmt⟩, -, hap⟩ := h
  cases stmt with
  | move d =>
      have h2 : (⟨q', cfg.Tape.move d⟩ : Turing.TM0.Cfg _ _) = ⟨qn, Tn⟩ := hap
      injection h2 with _ hT
      exact Or.inr ⟨d, hT.symm⟩
  | write s =>
      have h2 : (⟨q', cfg.Tape.write s⟩ : Turing.TM0.Cfg _ _) = ⟨qn, Tn⟩ := hap
      injection h2 with _ hT
      exact Or.inl ⟨s, hT.symm⟩

/-- Executing a coin prefix enlarges an initial envelope for the head and busy cells by at most
the prefix length on each side. -/
theorem coinPrefixEnvelope {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine CellCore Λ) :
    ∀ (cs : List Bool) (cfg : Turing.TM0.Cfg CellCore Λ) (off Wlo Whi k : ℤ),
      Wlo - k ≤ off ∧ off ≤ Whi + k →
      (∀ i : ℤ, phaseBusy (cfg.Tape.nth i) = true → Wlo - k ≤ i + off ∧ i + off ≤ Whi + k) →
      ∃ (cfg' : Turing.TM0.Cfg CellCore Λ) (off' : ℤ),
        coinPrefixCfg M cs cfg = cfg' ∧
        Wlo - (k + (cs.length : ℤ)) ≤ off' ∧ off' ≤ Whi + (k + (cs.length : ℤ)) ∧
        (∀ i : ℤ, phaseBusy (cfg'.Tape.nth i) = true →
          Wlo - (k + (cs.length : ℤ)) ≤ i + off' ∧ i + off' ≤ Whi + (k + (cs.length : ℤ))) := by
  intro cs
  induction cs with
  | nil =>
      intro cfg off Wlo Whi k hoff hbusy
      simp only [List.length_nil, Nat.cast_zero, add_zero]
      exact ⟨cfg, off, rfl, hoff.1, hoff.2, hbusy⟩
  | cons c cs' ih =>
      intro cfg off Wlo Whi k hoff hbusy
      have hlen : ((c :: cs').length : ℤ) = (cs'.length : ℤ) + 1 := by simp
      have hk1 : k + ((c :: cs').length : ℤ) = (k + 1) + (cs'.length : ℤ) := by
        rw [hlen]
        ring
      by_cases hh : coinHalt M cfg = true
      · refine ⟨cfg, off, ?_, ?_, ?_, ?_⟩
        · simp only [coinPrefixCfg, hh, ite_true]
        · omega
        · omega
        · intro i hi
          obtain ⟨h1, h2⟩ := hbusy i hi
          omega
      · have hch : coinHalt M cfg = false := by
          cases hc : coinHalt M cfg with
          | false => rfl
          | true => exact absurd hc hh
        simp only [coinPrefixCfg, hch, Bool.false_eq_true, ↓reduceIte]
        cases hs : Turing.TM0.step (M c) cfg with
        | none =>
            refine ⟨cfg, off, rfl, ?_, ?_, ?_⟩
            · omega
            · omega
            · intro i hi
              obtain ⟨h1, h2⟩ := hbusy i hi
              omega
        | some next =>
            rcases tm0_step_tape_cases _ hs with ⟨s, hsT⟩ | ⟨d, hsT⟩
            · have hoffk : Wlo - (k + 1) ≤ off ∧ off ≤ Whi + (k + 1) := by omega
              have hbusyOld : ∀ i : ℤ, phaseBusy (cfg.Tape.nth i) = true →
                  Wlo - (k + 1) ≤ i + off ∧ i + off ≤ Whi + (k + 1) := by
                intro i hi
                obtain ⟨h1, h2⟩ := hbusy i hi
                exact ⟨by omega, by omega⟩
              have hbusy' : ∀ i : ℤ, phaseBusy (next.Tape.nth i) = true →
                  Wlo - (k + 1) ≤ i + off ∧ i + off ≤ Whi + (k + 1) := by
                rw [hsT]
                exact phaseEnvBusy_write cfg.Tape s off (Wlo - (k + 1)) (Whi + (k + 1))
                  hbusyOld (fun _ => ⟨by omega, by omega⟩)
              obtain ⟨cfg', off', hpfx, hlo1, hhi1, hbusy''⟩ :=
                ih next off Wlo Whi (k + 1) hoffk hbusy'
              refine ⟨cfg', off', hpfx, ?_, ?_, ?_⟩
              · rw [hk1]; exact hlo1
              · rw [hk1]; exact hhi1
              · intro i hi
                obtain ⟨hb1, hb2⟩ := hbusy'' i hi
                omega
            · have hoffk : Wlo - (k + 1) ≤ off ∧ off ≤ Whi + (k + 1) := by omega
              have hbusyOld : ∀ i : ℤ, phaseBusy (cfg.Tape.nth i) = true →
                  Wlo - (k + 1) ≤ i + off ∧ i + off ≤ Whi + (k + 1) := by
                intro i hi
                obtain ⟨h1, h2⟩ := hbusy i hi
                exact ⟨by omega, by omega⟩
              cases d with
              | left =>
                  have hoff' : Wlo - (k + 1) ≤ off - 1 ∧ off - 1 ≤ Whi + (k + 1) := by omega
                  have hbusy' : ∀ i : ℤ, phaseBusy (next.Tape.nth i) = true →
                      Wlo - (k + 1) ≤ i + (off - 1) ∧ i + (off - 1) ≤ Whi + (k + 1) := by
                    rw [hsT]
                    exact phaseEnvBusy_move_left cfg.Tape off (Wlo - (k + 1)) (Whi + (k + 1))
                      hbusyOld
                  obtain ⟨cfg', off'', hpfx, hlo1, hhi1, hbusy''⟩ :=
                    ih next (off - 1) Wlo Whi (k + 1) hoff' hbusy'
                  refine ⟨cfg', off'', hpfx, ?_, ?_, ?_⟩
                  · rw [hk1]; exact hlo1
                  · rw [hk1]; exact hhi1
                  · intro i hi
                    obtain ⟨hb1, hb2⟩ := hbusy'' i hi
                    omega
              | right =>
                  have hoff' : Wlo - (k + 1) ≤ off + 1 ∧ off + 1 ≤ Whi + (k + 1) := by omega
                  have hbusy' : ∀ i : ℤ, phaseBusy (next.Tape.nth i) = true →
                      Wlo - (k + 1) ≤ i + (off + 1) ∧ i + (off + 1) ≤ Whi + (k + 1) := by
                    rw [hsT]
                    exact phaseEnvBusy_move_right cfg.Tape off (Wlo - (k + 1)) (Whi + (k + 1))
                      hbusyOld
                  obtain ⟨cfg', off'', hpfx, hlo1, hhi1, hbusy''⟩ :=
                    ih next (off + 1) Wlo Whi (k + 1) hoff' hbusy'
                  refine ⟨cfg', off'', hpfx, ?_, ?_, ?_⟩
                  · rw [hk1]; exact hlo1
                  · rw [hk1]; exact hhi1
                  · intro i hi
                    obtain ⟨hb1, hb2⟩ := hbusy'' i hi
                    omega

/-- From a clean phase-input tape, prefix execution confines the head and all busy cells to
absolute offsets between minus and plus the prefix length. -/
theorem coinPrefixWorkspace {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine CellCore (ControlCore Λ))
    (input : List Bool) (cs : List Bool) :
    ∃ (cfg : Turing.TM0.Cfg CellCore (ControlCore Λ)) (off : ℤ),
      coinPrefixCfg M cs ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ = cfg ∧
      -(cs.length : ℤ) ≤ off ∧ off ≤ (cs.length : ℤ) ∧
      (∀ i : ℤ, phaseBusy (cfg.Tape.nth i) = true →
        -(cs.length : ℤ) ≤ i + off ∧ i + off ≤ (cs.length : ℤ)) := by
  obtain ⟨cfg, off, hp, h1, h2, hbusy⟩ :=
    coinPrefixEnvelope M cs ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ 0 0 0 0
      ⟨by norm_num, by norm_num⟩
      (by
        intro i hi
        rw [phaseInputTape_busy input i] at hi
        simp at hi)
  refine ⟨cfg, off, hp, by simpa using! h1, by simpa using! h2, by simpa using! hbusy⟩

/-- A prefix of `bs ++ cs` whose length is at least that of `bs` equals `bs` followed by its own
suffix after `bs`. -/
theorem list_prefix_extend {α : Type*} {as bs cs : List α}
    (h : as <+: bs ++ cs) (hle : bs.length ≤ as.length) :
    as = bs ++ as.drop bs.length := by
  obtain ⟨t, ht⟩ := h
  have hL : (as ++ t).take bs.length = as.take bs.length := by
    rw [List.take_append, Nat.sub_eq_zero_of_le hle, List.take_zero, List.append_nil]
  have hR : (bs ++ cs).take bs.length = bs := List.take_left
  have h1 : as.take bs.length = bs :=
    calc as.take bs.length = (as ++ t).take bs.length := hL.symm
      _ = (bs ++ cs).take bs.length := by rw [ht]
      _ = bs := hR
  calc as = as.take bs.length ++ as.drop bs.length :=
        (List.take_append_drop bs.length as).symm
    _ = bs ++ as.drop bs.length := by rw [h1]

/-- Embedding the initial structured copy configuration gives the initialized compiled
configuration on the same tape list. -/
theorem phase1EmbedCfg_init (Q : ℕ) (l : List CellCore) :
    phase1EmbedCfg Q ⟨Sum.inl default, Turing.Tape.mk₁ l⟩ = Turing.TM0.init l := by
  rfl

/-- Prefix execution in the compiled machine commutes with embedding structured phase-dispatch
configurations. -/
theorem tmCompile_coinPrefixCfg (code : Code) :
    ∀ (cs : List Bool)
      (cfg : Turing.TM0.Cfg CellCore (ControlCore (Fin (controlSize code + 1)))),
      coinPrefixCfg (phase1Table (tmCopyRunResetCompile code)) cs
          (phase1EmbedCfg (controlSize code) cfg)
        = phase1EmbedCfg (controlSize code)
            (coinPrefixCfg (phaseDispatchTable (table code) (readout code) default) cs cfg) := by
  intro cs
  induction cs with
  | nil => intro cfg; rfl
  | cons c cs' ih =>
      intro cfg
      simp only [coinPrefixCfg]
      rw [tmCompile_coinHalt code cfg]
      by_cases hh :
        coinHalt (phaseDispatchTable (table code) (readout code) default) cfg = true
      · simp only [hh, ite_true]
      · have hch :
          coinHalt (phaseDispatchTable (table code) (readout code) default) cfg = false := by
          cases hc :
            coinHalt (phaseDispatchTable (table code) (readout code) default) cfg with
          | false => rfl
          | true => exact absurd hc hh
        simp only [hch, Bool.false_eq_true, ↓reduceIte]
        rw [tmCompile_step code c cfg]
        cases hs :
          Turing.TM0.step (phaseDispatchTable (table code) (readout code) default c) cfg with
        | none => rfl
        | some next =>
            simp only [Option.map_some]
            exact ih next

/-- For every prefix of a compiled execution associated with a fully consumed halting source
word, a head offset and all busy absolute positions lie between minus and plus
`tmCopyRunResetCoinBudget input.length w.length`. -/
theorem tmCopyRunResetCompile_workspace_bound (code : Code) (hc : commonHalt code)
    (input : List Bool) (w fs : List Bool)
    (final : Turing.TM0.Cfg (Option Bool) (Fin (controlSize code + 1)))
    (hstop : (coinConfigRunAux (table code) w
        ⟨default, (phaseCopyResult input).map phaseWorkMap⟩).stopped = some final)
    (hread : (coinConfigRunAux (table code) w
        ⟨default, (phaseCopyResult input).map phaseWorkMap⟩).reads = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (off' lo' hi' : ℤ),
    ∀ (jcopy jhome jreset tail : List Bool) (c₁ c₂ c₃ x : Bool),
      jcopy.length = 3 * input.length + 3 →
      jhome.length = (if sf then (-off').toNat else off'.toNat) →
      jreset.length = 3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5 →
      ∀ (p : List Bool),
        p <+: (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))) ++ tail →
      ∃ off : ℤ,
        (-(tmCopyRunResetCoinBudget input.length w.length : ℤ) ≤ off ∧
          off ≤ (tmCopyRunResetCoinBudget input.length w.length : ℤ)) ∧
        ∀ i : ℤ,
          phaseBusy ((coinPrefixCfg (phase1Table (tmCopyRunResetCompile code)) p
            (Turing.TM0.init (phaseInput input))).Tape.nth i) = true →
          -(tmCopyRunResetCoinBudget input.length w.length : ℤ) ≤ i + off ∧
            i + off ≤ (tmCopyRunResetCoinBudget input.length w.length : ℤ) := by
  obtain ⟨sf, Tf, T'', off', lo', hi', hprop, hrun⟩ :=
    phaseDispatchRunReset (table code) (readout code) hc default input w fs final hstop hread hfs
  obtain ⟨_, _, hcleanS, _, _, hoffLo, hoffHi, hlo, hhi, hhiHi, hloLo⟩ := hprop
  have hOff : (if sf then (-off').toNat else off'.toNat) ≤ w.length := by
    cases sf with
    | false => exact Int.toNat_le.2 (by omega)
    | true => exact Int.toNat_le.2 (by omega)
  have hMax : (max hi' ((input.length : ℤ) - 1)).toNat ≤ 2 * w.length + 1 + input.length := by
    apply Int.toNat_le.2
    apply max_le <;> omega
  have hLo : (-lo').toNat ≤ 2 * w.length := Int.toNat_le.2 (by omega)
  have hbudN : tmCopyRunResetCoinBudget input.length w.length
      = 6 * input.length + 15 * w.length + 16 := rfl
  refine ⟨sf, off', lo', hi', ?_⟩
  intro jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset p hpfx
  have hsegsLen :
      (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))).length
        = (3 * input.length + 3) + 1 + (2 * w.length + 1) + 1
            + (if sf then (-off').toNat else off'.toNat) + 1
            + (3 * (max hi' ((input.length : ℤ) - 1)).toNat + 3 * (-lo').toNat + 5) := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      pairCoins_length w fs hfs, hjcopy, hjhome, hjreset]
    omega
  have hLBud :
      (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))).length
        ≤ tmCopyRunResetCoinBudget input.length w.length := by
    rw [hbudN]
    omega
  obtain ⟨-, -, hchain, hcoinHalt⟩ :=
    hrun jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset
  have hpre :
      coinPrefixCfg (phase1Table (tmCopyRunResetCompile code)) p
          (Turing.TM0.init (phaseInput input))
        = phase1EmbedCfg (controlSize code)
            (coinPrefixCfg (phaseDispatchTable (table code) (readout code) default) p
              ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩) := by
    have hcore := tmCompile_coinPrefixCfg code p
      ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩
    rw [phase1EmbedCfg_init (controlSize code) (phaseInput input)] at hcore
    exact hcore
  by_cases hple :
    p.length ≤
      (jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset))).length
  · obtain ⟨cfgD, off, hpD, hoff1, hoff2, hbusyD⟩ :=
      coinPrefixWorkspace (phaseDispatchTable (table code) (readout code) default) input p
    refine ⟨off, by omega, ?_⟩
    intro i hi
    have hTi :
        (coinPrefixCfg (phase1Table (tmCopyRunResetCompile code)) p
          (Turing.TM0.init (phaseInput input))).Tape.nth i = cfgD.Tape.nth i := by
      rw [hpre, hpD]
      rfl
    rw [hTi] at hi
    have hb := hbusyD i hi
    omega
  · have hp := list_prefix_extend hpfx (by omega)
    have hpreD :
        coinPrefixCfg (phaseDispatchTable (table code) (readout code) default) p
            ⟨Sum.inl default, Turing.Tape.mk₁ (phaseInput input)⟩ =
          ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR, readout code final.q))), T''⟩ := by
      rw [hp, coinPrefixCfg_append _ (phaseDispatch_commonHalt (table code) (readout code) default),
        coinPrefixCfg_of_trace _ _ _ _ hchain, coinPrefixCfg_halted _ hcoinHalt]
    refine ⟨0, by omega, ?_⟩
    intro i hi
    have hTi :
        (coinPrefixCfg (phase1Table (tmCopyRunResetCompile code)) p
          (Turing.TM0.init (phaseInput input))).Tape.nth i = T''.nth i := by
      rw [hpre, hpreD]
      rfl
    rw [hTi] at hi
    rw [hcleanS i] at hi
    exact absurd hi (by simp)

/-- The compiled control bound is a primitive recursive function of the source code. -/
theorem primrec_phase1Bound : Primrec (fun code : Code => phase1Bound (controlSize code)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) primrec_controlSize)
    (Primrec.const 30)

/-- The numeric readout is primitive recursive jointly in the source code and control label. -/
theorem primrec_phase1ReadoutNat :
    Primrec₂ (fun (code : Code) (l : ℕ) => phase1ReadoutNat code l) := by
  change Primrec (fun p : Code × ℕ => phase1ReadoutNat p.1 p.2)
  have hQ : Primrec (fun p : Code × ℕ => controlSize p.1) := primrec_controlSize.comp Primrec.fst
  have ht : Primrec (fun p : Code × ℕ => 5 + 10 * (controlSize p.1 + 1) + 4) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 10)
        (Primrec.nat_add.comp hQ (Primrec.const 1)))) (Primrec.const 4)
  have hsub : Primrec (fun p : Code × ℕ => p.2 - (5 + 10 * (controlSize p.1 + 1) + 4)) :=
    Primrec.nat_sub.comp Primrec.snd ht
  have hbody : Primrec (fun p : Code × ℕ =>
      decide ((p.2 - (5 + 10 * (controlSize p.1 + 1) + 4)) % 2 = 1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp hsub (Primrec.const 2)) (Primrec.const 1)).decide
  exact Primrec.ite (Primrec.nat_le.comp ht Primrec.snd) hbody (Primrec.const false)

/-- The numeric copy-phase row generator is primitive recursive in its label and cell index. -/
theorem primrec_phase1CopyRowNat : Primrec (fun p : ℕ × ℕ => phase1CopyRowNat p.1 p.2) := by
  have hl : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hd18 : Primrec (fun p : ℕ × ℕ => p.2 / 18) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 18)
  have hm63 : Primrec (fun p : ℕ × ℕ => p.2 / 6 % 3) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 6)) (Primrec.const 3)
  have hm32 : Primrec (fun p : ℕ × ℕ => p.2 / 3 % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 3)) (Primrec.const 2)
  have hm3 : Primrec (fun p : ℕ × ℕ => p.2 % 3) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 3)
  have h2s : Primrec (fun p : ℕ × ℕ => 2 + p.2) :=
    Primrec.nat_add.comp (Primrec.const 2) Primrec.snd
  have hcar : Primrec (fun p : ℕ × ℕ =>
      2 + 18 * (p.2 / 18) + 6 * (p.2 / 6 % 3) + 3 + p.2 % 3) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 18) hd18))
      (Primrec.nat_mul.comp (Primrec.const 6) hm63)) (Primrec.const 3)) hm3
  have hcar1b : Primrec (fun p : ℕ × ℕ =>
      2 + 18 * (p.2 / 18) + 6 * (p.2 / 18) + 3 * (p.2 / 3 % 2) + p.2 % 3) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 18) hd18))
      (Primrec.nat_mul.comp (Primrec.const 6) hd18))
      (Primrec.nat_mul.comp (Primrec.const 3) hm32)) hm3
  have hr0 : Primrec (fun p : ℕ × ℕ =>
      56 * 1 + (2 + 18 * (p.2 / 18) + 6 * (p.2 / 6 % 3) + 3 + p.2 % 3) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) (Primrec.const 1)) hcar) (Primrec.const 1)
  have hr1a : Primrec (fun p : ℕ × ℕ => 56 * 3 + (2 + p.2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) (Primrec.const 3)) h2s) (Primrec.const 1)
  have hr1b : Primrec (fun p : ℕ × ℕ =>
      56 * 2 + (2 + 18 * (p.2 / 18) + 6 * (p.2 / 18) + 3 * (p.2 / 3 % 2) + p.2 % 3) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) (Primrec.const 2)) hcar1b) (Primrec.const 1)
  have hr1 : Primrec (fun p : ℕ × ℕ =>
      if p.2 / 18 = 0 then 56 * 3 + (2 + p.2) + 1
      else 56 * 2 + (2 + 18 * (p.2 / 18) + 6 * (p.2 / 18) + 3 * (p.2 / 3 % 2) + p.2 % 3) + 1) :=
    Primrec.ite (Primrec.eq.comp hd18 (Primrec.const 0)) hr1a hr1b
  have hr3a : Primrec (fun p : ℕ × ℕ => 56 * 4 + (2 + p.2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) (Primrec.const 4)) h2s) (Primrec.const 1)
  have hr3 : Primrec (fun p : ℕ × ℕ =>
      if p.2 / 3 % 2 = 1 then 56 * 4 + (2 + p.2) + 1 else 169) :=
    Primrec.ite (Primrec.eq.comp hm32 (Primrec.const 1)) hr3a (Primrec.const 169)
  have hr4 : Primrec (fun p : ℕ × ℕ => 56 * 5 + (2 + p.2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) (Primrec.const 5)) h2s) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) hr0
    (Primrec.ite (Primrec.eq.comp hl (Primrec.const 1)) hr1
      (Primrec.ite (Primrec.eq.comp hl (Primrec.const 2)) (Primrec.const 58)
        (Primrec.ite (Primrec.eq.comp hl (Primrec.const 3)) hr3 hr4)))

/-- The numeric pending-state row generator is primitive recursive in its control bound, label,
and cell index. -/
theorem primrec_phase1PendingRowNat :
    Primrec (fun p : ℕ × ℕ × ℕ => phase1PendingRowNat p.1 p.2.1 p.2.2) := by
  have hQ : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hl : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hbase : Primrec (fun p : ℕ × ℕ × ℕ => 5 + 2 * (p.1 + 1)) :=
    Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hQ (Primrec.const 1)))
  have hsub : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1 - (5 + 2 * (p.1 + 1))) :=
    Primrec.nat_sub.comp hl hbase
  have hq : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 2 * (p.1 + 1))) / 6) :=
    Primrec.nat_div.comp hsub (Primrec.const 6)
  have hbD : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 2 * (p.1 + 1))) / 3 % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hsub (Primrec.const 3)) (Primrec.const 2)
  have hdIdx : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 2 * (p.1 + 1))) % 3) :=
    Primrec.nat_mod.comp hsub (Primrec.const 3)
  have hL : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 2 * ((p.2.1 - (5 + 2 * (p.1 + 1))) / 6) + (p.2.1 - (5 + 2 * (p.1 + 1))) / 3 % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 2) hq)) hbD
  have h56L : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 2 * ((p.2.1 - (5 + 2 * (p.1 + 1))) / 6)
        + (p.2.1 - (5 + 2 * (p.1 + 1))) / 3 % 2)) :=
    Primrec.nat_mul.comp (Primrec.const 56) hL
  have hb0 : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 2 * ((p.2.1 - (5 + 2 * (p.1 + 1))) / 6)
        + (p.2.1 - (5 + 2 * (p.1 + 1))) / 3 % 2) + (2 + p.2.2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp h56L
      (Primrec.nat_add.comp (Primrec.const 2) hs)) (Primrec.const 1)
  have hb1 : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 2 * ((p.2.1 - (5 + 2 * (p.1 + 1))) / 6)
        + (p.2.1 - (5 + 2 * (p.1 + 1))) / 3 % 2) + 0 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp h56L (Primrec.const 0)) (Primrec.const 1)
  have hb2 : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 2 * ((p.2.1 - (5 + 2 * (p.1 + 1))) / 6)
        + (p.2.1 - (5 + 2 * (p.1 + 1))) / 3 % 2) + 1 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp h56L (Primrec.const 1)) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp hdIdx (Primrec.const 0)) hb0
    (Primrec.ite (Primrec.eq.comp hdIdx (Primrec.const 1)) hb1 hb2)

/-- The numeric final marked-run row generator is primitive recursive in its source code, label,
and cell index. -/
theorem primrec_phase1MarkHaltRowNat :
    Primrec (fun p : (Code × ℕ) × ℕ => phase1MarkHaltRowNat p.1.1 p.1.2 p.2) := by
  have hcode : Primrec (fun p : (Code × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hl : Primrec (fun p : (Code × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun p : (Code × ℕ) × ℕ => p.2) := Primrec.snd
  have hQ : Primrec (fun p : (Code × ℕ) × ℕ => controlSize p.1.1) :=
    primrec_controlSize.comp hcode
  have hbase : Primrec (fun p : (Code × ℕ) × ℕ => 5 + 8 * (controlSize p.1.1 + 1)) :=
    Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 8)
        (Primrec.nat_add.comp hQ (Primrec.const 1)))
  have hsub : Primrec (fun p : (Code × ℕ) × ℕ => p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) :=
    Primrec.nat_sub.comp hl hbase
  have hsfD : Primrec (fun p : (Code × ℕ) × ℕ =>
      (p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) % 2) :=
    Primrec.nat_mod.comp hsub (Primrec.const 2)
  have hget : Primrec (fun p : (Code × ℕ) × ℕ =>
      p.1.1.getD (1 + (p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) / 2) 0) :=
    (Primrec.list_getD (0 : ℕ)).comp hcode
      (Primrec.nat_add.comp (Primrec.const 1)
        (Primrec.nat_div.comp hsub (Primrec.const 2)))
  have hmod : Primrec (fun p : (Code × ℕ) × ℕ =>
      p.1.1.getD (1 + (p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) / 2) 0 % 2) :=
    Primrec.nat_mod.comp hget (Primrec.const 2)
  have hlatch : Primrec (fun p : (Code × ℕ) × ℕ =>
      if p.1.1.getD (1 + (p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) / 2) 0 % 2 = 1
      then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp hmod (Primrec.const 1)) (Primrec.const 1) (Primrec.const 0)
  have hL : Primrec (fun p : (Code × ℕ) × ℕ =>
      5 + 10 * (controlSize p.1.1 + 1) + 2 * ((p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) % 2)
        + (if p.1.1.getD (1 + (p.1.2 - (5 + 8 * (controlSize p.1.1 + 1))) / 2) 0 % 2 = 1
          then 1 else 0)) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 10)
        (Primrec.nat_add.comp hQ (Primrec.const 1))))
      (Primrec.nat_mul.comp (Primrec.const 2) hsfD)) hlatch
  exact Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 56) hL)
    (Primrec.nat_add.comp (Primrec.const 2) hs)) (Primrec.const 1)

/-- The numeric homing row generator is primitive recursive in its control bound, label, and
cell index. -/
theorem primrec_phase1HomeRowNat :
    Primrec (fun p : ℕ × ℕ × ℕ => phase1HomeRowNat p.1 p.2.1 p.2.2) := by
  have hQ : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hl : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hbase : Primrec (fun p : ℕ × ℕ × ℕ => 5 + 10 * (p.1 + 1)) :=
    Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 10) (Primrec.nat_add.comp hQ (Primrec.const 1)))
  have hsub : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1 - (5 + 10 * (p.1 + 1))) :=
    Primrec.nat_sub.comp hl hbase
  have hleft : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 10 * (p.1 + 1))) / 2) :=
    Primrec.nat_div.comp hsub (Primrec.const 2)
  have hbit : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 10 * (p.1 + 1))) % 2) :=
    Primrec.nat_mod.comp hsub (Primrec.const 2)
  have hm32 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 / 3 % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const 3)) (Primrec.const 2)
  have hLt : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + (p.2.1 - (5 + 10 * (p.1 + 1))) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 5)
        (Primrec.nat_mul.comp (Primrec.const 10) (Primrec.nat_add.comp hQ (Primrec.const 1))))
      (Primrec.const 4)) hbit
  have hbt : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + (p.2.1 - (5 + 10 * (p.1 + 1))) % 2) + (2 + p.2.2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hLt)
      (Primrec.nat_add.comp (Primrec.const 2) hs)) (Primrec.const 1)
  have h56l : Primrec (fun p : ℕ × ℕ × ℕ => 56 * p.2.1) :=
    Primrec.nat_mul.comp (Primrec.const 56) hl
  have hbl : Primrec (fun p : ℕ × ℕ × ℕ => 56 * p.2.1 + 1 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp h56l (Primrec.const 1)) (Primrec.const 1)
  have hbr : Primrec (fun p : ℕ × ℕ × ℕ => 56 * p.2.1 + 0 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp h56l (Primrec.const 0)) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp hm32 (Primrec.const 1)) hbt
    (Primrec.ite (Primrec.eq.comp hleft (Primrec.const 1)) hbl hbr)

/-- The numeric reset row generator is primitive recursive in its control bound, label, and cell
index. -/
theorem primrec_phase1ResetRowNat :
    Primrec (fun p : ℕ × ℕ × ℕ => phase1ResetRowNat p.1 p.2.1 p.2.2) := by
  have hQ : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hl : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hQ1 : Primrec (fun p : ℕ × ℕ × ℕ => p.1 + 1) :=
    Primrec.nat_add.comp hQ (Primrec.const 1)
  have hbase : Primrec (fun p : ℕ × ℕ × ℕ => 5 + 10 * (p.1 + 1) + 4) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 10) hQ1)) (Primrec.const 4)
  have hsub : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1 - (5 + 10 * (p.1 + 1) + 4)) :=
    Primrec.nat_sub.comp hl hbase
  have hph : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) / 2) :=
    Primrec.nat_div.comp hsub (Primrec.const 2)
  have hbD : Primrec (fun p : ℕ × ℕ × ℕ => (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_mod.comp hsub (Primrec.const 2)
  have hd18 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 / 18) :=
    Primrec.nat_div.comp hs (Primrec.const 18)
  have hd6 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 / 6) :=
    Primrec.nat_div.comp hs (Primrec.const 6)
  have hd3 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 / 3) :=
    Primrec.nat_div.comp hs (Primrec.const 3)
  have hm63 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 / 6 % 3) :=
    Primrec.nat_mod.comp hd6 (Primrec.const 3)
  have hm32 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 / 3 % 2) :=
    Primrec.nat_mod.comp hd3 (Primrec.const 2)
  have hm3 : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2 % 3) :=
    Primrec.nat_mod.comp hs (Primrec.const 3)
  have hbusy : PrimrecPred (fun p : ℕ × ℕ × ℕ =>
      (decide (p.2.2 / 6 % 3 ≠ 0) || decide (p.2.2 % 3 ≠ 0)) = true) :=
    Primrec.eq.comp
      (Primrec.or.comp
        (PrimrecPred.not (Primrec.eq.comp hm63 (Primrec.const 0))).decide
        (PrimrecPred.not (Primrec.eq.comp hm3 (Primrec.const 0))).decide)
      (Primrec.const true)
  have herase : Primrec (fun p : ℕ × ℕ × ℕ =>
      2 + 18 * (p.2.2 / 18) + 3 * (p.2.2 / 3 % 2)) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.const 18) hd18))
      (Primrec.nat_mul.comp (Primrec.const 3) hm32)
  have hL8 : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + 8 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hbase (Primrec.const 8)) hbD
  have hL2 : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + 2 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hbase (Primrec.const 2)) hbD
  have hL4 : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + 4 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hbase (Primrec.const 4)) hbD
  have hL6 : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + 6 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hbase (Primrec.const 6)) hbD
  have hL0 : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + 0 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hbase (Primrec.const 0)) hbD
  have hL10 : Primrec (fun p : ℕ × ℕ × ℕ =>
      5 + 10 * (p.1 + 1) + 4 + 10 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hbase (Primrec.const 10)) hbD
  have hb0t : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + 8 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2)
        + (2 + 18 * (p.2.2 / 18) + 3 * (p.2.2 / 3 % 2)) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL8) herase) (Primrec.const 1)
  have hb0f : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + 2 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) + 0 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL2) (Primrec.const 0)) (Primrec.const 1)
  have hb1t : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + 4 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) + 0 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL4) (Primrec.const 0)) (Primrec.const 1)
  have hb2t : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + 10 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2)
        + (2 + 18 * (p.2.2 / 18) + 3 * (p.2.2 / 3 % 2)) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL10) herase) (Primrec.const 1)
  have hb2f : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + 6 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) + 1 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL6) (Primrec.const 1)) (Primrec.const 1)
  have hb4 : Primrec (fun p : ℕ × ℕ × ℕ =>
      56 * (5 + 10 * (p.1 + 1) + 4 + 0 + (p.2.1 - (5 + 10 * (p.1 + 1) + 4)) % 2) + 1 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL0) (Primrec.const 1)) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp hph (Primrec.const 0))
    (Primrec.ite hbusy hb0t hb0f)
    (Primrec.ite (Primrec.eq.comp hph (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp hm32 (Primrec.const 1)) hb1t hb0f)
      (Primrec.ite (Primrec.eq.comp hph (Primrec.const 2))
        (Primrec.ite hbusy hb2t hb2f)
        (Primrec.ite (Primrec.eq.comp hph (Primrec.const 3))
          (Primrec.ite (Primrec.eq.comp hm32 (Primrec.const 1)) (Primrec.const 0) hb2f)
          (Primrec.ite (Primrec.eq.comp hph (Primrec.const 4)) hb4 hb1t))))

/-- The numeric live marked-run row generator is primitive recursive in its source code, coin
coordinate, label, and cell index. -/
theorem primrec_phase1MarkLiveRowNat :
    Primrec (fun p : (Code × ℕ) × ℕ × ℕ => phase1MarkLiveRowNat p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hcode : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hcD : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hl : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hQ : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => controlSize p.1.1) :=
    primrec_controlSize.comp hcode
  have hQ1 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => controlSize p.1.1 + 1) :=
    Primrec.nat_add.comp hQ (Primrec.const 1)
  have hq : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => (p.2.1 - 5) / 2) :=
    Primrec.nat_div.comp (Primrec.nat_sub.comp hl (Primrec.const 5)) (Primrec.const 2)
  have hbD : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => (p.2.1 - 5) % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_sub.comp hl (Primrec.const 5)) (Primrec.const 2)
  have hd18 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.2.2 / 18) :=
    Primrec.nat_div.comp hs (Primrec.const 18)
  have hm63 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.2.2 / 6 % 3) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const 6)) (Primrec.const 3)
  have hm32 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ => p.2.2 / 3 % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const 3)) (Primrec.const 2)
  have hidx : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      1 + (controlSize p.1.1 + 1)
        + (p.1.2 * (controlSize p.1.1 + 1) + (p.2.1 - 5) / 2) * 3 + p.2.2 / 6 % 3) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1) hQ1)
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp hcD hQ1) hq) (Primrec.const 3))) hm63
  have hsrc : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3)) :=
    ((Primrec.list_getD (0 : ℕ)).comp hcode hidx).of_eq (fun p => rfl)
  have hm5 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) :=
    Primrec.nat_sub.comp hsrc (Primrec.const 1)
  have hq' : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      (phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
        % (controlSize p.1.1 + 1)) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hm5 (Primrec.const 5)) hQ1
  have hact : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      (phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) % 5) :=
    Primrec.nat_mod.comp hm5 (Primrec.const 5)
  have hcar : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      2 + 18 * (p.2.2 / 18) + 6 * (p.2.2 / 6 % 3) + 3 * (p.2.2 / 3 % 2) + 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 18) hd18))
      (Primrec.nat_mul.comp (Primrec.const 6) hm63))
      (Primrec.nat_mul.comp (Primrec.const 3) hm32)) (Primrec.const 2)
  have hsel1 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      if p.2.2 / 3 % 2 = 1 then 1 else (p.2.1 - 5) % 2) :=
    Primrec.ite (Primrec.eq.comp hm32 (Primrec.const 1)) (Primrec.const 1) hbD
  have hsel0 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      if p.2.2 / 3 % 2 = 1 then 0 else (p.2.1 - 5) % 2) :=
    Primrec.ite (Primrec.eq.comp hm32 (Primrec.const 1)) (Primrec.const 0) hbD
  have h2q' : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
        % (controlSize p.1.1 + 1))) :=
    Primrec.nat_mul.comp (Primrec.const 2) hq'
  have h2qs1 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
        % (controlSize p.1.1 + 1))
        + (if p.2.2 / 3 % 2 = 1 then 1 else (p.2.1 - 5) % 2)) :=
    Primrec.nat_add.comp h2q' hsel1
  have h2qs0 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
        % (controlSize p.1.1 + 1))
        + (if p.2.2 / 3 % 2 = 1 then 0 else (p.2.1 - 5) % 2)) :=
    Primrec.nat_add.comp h2q' hsel0
  have h2qb : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
        % (controlSize p.1.1 + 1)) + (p.2.1 - 5) % 2) :=
    Primrec.nat_add.comp h2q' hbD
  have hL0 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      5 + 8 * (controlSize p.1.1 + 1) + 2 * ((p.2.1 - 5) / 2) + (p.2.1 - 5) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 8) hQ1))
      (Primrec.nat_mul.comp (Primrec.const 2) hq)) hbD
  have hLA0 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      5 + 2 * (controlSize p.1.1 + 1)
        + 3 * (2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
              % (controlSize p.1.1 + 1))
            + (if p.2.2 / 3 % 2 = 1 then 1 else (p.2.1 - 5) % 2)) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 2) hQ1))
      (Primrec.nat_mul.comp (Primrec.const 3) h2qs1)) (Primrec.const 1)
  have hLA1 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      5 + 2 * (controlSize p.1.1 + 1)
        + 3 * (2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
              % (controlSize p.1.1 + 1))
            + (if p.2.2 / 3 % 2 = 1 then 0 else (p.2.1 - 5) % 2)) + 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 2) hQ1))
      (Primrec.nat_mul.comp (Primrec.const 3) h2qs0)) (Primrec.const 2)
  have hLA2 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      5 + 2 * (controlSize p.1.1 + 1)
        + 3 * (2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
              % (controlSize p.1.1 + 1)) + (p.2.1 - 5) % 2)) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 5)
      (Primrec.nat_mul.comp (Primrec.const 2) hQ1))
      (Primrec.nat_mul.comp (Primrec.const 3) h2qb)
  have hcar2 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      2 + 18 * (p.2.2 / 18) + 6 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2)
            (p.2.2 / 6 % 3) - 1) % 5 - 2) + 3 * (p.2.2 / 3 % 2) + 2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 18) hd18))
      (Primrec.nat_mul.comp (Primrec.const 6)
        (Primrec.nat_sub.comp hact (Primrec.const 2))))
      (Primrec.nat_mul.comp (Primrec.const 3) hm32)) (Primrec.const 2)
  have hb0 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      56 * (5 + 8 * (controlSize p.1.1 + 1) + 2 * ((p.2.1 - 5) / 2) + (p.2.1 - 5) % 2)
        + (2 + 18 * (p.2.2 / 18) + 6 * (p.2.2 / 6 % 3) + 3 * (p.2.2 / 3 % 2) + 2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hL0) hcar) (Primrec.const 1)
  have hbA0 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      56 * (5 + 2 * (controlSize p.1.1 + 1)
          + 3 * (2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
                % (controlSize p.1.1 + 1))
              + (if p.2.2 / 3 % 2 = 1 then 1 else (p.2.1 - 5) % 2)) + 1)
        + (2 + 18 * (p.2.2 / 18) + 6 * (p.2.2 / 6 % 3) + 3 * (p.2.2 / 3 % 2) + 2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hLA0) hcar) (Primrec.const 1)
  have hbA1 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      56 * (5 + 2 * (controlSize p.1.1 + 1)
          + 3 * (2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
                % (controlSize p.1.1 + 1))
              + (if p.2.2 / 3 % 2 = 1 then 0 else (p.2.1 - 5) % 2)) + 2)
        + (2 + 18 * (p.2.2 / 18) + 6 * (p.2.2 / 6 % 3) + 3 * (p.2.2 / 3 % 2) + 2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hLA1) hcar) (Primrec.const 1)
  have hbA2 : Primrec (fun p : (Code × ℕ) × ℕ × ℕ =>
      56 * (5 + 2 * (controlSize p.1.1 + 1)
          + 3 * (2 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2) (p.2.2 / 6 % 3) - 1) / 5
                % (controlSize p.1.1 + 1)) + (p.2.1 - 5) % 2))
        + (2 + 18 * (p.2.2 / 18) + 6 * ((phase1SourceNat p.1.1 p.1.2 ((p.2.1 - 5) / 2)
              (p.2.2 / 6 % 3) - 1) % 5 - 2) + 3 * (p.2.2 / 3 % 2) + 2) + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 56) hLA2) hcar2) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp hsrc (Primrec.const 0)) hb0
    (Primrec.ite (Primrec.nat_le.comp hact (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp hact (Primrec.const 0)) hbA0 hbA1) hbA2)

/-- The complete numeric row generator is primitive recursive jointly in the source code and row
index. -/
theorem primrec_phase1RowNat : Primrec₂ (fun (code : Code) (i : ℕ) => phase1RowNat code i) := by
  change Primrec (fun p : Code × ℕ => phase1RowNat p.1 p.2)
  have hcode : Primrec (fun p : Code × ℕ => p.1) := Primrec.fst
  have hQ : Primrec (fun p : Code × ℕ => controlSize p.1) := primrec_controlSize.comp Primrec.fst
  have hQ1 : Primrec (fun p : Code × ℕ => controlSize p.1 + 1) :=
    Primrec.nat_add.comp hQ (Primrec.const 1)
  have hK : Primrec (fun p : Code × ℕ => phase1Bound (controlSize p.1)) :=
    primrec_phase1Bound.comp Primrec.fst
  have hK1 : Primrec (fun p : Code × ℕ => phase1Bound (controlSize p.1) + 1) :=
    Primrec.nat_add.comp hK (Primrec.const 1)
  have hsIdx : Primrec (fun p : Code × ℕ => p.2 % 54) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 54)
  have hdiv : Primrec (fun p : Code × ℕ => p.2 / 54) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 54)
  have hl : Primrec (fun p : Code × ℕ => p.2 / 54 % (phase1Bound (controlSize p.1) + 1)) :=
    Primrec.nat_mod.comp hdiv hK1
  have hcD : Primrec (fun p : Code × ℕ =>
      if phase1Bound (controlSize p.1) + 1 ≤ p.2 / 54 then 1 else 0) :=
    Primrec.ite (Primrec.nat_le.comp hK1 hdiv) (Primrec.const 1) (Primrec.const 0)
  have hpair2 : Primrec (fun p : Code × ℕ =>
      (p.2 / 54 % (phase1Bound (controlSize p.1) + 1), p.2 % 54)) := hl.pair hsIdx
  have hcopy := primrec_phase1CopyRowNat.comp hpair2
  have hlive := primrec_phase1MarkLiveRowNat.comp ((hcode.pair hcD).pair hpair2)
  have hpend := primrec_phase1PendingRowNat.comp (hQ.pair (hl.pair hsIdx))
  have hmark := primrec_phase1MarkHaltRowNat.comp ((hcode.pair hl).pair hsIdx)
  have hhome := primrec_phase1HomeRowNat.comp (hQ.pair (hl.pair hsIdx))
  have hreset := primrec_phase1ResetRowNat.comp (hQ.pair (hl.pair hsIdx))
  have hb2 : Primrec (fun p : Code × ℕ => 5 + 2 * (controlSize p.1 + 1)) :=
    Primrec.nat_add.comp (Primrec.const 5) (Primrec.nat_mul.comp (Primrec.const 2) hQ1)
  have hb8 : Primrec (fun p : Code × ℕ => 5 + 8 * (controlSize p.1 + 1)) :=
    Primrec.nat_add.comp (Primrec.const 5) (Primrec.nat_mul.comp (Primrec.const 8) hQ1)
  have hb10 : Primrec (fun p : Code × ℕ => 5 + 10 * (controlSize p.1 + 1)) :=
    Primrec.nat_add.comp (Primrec.const 5) (Primrec.nat_mul.comp (Primrec.const 10) hQ1)
  have hb104 : Primrec (fun p : Code × ℕ => 5 + 10 * (controlSize p.1 + 1) + 4) :=
    Primrec.nat_add.comp hb10 (Primrec.const 4)
  exact Primrec.ite (Primrec.nat_lt.comp hl (Primrec.const 5)) hcopy
    (Primrec.ite (Primrec.nat_lt.comp hl hb2) hlive
      (Primrec.ite (Primrec.nat_lt.comp hl hb8) hpend
        (Primrec.ite (Primrec.nat_lt.comp hl hb10) hmark
          (Primrec.ite (Primrec.nat_lt.comp hl hb104) hhome hreset))))

/-- The copy–run–reset compiler is primitive recursive on source codes. -/
theorem primrec_tmCopyRunResetCompile : Primrec tmCopyRunResetCompile := by
  have hb : Primrec (fun code : Code => phase1Bound (controlSize code)) := primrec_phase1Bound
  have ho : Primrec₂ (fun (code : Code) (l : ℕ) => phase1ReadoutNat code l) :=
    primrec_phase1ReadoutNat
  have hr : Primrec₂ (fun (code : Code) (i : ℕ) => phase1RowNat code i) := primrec_phase1RowNat
  have hbool : Primrec Bool.toNat := Primrec.dom_bool Bool.toNat
  have hq : Primrec (fun code : Code => phase1Bound (controlSize code) + 1) :=
    Primrec.nat_add.comp hb (Primrec.const 1)
  have ha : Primrec (fun code : Code =>
      (List.range (phase1Bound (controlSize code) + 1)).map
        (fun l => (phase1ReadoutNat code l).toNat)) :=
    Primrec.list_map (Primrec.list_range.comp hq) (hbool.comp₂ ho)
  have ht : Primrec (fun code : Code =>
      (List.range (108 * (phase1Bound (controlSize code) + 1))).map
        (fun i => phase1RowNat code i)) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 108) hq)) hr
  exact Primrec.list_cons.comp hb (Primrec.list_append.comp ha ht)

/-- The copy–run–reset compiler is computable on source codes. -/
theorem computable_tmCopyRunResetCompile : Computable tmCopyRunResetCompile :=
  primrec_tmCopyRunResetCompile.to_comp

/-- The first compilation frontier, defined by the copy–run–reset compiler. -/
def frontier1 (code : Code) : CodeCore := tmCopyRunResetCompile code

/-- The first compilation frontier is computable jointly in the source code and an unused
natural-number parameter. -/
theorem computable₂_frontier1 :
    Computable₂ (fun (code : Code) (_ : ℕ) => frontier1 code) :=
  (primrec_tmCopyRunResetCompile.comp₂ Primrec₂.left).to_comp

alias frontier1_run := tmCopyRunResetCompile_run
