/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilistic
import Qatlib.Concepts.ClassicalTape.TapeBoundary
import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilisticDefs

/-!
# Tape invariants for classical majority amplification

This module describes the input and working tracks of a majority-vote tape machine. The cell
functions `majInputCell` and `majRunCell` express the invariants used to copy an input, return
the head to its origin, and simulate a component machine.

The proofs account for the consumed coin prefix and transition count during copying. They
provide implementation details for repetition and majority amplification in the computational
setting of [KitaevShenVyalyi2002].

## Main statements

* `maj_copy_run`: copying and returning to the origin use `3 * input.length + 2` transitions.
* `maj_sim_step_some`: a component transition is simulated while preserving its working track.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Turing
open scoped Classical

/-- The input tape cell at an integer position, with blank cells at negative positions and
beyond the encoded input. -/
def majInputCell (input : List Bool) (x : ℤ) : Option Bool :=
  if x < 0 then (none : Option Bool) else (standardBitEncode input).getI x.toNat

/-- The standard bit encoding contains the input bit at each valid index and a blank at every
later index. -/
theorem standardBitEncode_getI (input : List Bool) (m : ℕ) :
    (standardBitEncode input).getI m = if m < input.length then some (input.getI m) else none := by
  unfold standardBitEncode
  rw [getI_map]
  split_ifs <;> rfl

/-- The track encoding places the input on track zero and leaves all other tracks blank. -/
theorem tracksEncode_getI (m : ℕ) (input : List Bool) (x : ℕ) :
    (tracksEncode m input).getI x =
      if x < input.length then (fun t : Fin m => if t.val = 0 then some (input.getI x) else none)
      else default := by
  unfold tracksEncode
  rw [getI_map]

/-- At a natural-number position, `majInputCell` is the corresponding input bit when in range
and is blank otherwise. -/
theorem majInputCell_ofNat (input : List Bool) (m : ℕ) :
    majInputCell input m = if m < input.length then some (input.getI m) else none := by
  unfold majInputCell
  rw [if_neg (by omega : ¬((m : ℤ) < 0)), Int.toNat_natCast]
  rw [standardBitEncode_getI]

/-- Every negative integer position of `majInputCell` is blank. -/
theorem majInputCell_negSucc (input : List Bool) (m : ℕ) :
    majInputCell input (Int.negSucc m) = (none : Option Bool) := by
  unfold majInputCell
  rw [if_pos (Int.negSucc_lt_zero m)]

/-- Evaluation of the track encoding at a given track yields an input bit only on track zero and
within the input length. -/
theorem tracksEncode_getI_apply (m : ℕ) (input : List Bool) (x : ℕ) (t : Fin m) :
    (tracksEncode m input).getI x t =
      if t.val = 0 then if x < input.length then some (input.getI x) else none
      else none := by
  rw [tracksEncode_getI]
  by_cases hx : x < input.length
  · rw [if_pos hx]
    show (if t.val = 0 then some (input.getI x) else none) = _
    by_cases ht : t.val = 0
    · rw [if_pos ht, if_pos ht, if_pos hx]
    · rw [if_neg ht, if_neg ht]
  · rw [if_neg hx]
    show (none : Option Bool) = _
    by_cases ht : t.val = 0
    · rw [if_pos ht, if_neg hx]
    · rw [if_neg ht]

/-- At a nonnegative position, the majority input cell is the input bit precisely when the index
lies within the input. -/
theorem majInputCell_ofNat' (input : List Bool) (m : ℕ) :
    majInputCell input m = if m < input.length then some (input.getI m) else none :=
  majInputCell_ofNat input m

/-- The initialized majority tape contains `majInputCell` on track zero and blank cells on all
working tracks. -/
theorem init_majorityEncode_nth {Q r : ℕ}
    (input : List Bool) (x : ℤ) (t : Fin (2 * r + 2)) :
    (((Turing.TM0.init (majorityEncode r input) :
          Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)).Tape).nth x) t =
      if t.val = 0 then majInputCell input x else none := by
  rw [init_nth]
  by_cases hx : x < 0
  · rw [if_pos hx]
    show (none : Option Bool) = _
    by_cases ht : t.val = 0
    · rw [if_pos ht, majInputCell, if_pos hx]
    · rw [if_neg ht]
  · rw [if_neg hx]
    rw [show (majorityEncode r input) = tracksEncode (2 * r + 2) input from rfl,
      tracksEncode_getI_apply]
    have hxc : majInputCell input x =
        if x.toNat < input.length then some (input.getI x.toNat) else none := by
      rw [majInputCell, if_neg hx]
      exact standardBitEncode_getI input x.toNat
    by_cases ht : t.val = 0
    · rw [if_pos ht, if_pos ht, hxc]
    · rw [if_neg ht, if_neg ht]

/-- The majority machine starts in the first copy-write state with zero tally and zero position. -/
theorem init_majorityEncode_zero {Q r : ℕ} (input : List Bool) :
    Turing.TM0.init (majorityEncode r input) =
      (⟨.copyW ⟨0, by omega⟩ 0 0,
        (Turing.TM0.init (majorityEncode r input) :
          Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)).Tape⟩ :
        Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) := by
  rfl

/-- The partially copied working-track cell, retaining the input strictly before `pos` and
remaining blank from `pos` onward. -/
def majRunCell (input : List Bool) (pos : ℕ) (x : ℤ) : Option Bool :=
  if x < (pos : ℤ) then majInputCell input x else (none : Option Bool)

/-- The working track is blank before any input positions have been copied. -/
theorem majRunCell_zero (input : List Bool) (x : ℤ) :
    majRunCell input 0 x = (none : Option Bool) := by
  unfold majRunCell
  rw [Int.natCast_zero]
  by_cases hx : x < (0 : ℤ)
  · rw [if_pos hx, majInputCell, if_pos hx]
  · rw [if_neg hx]

/-- After copying the full input length, the working-track cell agrees with the input cell
everywhere. -/
theorem majRunCell_end (input : List Bool) (x : ℤ) :
    majRunCell input input.length x = majInputCell input x := by
  by_cases hx : x < (input.length : ℤ)
  · rw [majRunCell, if_pos hx]
  · rw [majRunCell, if_neg hx]
    by_cases h0 : x < 0
    · rw [majInputCell, if_pos h0]
    · have hle : (input.length : ℤ) ≤ x := by omega
      have hx0 : 0 ≤ x := by omega
      rw [majInputCell, if_neg h0]
      rw [standardBitEncode_getI, if_neg (by omega)]

/-- Advancing the copy boundary by one replaces exactly the cell at the old boundary with its
input cell. -/
theorem majRunCell_succ (input : List Bool) (pos : ℕ) (x : ℤ) :
    majRunCell input (pos + 1) x =
      if x = (pos : ℤ) then majInputCell input x else majRunCell input pos x := by
  by_cases he : x = (pos : ℤ)
  · subst he
    rw [majRunCell, if_pos (show (pos : ℤ) < ((pos + 1 : ℕ) : ℤ) from by omega)]
    rw [if_pos rfl]
  · rw [if_neg he]
    by_cases h : x < (pos : ℤ)
    · rw [majRunCell, majRunCell, if_pos h, if_pos (by omega)]
    · rw [majRunCell, majRunCell, if_neg h, if_neg (by omega)]

/-- A simulation working track has an index distinct from the input track zero. -/
theorem runTrackIdx_ne_zero {r : ℕ} (j : Fin (2 * r + 1)) :
    runTrackIdx r j ≠ (0 : Fin (2 * r + 2)) := by
  intro h
  have h2 : (runTrackIdx r j).val = (0 : Fin (2 * r + 2)).val := congrArg Fin.val h
  simp only [runTrackIdx, Fin.val_zero] at h2
  omega

/-- The input track zero is distinct from every simulation working track. -/
theorem runTrackIdx_ne_zero' {r : ℕ} (j : Fin (2 * r + 1)) :
    (0 : Fin (2 * r + 2)) ≠ runTrackIdx r j :=
  Ne.symm (runTrackIdx_ne_zero j)

/-- Successive additions to the transition-count component combine into addition by their sum. -/
theorem prod_map_add (m n : ℕ) (p : Option Bool × ℕ) :
    Prod.map id (· + m) (Prod.map id (· + n) p) = Prod.map id (· + (n + m)) p := by
  rcases p with ⟨a, b⟩
  simp [Prod.map]
  omega

/-- The input-track invariant identifies the head symbol on track zero with the input cell at
the current position. -/
theorem maj_sym_zero {input : List Bool} {pos : ℕ} {r : ℕ}
    {T : Turing.Tape (Tracks (2 * r + 2))}
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i)) :
    T.head ⟨0, by omega⟩ = majInputCell input pos := by
  rw [← Turing.Tape.nth_zero T]
  have h := h0 0
  simpa using h

/-- Within the input, the copy-write transition writes the current bit to the selected working
track and enters the copy-move state. -/
theorem maj_copyW_tab_write {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally pos : ℕ) (hpos : pos < input.length)
    (T : Turing.Tape (Tracks (2 * r + 2)))
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i)) :
    ∀ c : Bool, majorityTable Q r M acceptM c (.copyW j tally pos) T.head
      = some (.copyM j tally pos,
          .write fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t) := by
  intro c
  have hsym : T.head ⟨0, by omega⟩ = some (input.getI pos) := by
    rw [maj_sym_zero h0, majInputCell_ofNat, if_pos hpos]
  show (match T.head ⟨0, by omega⟩ with
    | some b => some (MajCtrl.copyM j tally pos,
        Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then some b else T.head t)
    | none => some (MajCtrl.copyHome j tally pos, Turing.TM0.Stmt.write T.head)) = _
  rw [hsym]

/-- At or beyond the input length, the copy-write transition preserves the head symbols and
enters the return-home state. -/
theorem maj_copyW_tab_blank {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally pos : ℕ)
    (T : Turing.Tape (Tracks (2 * r + 2)))
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i))
    (hpos : input.length ≤ pos) :
    ∀ c : Bool, majorityTable Q r M acceptM c (.copyW j tally pos) T.head
      = some (.copyHome j tally pos, .write T.head) := by
  intro c
  have hsym : T.head ⟨0, by omega⟩ = (none : Option Bool) := by
    rw [maj_sym_zero h0, majInputCell_ofNat, if_neg (by omega)]
  show (match T.head ⟨0, by omega⟩ with
    | some b => some (MajCtrl.copyM j tally pos,
        Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then some b else T.head t)
    | none => some (MajCtrl.copyHome j tally pos, Turing.TM0.Stmt.write T.head)) = _
  rw [hsym]

/-- Under the input and working-track invariants, a copy-write step writes the current input bit
to the selected working track. -/
theorem maj_copyW_write {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally pos : ℕ) (hpos : pos < input.length)
    (T : Turing.Tape (Tracks (2 * r + 2)))
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i))
    (hj : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = majRunCell input pos ((pos : ℤ) + i)) :
    ∀ c : Bool, Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.copyW j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
      = some (⟨.copyM j tally pos,
          T.write fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t⟩) := by
  intro c
  have htab := maj_copyW_tab_write M acceptM input j tally pos hpos T h0 c
  exact TM0_step_eq_some (majorityTable Q r M acceptM c)
    (⟨.copyW j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _ htab

/-- Writing the next copied bit preserves the input track and advances the working-track copy
boundary by one. -/
theorem maj_write_inv {input : List Bool} {r : ℕ} {j : Fin (2 * r + 1)} {pos : ℕ}
    {T : Turing.Tape (Tracks (2 * r + 2))}
    (hpos : pos < input.length)
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i))
    (hj : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = majRunCell input pos ((pos : ℤ) + i)) :
    (∀ i : ℤ, ((T.write (fun t => if t = runTrackIdx r j then some (input.getI pos)
      else T.head t)).nth i) 0 = majInputCell input ((pos : ℤ) + i)) ∧
    (∀ i : ℤ, ((T.write (fun t => if t = runTrackIdx r j then some (input.getI pos)
      else T.head t)).nth i) (runTrackIdx r j) = majRunCell input (pos + 1) ((pos : ℤ) + i)) := by
  constructor
  · intro i
    rw [Turing.Tape.write_nth]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, Int.add_zero]
      have hne := runTrackIdx_ne_zero' j
      rw [if_neg hne]
      exact h0 0
    · rw [if_neg hi]
      exact h0 i
  · intro i
    rw [Turing.Tape.write_nth]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, if_pos rfl, Int.add_zero, majRunCell_succ]
      rw [if_pos rfl, majInputCell_ofNat, if_pos hpos]
    · rw [if_neg hi]
      erw [hj i]
      rw [majRunCell_succ]
      by_cases he : (pos : ℤ) + i = (pos : ℤ)
      · rw [if_pos he]
        have : i = 0 := by omega
        exact absurd this hi
      · rw [if_neg he]

/-- The copy-move transition moves right and increments the input position. -/
theorem maj_copyM_tab {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (j : Fin (2 * r + 1)) (tally pos : ℕ)
    (T : Turing.Tape (Tracks (2 * r + 2))) (c : Bool) :
    majorityTable Q r M acceptM c (.copyM j tally pos) T.head
      = some (.copyW j tally (pos + 1), .move Turing.Dir.right) := rfl

/-- A copy-move machine step advances to the next copy-write state with the tape moved one cell
right. -/
theorem maj_copyM_run {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (j : Fin (2 * r + 1)) (tally pos : ℕ)
    (T : Turing.Tape (Tracks (2 * r + 2))) (c : Bool) :
    Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.copyM j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
      = some (⟨.copyW j tally (pos + 1), T.move Turing.Dir.right⟩) :=
  TM0_step_eq_some (majorityTable Q r M acceptM c)
    (⟨.copyM j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _
    (maj_copyM_tab M acceptM j tally pos T c)

/-- A return-home transition at positive position moves left and decrements the position
counter. -/
theorem maj_copyHome_tab {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (j : Fin (2 * r + 1)) (tally pos : ℕ)
    (T : Turing.Tape (Tracks (2 * r + 2))) (c : Bool) :
    majorityTable Q r M acceptM c (.copyHome j tally (pos + 1)) T.head
      = some (.copyHome j tally pos, .move Turing.Dir.left) := rfl

/-- At position zero, the return-home transition preserves the tape and enters the initial
component simulation state. -/
theorem maj_copyHome0_tab {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (j : Fin (2 * r + 1)) (tally : ℕ)
    (T : Turing.Tape (Tracks (2 * r + 2))) (c : Bool) :
    majorityTable Q r M acceptM c (.copyHome j tally 0) T.head
      = some (.simQ j ⟨0, by omega⟩ tally 0, .write T.head) := rfl

/-- With enough coins, returning home consumes `pos + 1` transitions and restores both track
invariants relative to the origin. -/
theorem maj_copyHome_run {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally : ℕ) :
    ∀ (pos : ℕ) (T : Turing.Tape (Tracks (2 * r + 2)))
      (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i))
      (hj : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = majRunCell input input.length ((pos : ℤ) + i))
      (coins : List Bool), pos + 1 ≤ coins.length →
    ∃ T' : Turing.Tape (Tracks (2 * r + 2)),
      coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r) coins
          (⟨.copyHome j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) =
        Prod.map id (· + (pos + 1))
          (coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r)
            (coins.drop (pos + 1)) (⟨.simQ j ⟨0, by omega⟩ tally 0, T'⟩)) ∧
      (∀ i : ℤ, (T'.nth i) 0 = majInputCell input i) ∧
      (∀ i : ℤ, (T'.nth i) (runTrackIdx r j) = majRunCell input input.length i) := by
  intro pos
  induction pos with
  | zero =>
    intro T h0 hj coins hlen
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, coins = c :: cs :=
      List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen)
    have hst : Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.copyHome j tally 0, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.simQ j ⟨0, by omega⟩ tally 0, T.write T.head⟩) :=
      TM0_step_eq_some (majorityTable Q r M acceptM c)
        (⟨.copyHome j tally 0, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _
        (maj_copyHome0_tab M acceptM j tally T c)
    have hch : coinHalt (majorityTable Q r M acceptM)
        (⟨.copyHome j tally 0, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) = false := by
      simp only [coinHalt]
      rw [maj_copyHome0_tab M acceptM j tally T false, maj_copyHome0_tab M acceptM j tally T true]
      rfl
    rw [coinTapeRunAux_cons_of_step_some _ _ c cs _ _ hch hst]
    have hwrite : (T.write T.head) = T := Turing.Tape.write_self T
    rw [hwrite]
    refine ⟨T, ?_, ?_, ?_⟩
    · show Prod.map id (· + 1) (coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r) cs
        (⟨.simQ j ⟨0, by omega⟩ tally 0, T⟩)) =
        Prod.map id (· + 1) (coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r) cs
          (⟨.simQ j ⟨0, by omega⟩ tally 0, T⟩))
      rfl
    · intro i
      have := h0 i
      simpa [Int.zero_add] using this
    · intro i
      erw [hj i]
      congr 1
      omega
  | succ pos ih =>
    intro T h0 hj coins hlen
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, coins = c :: cs :=
      List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen)
    simp only [List.length_cons] at hlen
    have hst : Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.copyHome j tally (pos + 1), T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.copyHome j tally pos, T.move Turing.Dir.left⟩) :=
      TM0_step_eq_some (majorityTable Q r M acceptM c)
        (⟨.copyHome j tally (pos + 1), T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _
        (maj_copyHome_tab M acceptM j tally pos T c)
    have hch : coinHalt (majorityTable Q r M acceptM)
        (⟨.copyHome j tally (pos + 1), T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) = false := by
      simp only [coinHalt]
      rw [maj_copyHome_tab M acceptM j tally pos T false,
          maj_copyHome_tab M acceptM j tally pos T true]
      rfl
    rw [coinTapeRunAux_cons_of_step_some _ _ c cs _ _ hch hst]
    have h0' : ∀ i : ℤ, ((T.move Turing.Dir.left).nth i) 0 = majInputCell input ((pos : ℤ) + i) := by
      intro i
      rw [Turing.Tape.move_left_nth]
      have := h0 (i - 1)
      simpa [add_sub_cancel] using this
    have hj' : ∀ i : ℤ, ((T.move Turing.Dir.left).nth i) (runTrackIdx r j)
        = majRunCell input input.length ((pos : ℤ) + i) := by
      intro i
      erw [Turing.Tape.move_left_nth]
      have := hj (i - 1)
      erw [this]
      congr 1
      omega
    have hlen2 : pos + 1 ≤ cs.length := by omega
    obtain ⟨T', hr, h0T', hjT'⟩ := ih (T.move Turing.Dir.left) h0' hj' cs hlen2
    have hdrop : cs.drop (pos + 1) = (c :: cs).drop (pos + 2) := by
      rw [List.drop_succ_cons]
    refine ⟨T', ?_, h0T', hjT'⟩
    rw [hr, hdrop, prod_map_add]

/-- At the input length, a copy-write machine step preserves the tape contents and begins
returning home. -/
theorem maj_copyW_blank {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally : ℕ) (T : Turing.Tape (Tracks (2 * r + 2)))
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((input.length : ℤ) + i)) :
    ∀ c : Bool, Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.copyW j tally input.length, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
      = some (⟨.copyHome j tally input.length, T.write T.head⟩) := by
  intro c
  have htab := maj_copyW_tab_blank M acceptM input j tally input.length T h0 (Nat.le_refl _) c
  exact TM0_step_eq_some (majorityTable Q r M acceptM c)
    (⟨.copyW j tally input.length, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _ htab

/-- Copying the remaining `d` input positions consumes `2 * d` transitions and establishes the
completed-copy invariant. -/
theorem maj_copyW_loop {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally : ℕ) :
    ∀ (d pos : ℕ), d = input.length - pos → pos ≤ input.length →
    ∀ (T : Turing.Tape (Tracks (2 * r + 2)))
      (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((pos : ℤ) + i))
      (hj : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = majRunCell input pos ((pos : ℤ) + i))
      (coins : List Bool), 2 * d ≤ coins.length →
    ∃ T' : Turing.Tape (Tracks (2 * r + 2)),
      coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r) coins
          (⟨.copyW j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) =
        Prod.map id (· + (2 * d))
          (coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r)
            (coins.drop (2 * d))
            (⟨.copyW j tally input.length, T'⟩)) ∧
      (∀ i : ℤ, (T'.nth i) 0 = majInputCell input ((input.length : ℤ) + i)) ∧
      (∀ i : ℤ, (T'.nth i) (runTrackIdx r j) = majRunCell input input.length ((input.length : ℤ) + i)) := by
  intro d
  induction d with
  | zero =>
    intro pos hd hle T h0 hj coins hlen
    have hpos : pos = input.length := by omega
    subst hpos
    refine ⟨T, ?_, h0, ?_⟩
    · show coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r) coins
          (⟨.copyW j tally input.length, T⟩) =
        Prod.map id (· + 0)
          (coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r)
            (coins.drop 0) (⟨.copyW j tally input.length, T⟩))
      rfl
    · intro i
      erw [hj i, majRunCell_end]
  | succ d ih =>
    intro pos hd hle T h0 hj coins hlen
    have hlt : pos < input.length := by omega
    obtain ⟨c₁, cs₁, rfl⟩ : ∃ c cs, coins = c :: cs :=
      List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen)
    simp only [List.length_cons] at hlen
    have hst₁ : Turing.TM0.step (majorityTable Q r M acceptM c₁)
        (⟨.copyW j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.copyM j tally pos,
            T.write fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t⟩) :=
      maj_copyW_write M acceptM input j tally pos hlt T h0 hj c₁
    have hch₁ : coinHalt (majorityTable Q r M acceptM)
        (⟨.copyW j tally pos, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) = false := by
      simp only [coinHalt]
      rw [maj_copyW_tab_write M acceptM input j tally pos hlt T h0 false,
        maj_copyW_tab_write M acceptM input j tally pos hlt T h0 true]
      rfl
    rw [coinTapeRunAux_cons_of_step_some _ _ c₁ cs₁ _ _ hch₁ hst₁]
    obtain ⟨c₂, cs₂, rfl⟩ : ∃ c cs, cs₁ = c :: cs :=
      List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen; omega)
    simp only [List.length_cons] at hlen
    have hst₂ : Turing.TM0.step (majorityTable Q r M acceptM c₂)
        (⟨.copyM j tally pos,
          T.write (fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t)⟩ :
          Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.copyW j tally (pos + 1),
          Turing.Tape.move Turing.Dir.right
            (T.write (fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t))⟩) :=
      maj_copyM_run M acceptM j tally pos _ c₂
    have hch₂ : coinHalt (majorityTable Q r M acceptM)
        (⟨.copyM j tally pos,
          T.write fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t⟩ :
          Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) = false := by
      simp only [coinHalt]
      rw [maj_copyM_tab M acceptM j tally pos _ false, maj_copyM_tab M acceptM j tally pos _ true]
      rfl
    rw [coinTapeRunAux_cons_of_step_some _ _ c₂ cs₂ _ _ hch₂ hst₂]
    obtain ⟨hinv₀, hinvj⟩ := maj_write_inv (r := r) hlt h0 hj
    have h0' : ∀ i : ℤ,
        ((Turing.Tape.move Turing.Dir.right
          (T.write (fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t))).nth i) 0
          = majInputCell input (((pos + 1 : ℕ) : ℤ) + i) := by
      intro i
      rw [Turing.Tape.move_right_nth]
      erw [hinv₀ (i + 1)]
      congr 1
      omega
    have hj' : ∀ i : ℤ,
        ((Turing.Tape.move Turing.Dir.right
          (T.write (fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t))).nth i)
          (runTrackIdx r j) = majRunCell input (pos + 1) (((pos + 1 : ℕ) : ℤ) + i) := by
      intro i
      erw [Turing.Tape.move_right_nth]
      erw [hinvj (i + 1)]
      congr 1
      omega
    have hlen2 : 2 * d ≤ cs₂.length := by omega
    have hpos2 : pos + 1 ≤ input.length := by omega
    have hd' : d = input.length - (pos + 1) := by omega
    obtain ⟨T', hr, h0T', hjT'⟩ := ih (pos + 1) hd' hpos2
      (Turing.Tape.move Turing.Dir.right
        (T.write (fun t => if t = runTrackIdx r j then some (input.getI pos) else T.head t)))
      h0' hj' cs₂ hlen2
    refine ⟨T', ?_, h0T', hjT'⟩
    have hnum : (2 * (d + 1) : ℕ) = 2 * d + 2 := by omega
    have hdrop : cs₂.drop (2 * d) = (c₁ :: c₂ :: cs₂).drop (2 * d + 2) := by
      rw [List.drop_succ_cons, List.drop_succ_cons]
    rw [hr, hnum, hdrop, prod_map_add, prod_map_add]

/-- Copying an initially blank working track and returning home consumes `3 * input.length + 2`
transitions, leaving both selected tracks equal to the input. -/
theorem maj_copy_run {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (input : List Bool) (j : Fin (2 * r + 1))
    (tally : ℕ) (T : Turing.Tape (Tracks (2 * r + 2)))
    (h0 : ∀ i : ℤ, (T.nth i) 0 = majInputCell input i)
    (hj : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = none)
    (coins : List Bool) (hlen : 3 * input.length + 2 ≤ coins.length) :
    ∃ T' : Turing.Tape (Tracks (2 * r + 2)),
      coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r) coins
          (⟨.copyW j tally 0, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) =
        Prod.map id (· + (3 * input.length + 2))
          (coinTapeRunAux (majorityTable Q r M acceptM) (majorityAccept Q r)
            (coins.drop (3 * input.length + 2))
            (⟨.simQ j ⟨0, by omega⟩ tally 0, T'⟩)) ∧
      (∀ i : ℤ, (T'.nth i) 0 = majInputCell input i) ∧
      (∀ i : ℤ, (T'.nth i) (runTrackIdx r j) = majInputCell input i) := by
  have h0loop : ∀ i : ℤ, (T.nth i) 0 = majInputCell input ((0 : ℕ) + i) := by
    intro i
    simpa using h0 i
  have hjloop : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = majRunCell input 0 ((0 : ℕ) + i) := by
    intro i
    erw [hj i, majRunCell_zero]
  have hlen1 : 2 * input.length ≤ coins.length := by omega
  obtain ⟨T₁, hr₁, h0₁, hj₁⟩ :=
    maj_copyW_loop M acceptM input j tally input.length 0 rfl (Nat.zero_le _) T h0loop hjloop coins hlen1
  have hlen3 : input.length + 2 ≤ (coins.drop (2 * input.length)).length := by
    rw [List.length_drop]
    omega
  have hch : coinHalt (majorityTable Q r M acceptM)
      (⟨.copyW j tally input.length, T₁⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
      = false := by
    simp only [coinHalt]
    rw [maj_copyW_tab_blank M acceptM input j tally input.length T₁ h0₁ (Nat.le_refl _) false,
      maj_copyW_tab_blank M acceptM input j tally input.length T₁ h0₁ (Nat.le_refl _) true]
    rfl
  have hst : ∀ c : Bool, Turing.TM0.step (majorityTable Q r M acceptM c)
      (⟨.copyW j tally input.length, T₁⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
      = some (⟨.copyHome j tally input.length, T₁.write T₁.head⟩) :=
    maj_copyW_blank M acceptM input j tally T₁ h0₁
  rw [hr₁]
  obtain ⟨c, cs, hsplit⟩ : ∃ c cs, coins.drop (2 * input.length) = c :: cs :=
    List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen3 <;> omega)
  rw [hsplit, coinTapeRunAux_cons_of_step_some _ _ c cs _ _ hch (hst c)]
  have hwrite : T₁.write T₁.head = T₁ := Turing.Tape.write_self T₁
  rw [hwrite]
  have hlen4 : input.length + 1 ≤ cs.length := by
    have : (coins.drop (2 * input.length)).length = coins.length - 2 * input.length :=
      List.length_drop
    simp only [hsplit, List.length_cons] at this
    omega
  obtain ⟨T', hr₂, h0', hj'⟩ :=
    maj_copyHome_run M acceptM input j tally input.length T₁ h0₁ hj₁ cs hlen4
  refine ⟨T', ?_, h0', ?_⟩
  · rw [hr₂, prod_map_add, prod_map_add]
    have hnum : (input.length + 1 + (1 + 2 * input.length) : ℕ) = 3 * input.length + 2 := by
      omega
    rw [hnum]
    have hdrop : cs.drop (input.length + 1) = coins.drop (3 * input.length + 2) := by
      have h1 : coins.drop (3 * input.length + 2)
          = (coins.drop (2 * input.length)).drop (input.length + 2) := by
        rw [List.drop_drop]
        congr 1
        omega
      rw [h1, hsplit, List.drop_succ_cons]
    rw [hdrop]
  · intro i
    erw [hj' i, majRunCell_end]

/-- The simulation transition cases can be combined into a single `some` value, including the
transition to tallying when the component halts. -/
theorem maj_sim_tab {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (j : Fin (2 * r + 1)) (q : Fin (Q + 1))
    (tally : ℕ) (off : ℤ) (T : Turing.Tape (Tracks (2 * r + 2))) (c : Bool) :
    (match M c q (T.head (runTrackIdx r j)) with
      | some (q', .write a) => some (MajCtrl.simQ j q' tally off,
          Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then a else T.head t)
      | some (q', .move d) => some (MajCtrl.simQ j q' tally (dirShift off d),
          Turing.TM0.Stmt.move d)
      | none => some (MajCtrl.tallyH j tally (acceptM q) off, Turing.TM0.Stmt.write T.head))
      = some (match M c q (T.head (runTrackIdx r j)) with
        | some (q', .write a) => (MajCtrl.simQ j q' tally off,
            Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then a else T.head t)
        | some (q', .move d) => (MajCtrl.simQ j q' tally (dirShift off d),
            Turing.TM0.Stmt.move d)
        | none => (MajCtrl.tallyH j tally (acceptM q) off, Turing.TM0.Stmt.write T.head)) := by
  cases M c q (T.head (runTrackIdx r j)) with
  | none => rfl
  | some p =>
    rcases p with ⟨q', stmt⟩
    cases stmt <;> rfl

/-- A successful component step has a corresponding majority-machine step preserving the
selected working track; its offset stays fixed or changes by one tape move. -/
theorem maj_sim_step_some {Q r : ℕ}
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (acceptM : Fin (Q + 1) → Bool) (j : Fin (2 * r + 1)) (q : Fin (Q + 1))
    (tally : ℕ) (off : ℤ) (T : Turing.Tape (Tracks (2 * r + 2)))
    (T_d : Turing.Tape (Option Bool)) (c : Bool) (q' : Fin (Q + 1))
    (stmt : Turing.TM0.Stmt (Option Bool))
    (hcorr : ∀ i : ℤ, (T.nth i) (runTrackIdx r j) = T_d.nth i)
    (hM : M c q T_d.head = some (q', stmt)) :
    ∃ (off' : ℤ) (T' : Turing.Tape (Tracks (2 * r + 2)))
      (T_d' : Turing.TM0.Cfg (Option Bool) (Fin (Q + 1))),
      Turing.TM0.step (majorityTable Q r M acceptM c)
          (⟨.simQ j q tally off, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.simQ j q' tally off', T'⟩) ∧
      Turing.TM0.step (M c) (⟨q, T_d⟩ : Turing.TM0.Cfg (Option Bool) (Fin (Q + 1)))
        = some T_d' ∧ T_d'.q = q' ∧
      (∀ i : ℤ, (T'.nth i) (runTrackIdx r j) = T_d'.Tape.nth i) ∧
      (off' = off ∨ off' = dirShift off Turing.Dir.left ∨ off' = dirShift off Turing.Dir.right) := by
  have hsym : T.head (runTrackIdx r j) = T_d.head := by
    rw [← Turing.Tape.nth_zero T, ← Turing.Tape.nth_zero T_d]
    exact hcorr 0
  have htab : M c q (T.head (runTrackIdx r j)) = some (q', stmt) := by
    rw [hsym, hM]
  cases stmt with
  | write a =>
    have h2 : majorityTable Q r M acceptM c (.simQ j q tally off) T.head
        = some (MajCtrl.simQ j q' tally off,
          Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then a else T.head t) := by
      show (match M c q (T.head (runTrackIdx r j)) with
        | some (q'', .write a') => some (MajCtrl.simQ j q'' tally off,
            Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then a' else T.head t)
        | some (q'', .move d') => some (MajCtrl.simQ j q'' tally (dirShift off d'),
            Turing.TM0.Stmt.move d')
        | none => some (MajCtrl.tallyH j tally (acceptM q) off, Turing.TM0.Stmt.write T.head))
          = some (MajCtrl.simQ j q' tally off,
            Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then a else T.head t)
      rw [htab]
    have hstep : Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.simQ j q tally off, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.simQ j q' tally off,
          T.write fun t => if t = runTrackIdx r j then a else T.head t⟩) :=
      TM0_step_eq_some (majorityTable Q r M acceptM c)
        (⟨.simQ j q tally off, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _ h2
    have hstepD : Turing.TM0.step (M c) (⟨q, T_d⟩ : Turing.TM0.Cfg (Option Bool) (Fin (Q + 1)))
        = some (⟨q', T_d.write a⟩) :=
      TM0_step_eq_some (M c) (⟨q, T_d⟩ : Turing.TM0.Cfg (Option Bool) (Fin (Q + 1))) _ _ hM
    refine ⟨off, T.write (fun t => if t = runTrackIdx r j then a else T.head t),
      ⟨q', T_d.write a⟩, hstep, hstepD, rfl, ?_, Or.inl rfl⟩
    intro i
    show ((T.write (fun t => if t = runTrackIdx r j then a else T.head t)).nth i)
        (runTrackIdx r j) = (T_d.write a).nth i
    by_cases hi : i = 0
    · subst hi
      show (if runTrackIdx r j = runTrackIdx r j then a else T.head (runTrackIdx r j)) = a
      rw [if_pos rfl]
    · simp only [Turing.Tape.write_nth, if_neg hi]
      exact hcorr i
  | move d =>
    have h2 : majorityTable Q r M acceptM c (.simQ j q tally off) T.head
        = some (MajCtrl.simQ j q' tally (dirShift off d), Turing.TM0.Stmt.move d) := by
      show (match M c q (T.head (runTrackIdx r j)) with
        | some (q'', .write a') => some (MajCtrl.simQ j q'' tally off,
            Turing.TM0.Stmt.write fun t => if t = runTrackIdx r j then a' else T.head t)
        | some (q'', .move d') => some (MajCtrl.simQ j q'' tally (dirShift off d'),
            Turing.TM0.Stmt.move d')
        | none => some (MajCtrl.tallyH j tally (acceptM q) off, Turing.TM0.Stmt.write T.head))
          = some (MajCtrl.simQ j q' tally (dirShift off d), Turing.TM0.Stmt.move d)
      rw [htab]
    have hstep : Turing.TM0.step (majorityTable Q r M acceptM c)
        (⟨.simQ j q tally off, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r))
        = some (⟨.simQ j q' tally (dirShift off d), T.move d⟩) :=
      TM0_step_eq_some (majorityTable Q r M acceptM c)
        (⟨.simQ j q tally off, T⟩ : Turing.TM0.Cfg (Tracks (2 * r + 2)) (MajCtrl Q r)) _ _ h2
    have hstepD : Turing.TM0.step (M c) (⟨q, T_d⟩ : Turing.TM0.Cfg (Option Bool) (Fin (Q + 1)))
        = some (⟨q', T_d.move d⟩) :=
      TM0_step_eq_some (M c) (⟨q, T_d⟩ : Turing.TM0.Cfg (Option Bool) (Fin (Q + 1))) _ _ hM
    refine ⟨dirShift off d, T.move d, ⟨q', T_d.move d⟩, hstep, hstepD, rfl, ?_, ?_⟩
    · intro i
      show ((T.move d).nth i) (runTrackIdx r j) = (T_d.move d).nth i
      cases d with
      | left =>
        rw [Turing.Tape.move_left_nth T i, Turing.Tape.move_left_nth T_d i]
        exact hcorr (i - 1)
      | right =>
        rw [Turing.Tape.move_right_nth T i, Turing.Tape.move_right_nth T_d i]
        exact hcorr (i + 1)
    · cases d <;> simp [dirShift] <;> tauto

end Qatlib.Concepts.AdversaryBounds.AdvDuality
