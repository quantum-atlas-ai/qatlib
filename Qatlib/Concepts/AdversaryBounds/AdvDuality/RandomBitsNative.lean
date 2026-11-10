/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.ClassicalTape.FairCoinTape

open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open NativeTape
open scoped ENNReal

private theorem head_cons (L : List Symbol) (a : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ L (a::R)).head = a := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.ListBlank.head_mk]

private theorem head_nil (L : List Symbol) : (Turing.Tape.mk₂ L []).head = .blank := rfl

private theorem run_done (n : ℕ) (bs : List Bool) (T : Turing.Tape Symbol) :
    run program n bs ⟨.done, T⟩ = ⟨⟨.done, T⟩, bs, .halted, []⟩ := by
  cases n <;> simp [run, program]

private theorem tape_write (L : List Symbol) (a b : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ L (a::R)).write b = Turing.Tape.mk₂ L (b::R) := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]

private theorem tape_right (L : List Symbol) (a : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ L (a::R)).move .right = Turing.Tape.mk₂ (a::L) R := by
  simp [Turing.Tape.mk₂, Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]

private theorem tape_left (L : List Symbol) (a : Symbol) (R : List Symbol) :
    (Turing.Tape.mk₂ (a::L) R).move .left = Turing.Tape.mk₂ L (a::R) := by
  simp [Turing.Tape.mk₂, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]

theorem alphabet_control_size : Fintype.card Symbol = 9 ∧ Fintype.card Control = 3 := by
  decide

theorem inputWord_length (a b : ℕ) (h : 0 < a+b) :
    (inputWord a b).length = a+b+1 := by
  cases a <;> cases b <;> simp_all [inputWord]
  all_goals omega

theorem position_left (a b : ℕ) :
    (positionTape (a+1) (b+1)).move .left = positionTape a (b+2) := by
  cases a <;> simp [positionTape, List.replicate_succ, tape_left]

theorem position_right (a b : ℕ) :
    (positionTape (a+1) (b+1)).move .right = positionTape (a+2) b := by
  cases b <;> simp [positionTape, List.replicate_succ, tape_right]

theorem load_prefix (xs L R : List Symbol) (bs : List Bool)
    (h : ∀ x ∈ xs, x = .left ∨ x = .cell) :
    let r := run program (xs.length+1) bs
      ⟨.load, Turing.Tape.mk₂ L (xs ++ .start :: R)⟩
    r.cfg = ⟨.walk, Turing.Tape.mk₂ (xs.reverse ++ L) (.cell::R)⟩ ∧
      r.unread = bs ∧ r.bits = [] ∧ r.steps = xs.length+1 := by
  induction xs generalizing L with
  | nil =>
      simp [run, head_cons, program, advance, TM0StmtApply, tape_write,
        Result.prepend, Result.bits, Result.steps]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (x::L) (fun y hy => h y (by simp [hy]))
      rcases hx with rfl | rfl <;>
        simpa [run, head_cons, program, advance, TM0StmtApply, tape_right,
          Result.prepend, Result.bits, Result.steps, List.reverse_cons,
          List.append_assoc, Nat.add_comm] using! ht

theorem load_positive (a b : ℕ) (bs : List Bool) :
    let r := run program (a+2) bs (input (a+1) (b+1))
    r.cfg = loaded (a+1) (b+1) ∧ r.unread = bs ∧ r.bits = [] ∧ r.steps = a+2 := by
  have h := load_prefix (.left :: List.replicate a .cell) []
    (List.replicate b .cell ++ [.right]) bs (by simp)
  simpa [input, inputWord, Turing.Tape.mk₁, loaded, positionTape,
    List.reverse_cons, List.reverse_replicate, List.append_assoc] using! h

theorem run_walk (n : ℕ) (bs : List Bool) (a b : ℕ) :
    let r := run program n bs (loaded a b)
    let z := walk n bs a b
    r.cfg = z.cfg ∧ r.stop = z.stop ∧ r.unread = z.unread ∧
      r.bits = z.bits ∧ r.steps = z.steps := by
  induction n generalizing bs a b with
  | zero =>
      cases a <;> cases b <;>
        simp [run, loaded, positionTape, head_cons, head_nil, program, walk,
          WalkResult.cfg, Result.bits, Result.steps]
  | succ n ih =>
      cases a with
      | zero =>
          cases b <;>
            simp [run, loaded, positionTape, head_cons, head_nil, program, walk, advance,
              TM0StmtApply, tape_write, run_done, WalkResult.cfg, outputSymbol,
              Result.prepend, Result.bits, Result.steps]
      | succ a =>
          cases b with
          | zero =>
              simp [run, loaded, positionTape, head_cons, program, walk, advance,
                TM0StmtApply, tape_write, run_done, WalkResult.cfg, outputSymbol,
                Result.prepend, Result.bits, Result.steps]
          | succ b =>
              cases bs with
              | nil =>
                  simp [run, loaded, positionTape, head_cons, program, walk,
                    WalkResult.cfg, Result.bits, Result.steps]
              | cons bit bs =>
                  have hh : (positionTape (a+1) (b+1)).head = .cell := by
                    simp [positionTape, head_cons]
                  cases bit
                  · simpa [run, loaded, hh, program, advance, TM0StmtApply,
                      position_left, position_right, walk, WalkResult.prependBit,
                      WalkResult.cfg, Result.prepend, Result.bits, Result.steps,
                      Nat.add_comm] using! ih bs a (b+2)
                  · simpa [run, loaded, hh, program, advance, TM0StmtApply,
                      position_left, position_right, walk, WalkResult.prependBit,
                      WalkResult.cfg, Result.prepend, Result.bits, Result.steps,
                      Nat.add_comm] using! ih bs (a+2) b

theorem walk_total (n : ℕ) (bs : List Bool) (a b : ℕ) :
    (walk n bs a b).left + (walk n bs a b).right = a+b := by
  induction n generalizing bs a b with
  | zero => cases a <;> cases b <;> rfl
  | succ n ih =>
      cases a <;> cases b <;> try rfl
      cases bs with
      | nil => rfl
      | cons bit bs =>
          cases bit <;> simp only [walk, Bool.false_eq_true, ↓reduceIte,
            WalkResult.prependBit] <;> rw [ih] <;> omega

theorem walk_clock (n : ℕ) (bs : List Bool) (a b : ℕ) :
    (walk n bs a b).steps = (walk n bs a b).bits.length +
      (if (walk n bs a b).out.isSome then 1 else 0) := by
  induction n generalizing bs a b with
  | zero => cases a <;> cases b <;> rfl
  | succ n ih =>
      cases a <;> cases b <;> try rfl
      cases bs with
      | nil => rfl
      | cons bit bs =>
          cases bit <;> simp only [walk, Bool.false_eq_true, ↓reduceIte,
            WalkResult.prependBit, List.length_cons] <;> rw [ih] <;> omega

theorem walk_output_boundary (n : ℕ) (bs : List Bool) (a b : ℕ) :
    ((walk n bs a b).out = some false → (walk n bs a b).left = 0) ∧
    ((walk n bs a b).out = some true → (walk n bs a b).right = 0) := by
  induction n generalizing bs a b with
  | zero => cases a <;> cases b <;> simp [walk]
  | succ n ih =>
      cases a <;> cases b <;> try simp only [walk]
      · simp
      · simp
      · simp
      · cases bs with
        | nil => simp [walk]
        | cons bit bs =>
            cases bit <;> simpa [WalkResult.prependBit] using! ih bs _ _

theorem walk_output_halted (n : ℕ) (bs : List Bool) (a b : ℕ) :
    (walk n bs a b).out.isSome = true → (walk n bs a b).stop = .halted := by
  induction n generalizing bs a b with
  | zero => cases a <;> cases b <;> simp [walk]
  | succ n ih =>
      cases a <;> cases b <;> try simp only [walk]
      · simp
      · simp
      · simp
      · cases bs with
        | nil => simp [walk]
        | cons bit bs =>
            cases bit <;> simpa [WalkResult.prependBit] using! ih bs _ _

theorem load_positive_fuel (a b : ℕ) (bs : List Bool) :
    (run program (a+2) bs (input (a+1) (b+1))).stop = .fuel := by
  apply (run_fuel_iff _ _ _ _).mpr
  have h := load_positive a b bs
  dsimp only at h
  refine ⟨h.2.2.2, ?_⟩
  rw [h.1]
  simp [loaded, positionTape, head_cons, program]

theorem run_positive (a b n : ℕ) (bs : List Bool) :
    let r := run program (a+2+n) bs (input (a+1) (b+1))
    let z := walk n bs (a+1) (b+1)
    r.cfg = z.cfg ∧ r.stop = z.stop ∧ r.unread = z.unread ∧
      r.bits = z.bits ∧ r.steps = a+2+z.steps := by
  have hl := load_positive a b bs
  have hs := load_positive_fuel a b bs
  have hw := run_walk n bs (a+1) (b+1)
  dsimp only at hl hw ⊢
  rw [run_add]
  simp only [resume, hs, ↓reduceIte, hl.1, hl.2.1]
  refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_, ?_⟩
  · simp only [Result.bits, List.filterMap_append]
    change (run program (a+2) bs (input (a+1) (b+1))).bits ++
        (run program n bs (loaded (a+1) (b+1))).bits = _
    rw [hl.2.2.1, List.nil_append, hw.2.2.2.1]
  · simp only [Result.steps, List.length_append]
    change (run program (a+2) bs (input (a+1) (b+1))).steps +
        (run program n bs (loaded (a+1) (b+1))).steps = _
    rw [hl.2.2.2, hw.2.2.2.2]

theorem run_walk_output (n : ℕ) (bs : List Bool) (a b : ℕ) :
    output (run program n bs (loaded a b)) = (walk n bs a b).out := by
  have h := run_walk n bs a b
  dsimp only at h
  cases ho : (walk n bs a b).out with
  | none =>
      have hc : (run program n bs (loaded a b)).cfg = loaded
          (walk n bs a b).left (walk n bs a b).right := by
        rw [h.1, WalkResult.cfg, ho]
      rw [output, hc]
      simp [loaded]
  | some bit =>
      have hs := walk_output_halted n bs a b (by simp [ho])
      have hc : (run program n bs (loaded a b)).cfg =
          ⟨.done, (positionTape (walk n bs a b).left
            (walk n bs a b).right).write (outputSymbol bit)⟩ := by
        rw [h.1, WalkResult.cfg, ho]
      rw [output, hc, h.2.1, hs]
      cases bit <;> simp [outputSymbol, Turing.Tape.write]

theorem positive_clock (a b n : ℕ) (bs : List Bool) :
    let r := run program (a+2+n) bs (input (a+1) (b+1))
    r.steps = a+2+r.bits.length + (if (walk n bs (a+1) (b+1)).out.isSome then 1 else 0) := by
  have h := run_positive a b n bs
  dsimp only at h ⊢
  rw [h.2.2.2.2, h.2.2.2.1, walk_clock]
  omega

theorem walk_cursor_bounds (n : ℕ) (bs : List Bool) (a b : ℕ) :
    ∀ p ∈ cursorTrace program (a : ℤ) (run program n bs (loaded a b)).trace,
      0 ≤ p ∧ p ≤ (a+b : ℕ) := by
  induction n generalizing bs a b with
  | zero =>
      cases a <;> cases b <;>
        simp [run, loaded, positionTape, head_cons, head_nil, program, cursorTrace] <;> omega
  | succ n ih =>
      cases a with
      | zero =>
          cases b <;>
            simp [run, loaded, positionTape, head_cons, head_nil, program, advance,
              TM0StmtApply, tape_write, run_done, Result.prepend, cursorTrace,
              tickDisplacement, table, statementDisplacement]
          all_goals omega
      | succ a =>
          cases b with
          | zero =>
              simp [run, loaded, positionTape, head_cons, program, advance,
                TM0StmtApply, tape_write, run_done, Result.prepend, cursorTrace,
                tickDisplacement, table, statementDisplacement]
              omega
          | succ b =>
              have hh : (positionTape (a+1) (b+1)).head = .cell := by
                simp [positionTape, head_cons]
              cases bs with
              | nil =>
                  simp [run, loaded, hh, program, cursorTrace]
                  constructor <;> omega
              | cons bit bs =>
                  cases bit
                  · simp only [run, loaded, hh, program, Bool.false_eq_true, ↓reduceIte,
                      advance, TM0StmtApply, position_left, Result.prepend]
                    intro p hp
                    have hp' : p = (a+1 : ℕ) ∨
                        p ∈ cursorTrace program (a : ℤ)
                          (run program n bs (loaded a (b+2))).trace := by
                      simpa [cursorTrace, tickDisplacement, table, loaded, hh,
                        program, statementDisplacement] using! hp
                    rcases hp' with rfl | hp'
                    · constructor <;> omega
                    · have hi := ih bs a (b+2) p hp'; constructor <;> omega
                  · simp only [run, loaded, hh, program, ↓reduceIte, advance,
                      TM0StmtApply, position_right, Result.prepend]
                    intro p hp
                    have hp' : p = (a+1 : ℕ) ∨
                        p ∈ cursorTrace program ((a+2 : ℕ) : ℤ)
                          (run program n bs (loaded (a+2) b)).trace := by
                      simpa [cursorTrace, tickDisplacement, table, loaded, hh,
                        program, statementDisplacement, add_assoc] using! hp
                    rcases hp' with rfl | hp'
                    · constructor <;> omega
                    · have hi := ih bs (a+2) b p hp'; constructor <;> omega

theorem walk_workspace_card (n : ℕ) (bs : List Bool) (a b : ℕ) :
    (workspace a b (run program n bs (loaded a b)).trace).card = a+b+1 := by
  have hsub : (cursorTrace program (a : ℤ) (run program n bs (loaded a b)).trace).toFinset ⊆
      (Finset.range (a+b+1)).image (fun i : ℕ => (i : ℤ)) := by
    intro p hp
    have h := walk_cursor_bounds n bs a b p (List.mem_toFinset.mp hp)
    refine Finset.mem_image.mpr ⟨p.toNat, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · exact Int.toNat_of_nonneg h.1
  rw [workspace, Finset.union_eq_left.mpr hsub, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro x y h; exact Int.ofNat_inj.mp h

theorem cycleWord_length (k : ℕ) : (cycleWord k).length = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [cycleWord, ih]; omega

theorem walk_cycle (k : ℕ) :
    walk (2*k) (cycleWord k) 1 2 = ⟨1, 2, none, .fuel, [], cycleWord k, 2*k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2*(k+1) = (2*k+1)+1 by omega]
      simp [cycleWord, walk, ih, WalkResult.prependBit]

theorem native_cycle_mass (k : ℕ) :
    (1/2 : ℝ≥0∞)^(2*k) ≤ nativeLaw 1 2 (2+2*k) (none, .fuel, 2+2*k, 2*k) := by
  have h := run_positive 0 1 (2*k) (cycleWord k)
  dsimp only at h
  rw [walk_cycle] at h
  have ho : observation (run program (2+2*k) (cycleWord k) (input 1 2)) =
      (none, .fuel, 2+2*k, 2*k) := by
    simp only [observation, output, h.2.1, reduceCtorEq, false_and, ↓reduceIte,
      h.2.2.2.1, cycleWord_length, h.2.2.2.2]
  have hm := mass_le_map (law program (2+2*k) (input 1 2)) observation
    (run program (2+2*k) (cycleWord k) (input 1 2))
  rw [ho] at hm
  have hl := law_run_lower program (2+2*k) (cycleWord k) (input 1 2)
    (by rw [h.2.1]; simp) h.2.2.1
  rw [cycleWord_length] at hl
  exact hl.trans hm

end Qatlib.Concepts.AdversaryBounds.AdvDuality
