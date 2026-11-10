/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilisticDefs
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Mathlib.Data.List.TakeWhile
import Qatlib.Concepts.ClassicalTape.FairCoinTape
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.FairCoinTape
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

open Turing

theorem getI_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (x : ℕ) :
    (l.map f).getI x = if x < l.length then f (l.getI x) else default := by
  by_cases h : x < l.length
  · have hlen : x < (l.map f).length := by simpa using h
    rw [if_pos h, List.getI_eq_getElem (l.map f) hlen, List.getElem_map,
      List.getI_eq_getElem l h]
  · have h2 : (l.map f).length ≤ x := by simpa using h
    rw [if_neg h, List.getI_eq_default (l.map f) h2]

theorem tape_ext {Γ : Type} [Inhabited Γ] {T₁ T₂ : Turing.Tape Γ}
    (h : ∀ i : ℤ, T₁.nth i = T₂.nth i) : T₁ = T₂ := by
  obtain ⟨a₁, l₁, r₁⟩ := T₁
  obtain ⟨a₂, l₂, r₂⟩ := T₂
  have ha : a₁ = a₂ := by simpa using h 0
  have hl : l₁ = l₂ := by
    refine Turing.ListBlank.ext (fun n => ?_)
    exact h (Int.negSucc n)
  have hr : r₁ = r₂ := by
    refine Turing.ListBlank.ext (fun n => ?_)
    exact h (n + 1 : ℕ)
  rw [ha, hl, hr]

theorem init_nth_ofNat {Γ : Type} [Inhabited Γ] {Λ : Type} [Inhabited Λ]
    (l : List Γ) (i : ℕ) :
    (Turing.TM0.init l : Turing.TM0.Cfg Γ Λ).Tape.nth (Int.ofNat i) = l.getI i := by
  have h := Turing.Tape.mk'_nth_nat (Γ := Γ) (ListBlank.mk ([] : List Γ)) (ListBlank.mk l) i
  have h2 : (Turing.TM0.init l : Turing.TM0.Cfg Γ Λ).Tape.nth (Int.ofNat i)
      = (Turing.Tape.mk' (ListBlank.mk ([] : List Γ)) (ListBlank.mk l)).nth (i : ℤ) := rfl
  rw [h2, h, Turing.ListBlank.nth_mk]

theorem init_nth_negSucc {Γ : Type} [Inhabited Γ] {Λ : Type} [Inhabited Λ]
    (l : List Γ) (n : ℕ) :
    (Turing.TM0.init l : Turing.TM0.Cfg Γ Λ).Tape.nth (Int.negSucc n) = default := by
  show (Turing.Tape.mk' (ListBlank.mk ([] : List Γ)) (ListBlank.mk l)).nth (Int.negSucc n) = _
  rfl

theorem init_nth {Γ : Type} [Inhabited Γ] {Λ : Type} [Inhabited Λ]
    (l : List Γ) (x : ℤ) :
    (Turing.TM0.init l : Turing.TM0.Cfg Γ Λ).Tape.nth x =
      if x < 0 then default else l.getI x.toNat := by
  cases x with
  | ofNat n =>
    rw [init_nth_ofNat]
    simp [Int.toNat_natCast]
  | negSucc n => rw [init_nth_negSucc]; simp

def runFrom {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) :
    ℕ → Turing.TM0.Cfg Γ Λ → Option (Turing.TM0.Cfg Γ Λ)
  | 0, cfg => some cfg
  | t + 1, cfg => (runFrom M t cfg).bind (Turing.TM0.step M)

theorem bitMachineAfter_eq_runFrom {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (input : List Γ) (t : ℕ) :
    BitMachineAfter M input t = runFrom M t (Turing.TM0.init input) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [BitMachineAfter, ih]; rfl

theorem runFrom_add {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ) :
    ∀ (a b : ℕ) (cfg : Turing.TM0.Cfg Γ Λ),
      runFrom M (a + b) cfg = (runFrom M a cfg).bind (runFrom M b) := by
  intro a b
  induction b with
  | zero => intro cfg; simp [runFrom]
  | succ b ih =>
    intro cfg
    have h1 : runFrom M (a + (b + 1)) cfg
        = (runFrom M (a + b) cfg).bind (Turing.TM0.step M) := by
      rw [Nat.add_succ]
      rfl
    rw [h1, ih, Option.bind_assoc]
    rfl

theorem runFrom_one {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ)
    (cfg : Turing.TM0.Cfg Γ Λ) :
    runFrom M 1 cfg = Turing.TM0.step M cfg := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, runFrom_add]
  simp [runFrom]

theorem runFrom_add1 {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ)
    (a : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    runFrom M (a + 1) cfg = (runFrom M a cfg).bind (Turing.TM0.step M) := by
  rw [runFrom_add]
  rfl

theorem twoTrackBitEncode_getI (input : List Bool) (x : ℕ) :
    (twoTrackBitEncode input).getI x =
      if x < input.length then (fun t => if t.val = 0 then some (input.getI x) else none)
      else default := by
  unfold twoTrackBitEncode tracksEncode
  rw [getI_map]

theorem bothTrackEncode_getI (input : List Bool) (x : ℕ) :
    (bothTrackEncode input).getI x =
      if x < input.length then (fun _ => some (input.getI x)) else default := by
  unfold bothTrackEncode
  rw [getI_map]

def copyContent (input : List Bool) (pos : ℕ) (x : ℤ) : Tracks 2 :=
  if x < 0 then default
  else if x < (pos : ℤ) then (fun _ => some (input.getI x.toNat))
  else (twoTrackBitEncode input).getI x.toNat

theorem copyContent_zero (input : List Bool) (x : ℤ) :
    copyContent input 0 x =
      if x < 0 then default else (twoTrackBitEncode input).getI x.toNat := by
  unfold copyContent
  split_ifs <;> first | rfl | omega

theorem copyContent_copied (input : List Bool) (pos : ℕ) {x : ℤ} (h : x < (pos : ℤ)) :
    copyContent input pos x =
      if x < 0 then default else (fun _ => some (input.getI x.toNat)) := by
  unfold copyContent
  split_ifs <;> first | rfl | omega

theorem copyContent_uncopied (input : List Bool) (pos : ℕ) {x : ℤ} (h : (pos : ℤ) ≤ x) :
    copyContent input pos x = (twoTrackBitEncode input).getI x.toNat := by
  unfold copyContent
  split_ifs <;> first | rfl | omega

theorem copyContent_succ (input : List Bool) (pos : ℕ) (x : ℤ) :
    copyContent input (pos + 1) x =
      if x = (pos : ℤ) then (fun _ => some (input.getI pos))
      else copyContent input pos x := by
  by_cases he : x = (pos : ℤ)
  · subst he
    rw [if_pos rfl]
    have h1 : copyContent input (pos + 1) ((pos : ℤ)) = (fun _ => some (input.getI pos)) := by
      rw [copyContent_copied input (pos + 1) (show (pos : ℤ) < ((pos + 1 : ℕ) : ℤ) from by omega),
        if_neg (show ¬((pos : ℤ) < 0) from by omega)]
      rfl
    exact h1
  · rw [if_neg he]
    by_cases h : x < (pos : ℤ)
    · have h2 : x < ((pos + 1 : ℕ) : ℤ) := by omega
      rw [copyContent_copied _ _ h, copyContent_copied _ _ h2]
    · have h3 : (pos : ℤ) ≤ x := by omega
      have h4 : ((pos + 1 : ℕ) : ℤ) ≤ x := by omega
      rw [copyContent_uncopied _ _ h3, copyContent_uncopied _ _ h4]

theorem copyContent_end (input : List Bool) (x : ℤ) :
    copyContent input input.length x =
      if x < 0 then default else (bothTrackEncode input).getI x.toNat := by
  by_cases hx : x < 0
  · rw [copyContent_copied input input.length
        (Int.lt_of_lt_of_le hx (Int.natCast_nonneg input.length)), if_pos hx, if_pos hx]
  · have hne : 0 ≤ x := Int.le_of_not_gt hx
    by_cases h2 : x.toNat < input.length
    · have h3 : x < (input.length : ℤ) := by
        rw [← Int.toNat_of_nonneg hne]
        exact_mod_cast h2
      rw [copyContent_copied input input.length h3, if_neg hx, if_neg hx,
        bothTrackEncode_getI, if_pos h2]
    · have h3 : (input.length : ℤ) ≤ x := by
        rw [← Int.toNat_of_nonneg hne]
        exact_mod_cast Nat.le_of_not_lt h2
      rw [copyContent_uncopied input input.length h3, if_neg hx, twoTrackBitEncode_getI,
        bothTrackEncode_getI, if_neg h2, if_neg h2]

theorem copyContent_head (input : List Bool) (pos : ℕ) (hpos : pos < input.length) :
    copyContent input pos (pos : ℤ) =
      (fun t => if t.val = 0 then some (input.getI pos) else none) := by
  rw [copyContent_uncopied input pos (show (pos : ℤ) ≤ (pos : ℤ) from le_rfl),
    twoTrackBitEncode_getI, Int.toNat_natCast, if_pos hpos]

theorem copyContent_head_end (input : List Bool) :
    copyContent input input.length (input.length : ℤ) = (fun _ => none) := by
  rw [copyContent_uncopied input input.length (show (input.length : ℤ) ≤ (input.length : ℤ) from le_rfl),
    Int.toNat_natCast, twoTrackBitEncode_getI, if_neg (Nat.lt_irrefl input.length)]
  rfl

theorem copy_write_cell (input : List Bool) (pos : ℕ) :
    (fun t : Fin 2 => if t.val = 1 then some (input.getI pos)
      else (fun t => if t.val = 0 then some (input.getI pos) else none) t)
      = (fun _ => some (input.getI pos)) := by
  funext t
  fin_cases t <;> rfl

theorem copy_step_cw {input : List Bool} {pos : ℕ} (hpos : pos < input.length)
    (cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
    (hq : cfg.q = CopyCtrl.cw pos)
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = copyContent input pos ((pos : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      Turing.TM0.step copyMachineTable cfg = some cfg' ∧
      cfg'.q = CopyCtrl.cm pos ∧
      ∀ i : ℤ, cfg'.Tape.nth i = copyContent input (pos + 1) ((pos : ℤ) + i) := by
  have hsym : cfg.Tape.head = (fun t => if t.val = 0 then some (input.getI pos) else none) := by
    rw [← Turing.Tape.nth_zero, hnth, Int.add_zero]
    exact copyContent_head input pos hpos
  have htab : copyMachineTable cfg.q cfg.Tape.head
      = some (CopyCtrl.cm pos,
          Turing.TM0.Stmt.write fun t => if t.val = 1 then some (input.getI pos)
            else (fun t => if t.val = 0 then some (input.getI pos) else none) t) := by
    rw [hq, hsym]
    rfl
  refine ⟨⟨CopyCtrl.cm pos, cfg.Tape.write
      (fun t => if t.val = 1 then some (input.getI pos)
        else (fun t => if t.val = 0 then some (input.getI pos) else none) t)⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some copyMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.write_nth, copyContent_succ]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos (show (0 : ℤ) = 0 from rfl),
        if_pos (show ((pos : ℤ) + 0) = (pos : ℤ) from rfl)]
      exact copy_write_cell input pos
    · rw [if_neg hi]
      have h1 : ((pos : ℤ) + i) ≠ (pos : ℤ) := by omega
      rw [if_neg h1, hnth]

theorem copy_step_cm {input : List Bool} {pos : ℕ}
    (cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
    (hq : cfg.q = CopyCtrl.cm pos)
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = copyContent input (pos + 1) ((pos : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      Turing.TM0.step copyMachineTable cfg = some cfg' ∧
      cfg'.q = CopyCtrl.cw (pos + 1) ∧
      ∀ i : ℤ, cfg'.Tape.nth i = copyContent input (pos + 1) (((pos + 1 : ℕ) : ℤ) + i) := by
  have htab : copyMachineTable cfg.q cfg.Tape.head
      = some (CopyCtrl.cw (pos + 1), Turing.TM0.Stmt.move Turing.Dir.right) := by
    rw [hq]
    rfl
  refine ⟨⟨CopyCtrl.cw (pos + 1), cfg.Tape.move Turing.Dir.right⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some copyMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.move_right_nth, hnth]
    congr 1
    omega

theorem copy_step_cw_end (input : List Bool)
    (cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
    (hq : cfg.q = CopyCtrl.cw input.length)
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = copyContent input input.length ((input.length : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      Turing.TM0.step copyMachineTable cfg = some cfg' ∧
      cfg'.q = CopyCtrl.ch input.length ∧
      ∀ i : ℤ, cfg'.Tape.nth i = copyContent input input.length ((input.length : ℤ) + i) := by
  have hsym : cfg.Tape.head = (fun _ => none) := by
    rw [← Turing.Tape.nth_zero, hnth, Int.add_zero]
    exact copyContent_head_end input
  have htab : copyMachineTable cfg.q cfg.Tape.head
      = some (CopyCtrl.ch input.length, Turing.TM0.Stmt.write (fun _ => none)) := by
    rw [hq, hsym]
    rfl
  refine ⟨⟨CopyCtrl.ch input.length, cfg.Tape.write (fun _ => none)⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some copyMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.write_nth]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos (show (0 : ℤ) = 0 from rfl)]
      rw [Int.add_zero, copyContent_head_end]
    · rw [if_neg hi, hnth]

theorem copy_step_ch {input : List Bool} {pos : ℕ}
    (cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
    (hq : cfg.q = CopyCtrl.ch (pos + 1))
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = copyContent input input.length (((pos + 1 : ℕ) : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      Turing.TM0.step copyMachineTable cfg = some cfg' ∧
      cfg'.q = CopyCtrl.ch pos ∧
      ∀ i : ℤ, cfg'.Tape.nth i = copyContent input input.length ((pos : ℤ) + i) := by
  have htab : copyMachineTable cfg.q cfg.Tape.head
      = some (CopyCtrl.ch pos, Turing.TM0.Stmt.move Turing.Dir.left) := by
    rw [hq]
    rfl
  refine ⟨⟨CopyCtrl.ch pos, cfg.Tape.move Turing.Dir.left⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some copyMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.move_left_nth, hnth]
    congr 1
    omega

theorem copy_step_ch0 (input : List Bool)
    (cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
    (hq : cfg.q = CopyCtrl.ch 0) :
    Turing.TM0.step copyMachineTable cfg = none := by
  rw [Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_none, hq]
  rfl

theorem copy_step_ch_ne_none
    (cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
    (hq : cfg.q = CopyCtrl.ch 1) :
    Turing.TM0.step copyMachineTable cfg ≠ none := by
  intro h
  rw [Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_none, hq] at h
  have h2 : copyMachineTable (CopyCtrl.ch 1) cfg.Tape.head
      = some (CopyCtrl.ch 0, Turing.TM0.Stmt.move Turing.Dir.left) := rfl
  rw [h2] at h
  nomatch h

theorem copy_init_step_ne_none (input : List Bool) :
    Turing.TM0.step copyMachineTable
      (Turing.TM0.init (twoTrackBitEncode input) : Turing.TM0.Cfg (Tracks 2) CopyCtrl) ≠ none := by
  cases input with
  | nil =>
    intro h
    have h2 : Turing.TM0.step copyMachineTable
        (Turing.TM0.init (twoTrackBitEncode []) : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
        = some ⟨CopyCtrl.ch 0,
            (Turing.TM0.init (twoTrackBitEncode []) : Turing.TM0.Cfg (Tracks 2) CopyCtrl).Tape.write
              (fun _ => none)⟩ := rfl
    rw [h2] at h
    nomatch h
  | cons b input' =>
    intro h
    have h2 : Turing.TM0.step copyMachineTable
        (Turing.TM0.init (twoTrackBitEncode (b :: input')) : Turing.TM0.Cfg (Tracks 2) CopyCtrl)
        = some ⟨CopyCtrl.cm 0,
            (Turing.TM0.init (twoTrackBitEncode (b :: input')) : Turing.TM0.Cfg (Tracks 2) CopyCtrl).Tape.write
              (fun t => if t.val = 1 then some b else (fun t => if t.val = 0 then some b else none) t)⟩ := rfl
    rw [h2] at h
    nomatch h

theorem copy_cw_reach (input : List Bool) :
    ∀ pos ≤ input.length, ∃ cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      runFrom copyMachineTable (2 * pos) (Turing.TM0.init (twoTrackBitEncode input)) = some cfg ∧
      cfg.q = CopyCtrl.cw pos ∧
      ∀ i : ℤ, cfg.Tape.nth i = copyContent input pos ((pos : ℤ) + i) := by
  intro pos hpos
  induction pos with
  | zero =>
    refine ⟨Turing.TM0.init (twoTrackBitEncode input), rfl, rfl, ?_⟩
    intro i
    have hz : ((0 : ℕ) : ℤ) + i = i := by omega
    rw [init_nth, hz, copyContent_zero]
  | succ pos ih =>
    obtain ⟨cfg, hr, hq, hnth⟩ := ih (Nat.le_of_succ_le hpos)
    have hpos' : pos < input.length := Nat.lt_of_succ_le hpos
    obtain ⟨cfg₁, hs₁, hq₁, hn₁⟩ := copy_step_cw hpos' cfg hq hnth
    obtain ⟨cfg₂, hs₂, hq₂, hn₂⟩ := copy_step_cm cfg₁ hq₁ hn₁
    refine ⟨cfg₂, ?_, hq₂, hn₂⟩
    rw [show (2 * (pos + 1)) = (2 * pos + 1) + 1 from by omega]
    rw [runFrom_add1, runFrom_add1, hr]
    simp [hs₁, hs₂]

theorem copy_ch_reach (input : List Bool) :
    ∀ k ≤ input.length, ∃ cfg : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      runFrom copyMachineTable (2 * input.length + 1 + k)
        (Turing.TM0.init (twoTrackBitEncode input)) = some cfg ∧
      cfg.q = CopyCtrl.ch (input.length - k) ∧
      ∀ i : ℤ, cfg.Tape.nth i =
        copyContent input input.length (((input.length - k : ℕ) : ℤ) + i) := by
  intro k hk
  induction k with
  | zero =>
    obtain ⟨cfg, hr, hq, hnth⟩ := copy_cw_reach input input.length le_rfl
    obtain ⟨cfg₁, hs₁, hq₁, hn₁⟩ := copy_step_cw_end input cfg hq hnth
    refine ⟨cfg₁, ?_, hq₁, hn₁⟩
    rw [show (2 * input.length + 1 + 0) = 2 * input.length + 1 from by omega,
      runFrom_add1, hr]
    simp [hs₁]
  | succ k ih =>
    obtain ⟨cfg, hr, hq, hnth⟩ := ih (Nat.le_of_succ_le hk)
    have heq : input.length - k = (input.length - (k + 1)) + 1 := by omega
    rw [heq] at hq hnth
    obtain ⟨cfg₁, hs₁, hq₁, hn₁⟩ := copy_step_ch cfg hq hnth
    refine ⟨cfg₁, ?_, hq₁, hn₁⟩
    rw [show (2 * input.length + 1 + (k + 1)) = (2 * input.length + 1 + k) + 1 from by omega,
      runFrom_add1, hr]
    simp [hs₁]

theorem copy_final (input : List Bool) :
    ∃ final : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      BitMachineAfter copyMachineTable (twoTrackBitEncode input) (3 * input.length + 1) = some final ∧
      Turing.TM0.step copyMachineTable final = none ∧
      final.Tape =
        (Turing.TM0.init (bothTrackEncode input) : Turing.TM0.Cfg (Tracks 2) CopyCtrl).Tape := by
  obtain ⟨cfg, hr, hq, hnth⟩ := copy_ch_reach input input.length le_rfl
  have hrun : BitMachineAfter copyMachineTable (twoTrackBitEncode input) (3 * input.length + 1)
      = some cfg := by
    rw [bitMachineAfter_eq_runFrom]
    rw [show (3 * input.length + 1) = 2 * input.length + 1 + input.length from by omega]
    exact hr
  have hq' : cfg.q = CopyCtrl.ch 0 := by
    rw [show (input.length - input.length) = 0 from Nat.sub_self _] at hq
    exact hq
  have hnth' : ∀ i : ℤ, cfg.Tape.nth i = copyContent input input.length i := by
    intro i
    rw [hnth]
    congr 1
    rw [show (input.length - input.length : ℕ) = 0 from Nat.sub_self _]
    exact (by omega : ((0 : ℕ) : ℤ) + i = i)
  refine ⟨cfg, hrun, copy_step_ch0 input cfg hq', ?_⟩
  apply tape_ext
  intro i
  rw [hnth', copyContent_end, init_nth]

theorem copy_mid (input : List Bool) :
    ∃ mid : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      BitMachineAfter copyMachineTable (twoTrackBitEncode input) (3 * input.length) = some mid ∧
      Turing.TM0.step copyMachineTable mid ≠ none := by
  rcases Nat.eq_zero_or_pos input.length with h0 | hpos
  · refine ⟨Turing.TM0.init (twoTrackBitEncode input), ?_, copy_init_step_ne_none input⟩
    rw [bitMachineAfter_eq_runFrom, h0]
    rfl
  · obtain ⟨cfg, hr, hq, hnth⟩ := copy_ch_reach input (input.length - 1) (by omega)
    have hq' : cfg.q = CopyCtrl.ch 1 := by
      rw [show (input.length - (input.length - 1)) = 1 from by omega] at hq
      exact hq
    refine ⟨cfg, ?_, copy_step_ch_ne_none cfg hq'⟩
    rw [bitMachineAfter_eq_runFrom]
    rw [show (3 * input.length) = 2 * input.length + 1 + (input.length - 1) from by omega]
    exact hr

def resetContent (l : List (Tracks 2)) (pos : ℕ) (x : ℤ) : Tracks 2 :=
  if x < 0 then default
  else if x < (pos : ℤ) then (fun t => if t.val = 1 then none else (l.getI x.toNat) t)
  else l.getI x.toNat

theorem resetContent_zero (l : List (Tracks 2)) (x : ℤ) :
    resetContent l 0 x = if x < 0 then default else l.getI x.toNat := by
  unfold resetContent
  split_ifs <;> first | rfl | omega

theorem resetContent_processed (l : List (Tracks 2)) (pos : ℕ) {x : ℤ} (h : x < (pos : ℤ)) :
    resetContent l pos x =
      if x < 0 then default else (fun t => if t.val = 1 then none else (l.getI x.toNat) t) := by
  unfold resetContent
  split_ifs <;> first | rfl | omega

theorem resetContent_unprocessed (l : List (Tracks 2)) (pos : ℕ) {x : ℤ} (h : (pos : ℤ) ≤ x) :
    resetContent l pos x = l.getI x.toNat := by
  unfold resetContent
  split_ifs <;> first | rfl | omega

theorem resetContent_succ (l : List (Tracks 2)) (pos : ℕ) (x : ℤ) :
    resetContent l (pos + 1) x =
      if x = (pos : ℤ) then (fun t => if t.val = 1 then none else (l.getI pos) t)
      else resetContent l pos x := by
  by_cases he : x = (pos : ℤ)
  · subst he
    rw [if_pos rfl]
    have h1 : resetContent l (pos + 1) ((pos : ℤ))
        = (fun t => if t.val = 1 then none else (l.getI pos) t) := by
      rw [resetContent_processed l (pos + 1)
          (show (pos : ℤ) < ((pos + 1 : ℕ) : ℤ) from by omega),
        if_neg (show ¬((pos : ℤ) < 0) from by omega)]
      rfl
    exact h1
  · rw [if_neg he]
    by_cases h : x < (pos : ℤ)
    · have h2 : x < ((pos + 1 : ℕ) : ℤ) := by omega
      rw [resetContent_processed _ _ h, resetContent_processed _ _ h2]
    · have h3 : (pos : ℤ) ≤ x := by omega
      have h4 : ((pos + 1 : ℕ) : ℤ) ≤ x := by omega
      rw [resetContent_unprocessed _ _ h3, resetContent_unprocessed _ _ h4]

theorem getI_append {α : Type} [Inhabited α] (A B : List α) (x : ℕ) :
    (A ++ B).getI x = if x < A.length then A.getI x else B.getI (x - A.length) := by
  by_cases h : x < A.length
  · rw [if_pos h]
    have h2 : x < (A ++ B).length := by
      rw [List.length_append]; omega
    rw [List.getI_eq_getElem _ h2, List.getI_eq_getElem _ h, List.getElem_append_left h]
  · rw [if_neg h]
    by_cases h2 : x < (A ++ B).length
    · have h3 : x - A.length < B.length := by
        rw [List.length_append] at h2; omega
      rw [List.getI_eq_getElem _ h2, List.getI_eq_getElem _ h3, List.getElem_append_right
        (Nat.le_of_not_lt h)]
    · have h4 : (A ++ B).length ≤ x := Nat.le_of_not_lt h2
      have h5 : B.length ≤ x - A.length := by
        rw [List.length_append] at h4; omega
      rw [List.getI_eq_default _ h4, List.getI_eq_default _ h5]

theorem inputWindow_le (l : List (Tracks 2)) : inputWindow l ≤ l.length := by
  unfold inputWindow
  exact List.Sublist.length_le (List.takeWhile_sublist _)

theorem takeWhile_getI {α : Type} [Inhabited α] (p : α → Bool) (l : List α) (i : ℕ)
    (h : i < (l.takeWhile p).length) : (l.takeWhile p).getI i = l.getI i := by
  have hde : l.takeWhile p ++ l.dropWhile p = l := List.takeWhile_append_dropWhile
  have h2 : (l.takeWhile p).getI i = (l.takeWhile p ++ l.dropWhile p).getI i := by
    rw [getI_append, if_pos h]
  rw [h2, hde]

theorem inputWindow_getI (l : List (Tracks 2)) {i : ℕ} (h : i < inputWindow l) :
    ((l.getI i) 0).isSome = true := by
  unfold inputWindow at h
  have hmem : (l.takeWhile fun s => (s 0).isSome).getI i
      ∈ l.takeWhile fun s => (s 0).isSome := by
    rw [List.getI_eq_getElem _ h]
    exact List.getElem_mem h
  have hp := List.mem_takeWhile_imp hmem
  rw [takeWhile_getI _ _ _ h] at hp
  exact hp

theorem inputWindow_getI_none (l : List (Tracks 2)) :
    ((l.getI (inputWindow l)) 0) = none := by
  have key : ¬ ((l.getI (inputWindow l)) 0).isSome = true := by
    unfold inputWindow
    by_cases h : (l.takeWhile fun s => (s 0).isSome).length < l.length
    · have hdrop : 0 < (l.dropWhile fun s => (s 0).isSome).length := by
        have hde := List.takeWhile_append_dropWhile
          (p := fun s : Tracks 2 => (s 0).isSome) (l := l)
        have := congrArg List.length hde
        rw [List.length_append] at this
        omega
      have hget := getI_append (l.takeWhile fun s => (s 0).isSome)
        (l.dropWhile fun s => (s 0).isSome) (l.takeWhile fun s => (s 0).isSome).length
      have hwn : ¬ (l.takeWhile fun s => (s 0).isSome).length
          < (l.takeWhile fun s => (s 0).isSome).length := by omega
      rw [if_neg hwn] at hget
      have hww : (l.takeWhile fun s => (s 0).isSome).length
          - (l.takeWhile fun s => (s 0).isSome).length = 0 := by omega
      rw [hww] at hget
      have hde := List.takeWhile_append_dropWhile
        (p := fun s : Tracks 2 => (s 0).isSome) (l := l)
      rw [hde] at hget
      have hnot := List.dropWhile_get_zero_not (fun s : Tracks 2 => (s 0).isSome) l hdrop
      have hconv : (l.dropWhile fun s => (s 0).isSome).get ⟨0, hdrop⟩
          = (l.dropWhile fun s => (s 0).isSome).getI 0 := by
        rw [List.get_eq_getElem, List.getI_eq_getElem]
      rw [hconv, ← hget] at hnot
      exact hnot
    · have heq : (l.takeWhile fun s => (s 0).isSome).length = l.length :=
        le_antisymm (List.Sublist.length_le (List.takeWhile_sublist _)) (Nat.le_of_not_lt h)
      rw [heq, List.getI_eq_default _ le_rfl]
      have hd : ((default : Tracks 2) 0) = (none : Option Bool) := rfl
      rw [hd]
      intro hc
      simp at hc
  cases hc : l.getI (inputWindow l) 0 with
  | none => rfl
  | some b => exact absurd (by simp [hc]) key

theorem resetWindowList_getI (l : List (Tracks 2)) (x : ℕ) :
    (resetWindowList l).getI x =
      if x < inputWindow l then (fun t => if t.val = 1 then none else (l.getI x) t)
      else l.getI x := by
  set A : List (Tracks 2) := (l.take (inputWindow l)).map fun s t => if t.val = 1 then none else s t
  have heq : resetWindowList l = A ++ l.drop (inputWindow l) := rfl
  have hlen : A.length = inputWindow l := by
    subst A
    rw [List.length_map, List.length_take]
    exact min_eq_left (inputWindow_le l)
  have happ := getI_append A (l.drop (inputWindow l)) x
  rw [heq, happ, hlen]
  by_cases h : x < inputWindow l
  · rw [if_pos h]
    subst A
    rw [getI_map]
    have h2 : x < l.length := Nat.lt_of_lt_of_le h (inputWindow_le l)
    have hlen2 : x < (l.take (inputWindow l)).length := by
      rw [List.length_take, Nat.lt_min]
      exact ⟨h, h2⟩
    rw [List.length_take]
    rw [if_pos (Nat.lt_min.mpr ⟨h, h2⟩)]
    rw [List.getI_eq_getElem _ hlen2, List.getElem_take, List.getI_eq_getElem _ h2]
    rw [if_pos h]
  · rw [if_neg h]
    have key : (l.drop (inputWindow l)).getI (x - inputWindow l) = l.getI x := by
      have hde : l.take (inputWindow l) ++ l.drop (inputWindow l) = l := List.take_append_drop _ _
      have happ2 := getI_append (l.take (inputWindow l)) (l.drop (inputWindow l)) x
      rw [hde] at happ2
      have hlt : ¬ x < (l.take (inputWindow l)).length := by
        rw [List.length_take, Nat.lt_min]
        exact fun hc => h hc.1
      rw [if_neg hlt] at happ2
      have hsub : x - (l.take (inputWindow l)).length = x - inputWindow l := by
        rw [List.length_take, min_eq_left (inputWindow_le l)]
      rw [hsub] at happ2
      exact happ2.symm
    rw [key, if_neg h]

theorem resetContent_end (l : List (Tracks 2)) (x : ℤ) :
    resetContent l (inputWindow l) x =
      if x < 0 then default else (resetWindowList l).getI x.toNat := by
  by_cases hx : x < 0
  · rw [resetContent_processed l (inputWindow l)
        (Int.lt_of_lt_of_le hx (Int.natCast_nonneg (inputWindow l))), if_pos hx, if_pos hx]
  · have hne : 0 ≤ x := Int.le_of_not_gt hx
    by_cases h2 : x.toNat < inputWindow l
    · have h3 : x < (inputWindow l : ℤ) := by
        rw [← Int.toNat_of_nonneg hne]
        exact_mod_cast h2
      rw [resetContent_processed l (inputWindow l) h3, if_neg hx, if_neg hx,
        resetWindowList_getI, if_pos h2]
    · have h3 : (inputWindow l : ℤ) ≤ x := by
        rw [← Int.toNat_of_nonneg hne]
        exact_mod_cast Nat.le_of_not_lt h2
      rw [resetContent_unprocessed l (inputWindow l) h3, if_neg hx,
        resetWindowList_getI, if_neg h2]

theorem inputWindow_bothTrack (input : List Bool) :
    inputWindow (bothTrackEncode input) = input.length := by
  have h2 : ∀ s ∈ bothTrackEncode input, (s 0).isSome = true := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
    rfl
  have h3 : (bothTrackEncode input).takeWhile (fun s => (s 0).isSome)
      = bothTrackEncode input := List.takeWhile_eq_self_iff.mpr h2
  unfold inputWindow
  rw [h3]
  unfold bothTrackEncode
  rw [List.length_map]

theorem bothTrack_getI_blank (input : List Bool) (x : ℕ) :
    (fun t : Fin 2 => if t.val = 1 then none else ((bothTrackEncode input).getI x) t)
      = (twoTrackBitEncode input).getI x := by
  rw [bothTrackEncode_getI, twoTrackBitEncode_getI]
  by_cases h : x < input.length
  · rw [if_pos h, if_pos h]
    funext t
    have hlt : t.val < 2 := t.isLt
    have ht : t.val = 0 ∨ t.val = 1 := by omega
    rcases ht with ht | ht <;> simp [ht]
  · rw [if_neg h, if_neg h]
    funext t
    by_cases ht : t.val = 1
    · rw [if_pos ht]; rfl
    · rw [if_neg ht]

theorem resetWindowList_bothTrack (input : List Bool) (x : ℕ) :
    (resetWindowList (bothTrackEncode input)).getI x = (twoTrackBitEncode input).getI x := by
  rw [resetWindowList_getI, inputWindow_bothTrack]
  by_cases h : x < input.length
  · rw [if_pos h]
    exact bothTrack_getI_blank input x
  · rw [if_neg h, bothTrackEncode_getI, twoTrackBitEncode_getI, if_neg h, if_neg h]

theorem reset_write_cell (l : List (Tracks 2)) (pos : ℕ) :
    (fun t : Fin 2 => if t.val = 1 then none else
      (fun t => if t.val = 1 then none else (l.getI pos) t) t)
      = (fun t : Fin 2 => if t.val = 1 then none else (l.getI pos) t) := by
  funext t
  have hlt : t.val < 2 := t.isLt
  have ht : t.val = 0 ∨ t.val = 1 := by omega
  rcases ht with ht | ht <;> simp [ht]

theorem reset_step_rw {l : List (Tracks 2)} {pos : ℕ} (hpos : pos < inputWindow l)
    (cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl)
    (hq : cfg.q = ResetCtrl.rw pos)
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = resetContent l pos ((pos : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      Turing.TM0.step resetMachineTable cfg = some cfg' ∧
      cfg'.q = ResetCtrl.rm pos ∧
      ∀ i : ℤ, cfg'.Tape.nth i = resetContent l (pos + 1) ((pos : ℤ) + i) := by
  have hsym0 : ((cfg.Tape.head) 0).isSome = true := by
    have h := inputWindow_getI l hpos
    have h2 : cfg.Tape.head = cfg.Tape.nth 0 := rfl
    rw [h2, hnth, Int.add_zero, resetContent_unprocessed l pos le_rfl, Int.toNat_natCast]
    exact h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsym0
  have hsym : cfg.Tape.head 0 = some b := hb
  have htab : resetMachineTable cfg.q cfg.Tape.head
      = some (ResetCtrl.rm pos,
          Turing.TM0.Stmt.write fun t => if t.val = 1 then none else cfg.Tape.head t) := by
    rw [hq]
    show (match cfg.Tape.head 0 with
      | some _ => some (ResetCtrl.rm pos,
          Turing.TM0.Stmt.write (fun t : Fin 2 => if t.val = 1 then none else cfg.Tape.head t))
      | none => some (ResetCtrl.rh pos, Turing.TM0.Stmt.write cfg.Tape.head)) = _
    rw [hsym]
  refine ⟨⟨ResetCtrl.rm pos, cfg.Tape.write
      (fun t => if t.val = 1 then none else cfg.Tape.head t)⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some resetMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.write_nth, resetContent_succ]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos (show (0 : ℤ) = 0 from rfl),
        if_pos (show ((pos : ℤ) + 0) = (pos : ℤ) from rfl)]
      have hs : cfg.Tape.head = l.getI pos := by
        rw [← Turing.Tape.nth_zero, hnth, Int.add_zero, resetContent_unprocessed l pos le_rfl,
          Int.toNat_natCast]
      rw [hs]
    · rw [if_neg hi]
      have h1 : ((pos : ℤ) + i) ≠ (pos : ℤ) := by omega
      rw [if_neg h1, hnth]

theorem reset_step_rm {l : List (Tracks 2)} {pos : ℕ}
    (cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl)
    (hq : cfg.q = ResetCtrl.rm pos)
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = resetContent l (pos + 1) ((pos : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      Turing.TM0.step resetMachineTable cfg = some cfg' ∧
      cfg'.q = ResetCtrl.rw (pos + 1) ∧
      ∀ i : ℤ, cfg'.Tape.nth i = resetContent l (pos + 1) (((pos + 1 : ℕ) : ℤ) + i) := by
  have htab : resetMachineTable cfg.q cfg.Tape.head
      = some (ResetCtrl.rw (pos + 1), Turing.TM0.Stmt.move Turing.Dir.right) := by
    rw [hq]
    rfl
  refine ⟨⟨ResetCtrl.rw (pos + 1), cfg.Tape.move Turing.Dir.right⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some resetMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.move_right_nth, hnth]
    congr 1
    omega

theorem reset_step_rw_end (l : List (Tracks 2))
    (cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl)
    (hq : cfg.q = ResetCtrl.rw (inputWindow l))
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = resetContent l (inputWindow l)
        ((inputWindow l : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      Turing.TM0.step resetMachineTable cfg = some cfg' ∧
      cfg'.q = ResetCtrl.rh (inputWindow l) ∧
      ∀ i : ℤ, cfg'.Tape.nth i = resetContent l (inputWindow l)
        ((inputWindow l : ℤ) + i) := by
  have hsym : cfg.Tape.head 0 = none := by
    rw [← Turing.Tape.nth_zero, hnth, Int.add_zero]
    have h2 : resetContent l (inputWindow l) (inputWindow l : ℤ)
        = l.getI (inputWindow l) := by
      rw [resetContent_unprocessed l (inputWindow l) le_rfl, Int.toNat_natCast]
    rw [h2]
    exact inputWindow_getI_none l
  have htab : resetMachineTable cfg.q cfg.Tape.head
      = some (ResetCtrl.rh (inputWindow l), Turing.TM0.Stmt.write cfg.Tape.head) := by
    rw [hq]
    show (match cfg.Tape.head 0 with
      | some _ => some (ResetCtrl.rm (inputWindow l),
          Turing.TM0.Stmt.write (fun t : Fin 2 => if t.val = 1 then none else cfg.Tape.head t))
      | none => some (ResetCtrl.rh (inputWindow l), Turing.TM0.Stmt.write cfg.Tape.head)) = _
    rw [hsym]
  refine ⟨⟨ResetCtrl.rh (inputWindow l), cfg.Tape.write cfg.Tape.head⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some resetMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.write_nth]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos (show (0 : ℤ) = 0 from rfl), Int.add_zero]
      have h2 : resetContent l (inputWindow l) (inputWindow l : ℤ)
          = l.getI (inputWindow l) := by
        rw [resetContent_unprocessed l (inputWindow l) le_rfl, Int.toNat_natCast]
      rw [h2]
      have h3 : cfg.Tape.head = cfg.Tape.nth 0 := rfl
      rw [h3, hnth, Int.add_zero, h2]
    · rw [if_neg hi, hnth]

theorem reset_step_rh {l : List (Tracks 2)} {pos : ℕ}
    (cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl)
    (hq : cfg.q = ResetCtrl.rh (pos + 1))
    (hnth : ∀ i : ℤ, cfg.Tape.nth i = resetContent l (inputWindow l)
        (((pos + 1 : ℕ) : ℤ) + i)) :
    ∃ cfg' : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      Turing.TM0.step resetMachineTable cfg = some cfg' ∧
      cfg'.q = ResetCtrl.rh pos ∧
      ∀ i : ℤ, cfg'.Tape.nth i = resetContent l (inputWindow l) ((pos : ℤ) + i) := by
  have htab : resetMachineTable cfg.q cfg.Tape.head
      = some (ResetCtrl.rh pos, Turing.TM0.Stmt.move Turing.Dir.left) := by
    rw [hq]
    rfl
  refine ⟨⟨ResetCtrl.rh pos, cfg.Tape.move Turing.Dir.left⟩, ?_, rfl, ?_⟩
  · exact Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_some resetMachineTable cfg _ _ htab
  · intro i
    rw [Turing.Tape.move_left_nth, hnth]
    congr 1
    omega

theorem reset_step_rh0 (l : List (Tracks 2))
    (cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl)
    (hq : cfg.q = ResetCtrl.rh 0) :
    Turing.TM0.step resetMachineTable cfg = none := by
  rw [Qatlib.Concepts.ClassicalTape.FairCoinTape.TM0_step_eq_none, hq]
  rfl

theorem reset_rw_reach (l : List (Tracks 2)) :
    ∀ pos ≤ inputWindow l, ∃ cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      runFrom resetMachineTable (2 * pos) (Turing.TM0.init l) = some cfg ∧
      cfg.q = ResetCtrl.rw pos ∧
      ∀ i : ℤ, cfg.Tape.nth i = resetContent l pos ((pos : ℤ) + i) := by
  intro pos hpos
  induction pos with
  | zero =>
    refine ⟨Turing.TM0.init l, rfl, rfl, ?_⟩
    intro i
    have hz : ((0 : ℕ) : ℤ) + i = i := by omega
    rw [init_nth, hz, resetContent_zero]
  | succ pos ih =>
    obtain ⟨cfg, hr, hq, hnth⟩ := ih (Nat.le_of_succ_le hpos)
    have hpos' : pos < inputWindow l := Nat.lt_of_succ_le hpos
    obtain ⟨cfg₁, hs₁, hq₁, hn₁⟩ := reset_step_rw hpos' cfg hq hnth
    obtain ⟨cfg₂, hs₂, hq₂, hn₂⟩ := reset_step_rm cfg₁ hq₁ hn₁
    refine ⟨cfg₂, ?_, hq₂, hn₂⟩
    rw [show (2 * (pos + 1)) = (2 * pos + 1) + 1 from by omega]
    rw [runFrom_add1, runFrom_add1, hr]
    simp [hs₁, hs₂]

theorem reset_rh_reach (l : List (Tracks 2)) :
    ∀ k ≤ inputWindow l, ∃ cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      runFrom resetMachineTable (2 * inputWindow l + 1 + k) (Turing.TM0.init l) = some cfg ∧
      cfg.q = ResetCtrl.rh (inputWindow l - k) ∧
      ∀ i : ℤ, cfg.Tape.nth i =
        resetContent l (inputWindow l) (((inputWindow l - k : ℕ) : ℤ) + i) := by
  intro k hk
  induction k with
  | zero =>
    obtain ⟨cfg, hr, hq, hnth⟩ := reset_rw_reach l (inputWindow l) le_rfl
    obtain ⟨cfg₁, hs₁, hq₁, hn₁⟩ := reset_step_rw_end l cfg hq hnth
    refine ⟨cfg₁, ?_, hq₁, hn₁⟩
    rw [show (2 * inputWindow l + 1 + 0) = 2 * inputWindow l + 1 from by omega,
      runFrom_add1, hr]
    simp [hs₁]
  | succ k ih =>
    obtain ⟨cfg, hr, hq, hnth⟩ := ih (Nat.le_of_succ_le hk)
    have heq : inputWindow l - k = (inputWindow l - (k + 1)) + 1 := by omega
    rw [heq] at hq hnth
    obtain ⟨cfg₁, hs₁, hq₁, hn₁⟩ := reset_step_rh cfg hq hnth
    refine ⟨cfg₁, ?_, hq₁, hn₁⟩
    rw [show (2 * inputWindow l + 1 + (k + 1)) = (2 * inputWindow l + 1 + k) + 1 from by omega,
      runFrom_add1, hr]
    simp [hs₁]

theorem reset_run (l : List (Tracks 2)) :
    ∃ cfg : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      runFrom resetMachineTable (2 * inputWindow l + 1 + inputWindow l) (Turing.TM0.init l)
        = some cfg ∧
      Turing.TM0.step resetMachineTable cfg = none ∧
      ∀ i : ℤ, cfg.Tape.nth i = resetContent l (inputWindow l) i := by
  obtain ⟨cfg, hr, hq, hnth⟩ := reset_rh_reach l (inputWindow l) le_rfl
  have hq' : cfg.q = ResetCtrl.rh 0 := by
    rw [show (inputWindow l - inputWindow l : ℕ) = 0 from Nat.sub_self _] at hq
    exact hq
  refine ⟨cfg, hr, reset_step_rh0 l cfg hq', ?_⟩
  intro i
  have h0 : (inputWindow l - inputWindow l : ℕ) = 0 := Nat.sub_self _
  have hz : (((0 : ℕ) : ℤ) + i) = i := by omega
  rw [hnth, h0, hz]

theorem reset_final (l : List (Tracks 2)) :
    ∃ final : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      BitMachineAfter resetMachineTable l (3 * inputWindow l + 1) = some final ∧
      Turing.TM0.step resetMachineTable final = none ∧
      final.Tape =
        (Turing.TM0.init (resetWindowList l) : Turing.TM0.Cfg (Tracks 2) ResetCtrl).Tape := by
  obtain ⟨cfg, hr, hstop, hnth⟩ := reset_run l
  refine ⟨cfg, ?_, hstop, ?_⟩
  · rw [bitMachineAfter_eq_runFrom]
    rw [show (3 * inputWindow l + 1) = 2 * inputWindow l + 1 + inputWindow l from by omega]
    exact hr
  · apply tape_ext
    intro i
    rw [hnth, resetContent_end, init_nth]

theorem reset_roundtrip (input : List Bool) :
    ∃ final : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      BitMachineAfter resetMachineTable (bothTrackEncode input) (3 * input.length + 1) = some final ∧
      Turing.TM0.step resetMachineTable final = none ∧
      final.Tape =
        (Turing.TM0.init (twoTrackBitEncode input) : Turing.TM0.Cfg (Tracks 2) ResetCtrl).Tape := by
  obtain ⟨cfg, hr, hq, hnth⟩ := reset_run (bothTrackEncode input)
  rw [inputWindow_bothTrack] at hr
  refine ⟨cfg, ?_, hq, ?_⟩
  · rw [bitMachineAfter_eq_runFrom]
    rw [show (3 * input.length + 1) = 2 * input.length + 1 + input.length from by omega]
    exact hr
  · apply tape_ext
    intro i
    rw [hnth, resetContent_end, init_nth]
    by_cases hx : i < 0
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx, resetWindowList_bothTrack]

theorem abs_le_succ_of_abs_le {i : ℤ} {t : ℕ} (h : |i| ≤ t) : |i| ≤ t + 1 := by
  have h' : -(t : ℤ) ≤ i ∧ i ≤ (t : ℤ) := abs_le.mp h
  refine abs_le.mpr ⟨?_, ?_⟩ <;> omega

theorem abs_le_succ_of_abs_pred {i : ℤ} {t : ℕ} (h : |i - 1| ≤ t) : |i| ≤ t + 1 := by
  have h' : -(t : ℤ) ≤ i - 1 ∧ i - 1 ≤ (t : ℤ) := abs_le.mp h
  refine abs_le.mpr ⟨?_, ?_⟩ <;> omega

theorem abs_le_succ_of_abs_succ {i : ℤ} {t : ℕ} (h : |i + 1| ≤ t) : |i| ≤ t + 1 := by
  have h' : -(t : ℤ) ≤ i + 1 ∧ i + 1 ≤ (t : ℤ) := abs_le.mp h
  refine abs_le.mpr ⟨?_, ?_⟩ <;> omega

theorem scratch_step_reach {t : ℕ} {Λ : Type} [Inhabited Λ]
    (T : Turing.Tape (Tracks 2)) (stmt : Turing.TM0.Stmt (Tracks 2))
    (H : ∀ j : ℤ, T.nth j 1 ≠ none → |j| ≤ t) :
    ∀ i : ℤ, (TM0StmtApply T stmt).nth i 1 ≠ none → |i| ≤ t + 1 := by
  cases stmt with
  | write a =>
    intro i hi
    change (T.write a).nth i 1 ≠ none at hi
    rw [Tape.write_nth] at hi
    by_cases hi0 : i = 0
    · subst hi0
      refine abs_le.mpr ⟨?_, ?_⟩ <;> omega
    · rw [if_neg hi0] at hi
      exact abs_le_succ_of_abs_le (H i hi)
  | move d =>
    intro i hi
    change (T.move d).nth i 1 ≠ none at hi
    cases d with
    | left =>
      rw [Tape.move_left_nth] at hi
      exact abs_le_succ_of_abs_pred (H (i - 1) hi)
    | right =>
      rw [Tape.move_right_nth] at hi
      exact abs_le_succ_of_abs_succ (H (i + 1) hi)

theorem scratch_head_reach :
    ∀ (Λ : Type) [Inhabited Λ] (M : Turing.TM0.Machine (Tracks 2) Λ)
      (l : List (Tracks 2)), (∀ s ∈ l, s 1 = none) →
    ∀ (t : ℕ) (final : Turing.TM0.Cfg (Tracks 2) Λ),
      BitMachineAfter M l t = some final → ScratchWithinHeadReach t final.Tape := by
  intro Λ instM M l hl t
  induction t with
  | zero =>
    intro final hrun i hi
    have h0 : some (Turing.TM0.init l : Turing.TM0.Cfg (Tracks 2) Λ) = some final := hrun
    have feq : (Turing.TM0.init l : Turing.TM0.Cfg (Tracks 2) Λ) = final := Option.some.inj h0
    subst feq
    rw [init_nth] at hi
    by_cases hneg : i < 0
    · rw [if_pos hneg] at hi
      exact absurd rfl hi
    · rw [if_neg hneg] at hi
      by_cases hlen : i.toNat < l.length
      · rw [List.getI_eq_getElem l hlen] at hi
        exact absurd (hl l[i.toNat] (List.getElem_mem hlen)) hi
      · rw [List.getI_eq_default l (Nat.le_of_not_lt hlen)] at hi
        exact absurd rfl hi
  | succ t ih =>
    intro final hrun i hi
    have hbind : (BitMachineAfter M l t).bind (Turing.TM0.step M) = some final := hrun
    obtain ⟨cfg, hcfg, hstep⟩ := Option.bind_eq_some_iff.mp hbind
    have ih' : ∀ j : ℤ, cfg.Tape.nth j 1 ≠ none → |j| ≤ t := ih cfg hcfg
    rw [TM0_step_apply] at hstep
    rcases hc : M cfg.q cfg.Tape.head with - | ⟨q', stmt⟩
    · rw [hc] at hstep
      simp only [Option.map_none] at hstep
      cases hstep
    · rw [hc] at hstep
      simp only [Option.map_some] at hstep
      have hfin : (⟨q', TM0StmtApply cfg.Tape stmt⟩ : Turing.TM0.Cfg (Tracks 2) Λ) = final := by
        simpa using Option.some.inj hstep
      have hTape : final.Tape = TM0StmtApply cfg.Tape stmt := by rw [← hfin]
      rw [hTape] at hi
      exact scratch_step_reach (Λ := Λ) cfg.Tape stmt ih' i hi

theorem g2 :

  (∀ input : List Bool,
    ∃ final : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      BitMachineAfter copyMachineTable (twoTrackBitEncode input) (3 * input.length + 1)
        = some final ∧
        Turing.TM0.step copyMachineTable final = none ∧
        final.Tape =
          (Turing.TM0.init (bothTrackEncode input) : Turing.TM0.Cfg (Tracks 2) CopyCtrl).Tape) ∧

  (∀ input : List Bool,
    ∃ mid : Turing.TM0.Cfg (Tracks 2) CopyCtrl,
      BitMachineAfter copyMachineTable (twoTrackBitEncode input) (3 * input.length)
        = some mid ∧
      Turing.TM0.step copyMachineTable mid ≠ none) ∧

  (∀ l : List (Tracks 2),
    ∃ final : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      BitMachineAfter resetMachineTable l (3 * inputWindow l + 1) = some final ∧
        Turing.TM0.step resetMachineTable final = none ∧
        final.Tape =
          (Turing.TM0.init (resetWindowList l) : Turing.TM0.Cfg (Tracks 2) ResetCtrl).Tape) ∧

  (∀ input : List Bool,
    ∃ final : Turing.TM0.Cfg (Tracks 2) ResetCtrl,
      BitMachineAfter resetMachineTable (bothTrackEncode input) (3 * input.length + 1)
        = some final ∧
        Turing.TM0.step resetMachineTable final = none ∧
        final.Tape =
          (Turing.TM0.init (twoTrackBitEncode input) : Turing.TM0.Cfg (Tracks 2) ResetCtrl).Tape) ∧

  (∀ (Λ : Type) [Inhabited Λ] (M : Turing.TM0.Machine (Tracks 2) Λ)
      (l : List (Tracks 2)), (∀ s ∈ l, s 1 = none) →
    ∀ (t : ℕ) (final : Turing.TM0.Cfg (Tracks 2) Λ),
      BitMachineAfter M l t = some final → ScratchWithinHeadReach t final.Tape)
 := by
  exact ⟨copy_final, copy_mid, reset_final, reset_roundtrip, scratch_head_reach⟩

open Turing

def copyStk (i w a : List Bool) : TM2Stack → List Bool
  | .input => i
  | .work => w
  | .aux => a

theorem update_copyStk_input (i w a i' : List Bool) :
    Function.update (copyStk i w a) TM2Stack.input i' = copyStk i' w a := by
  funext k; cases k <;> rfl

theorem update_copyStk_work (i w a w' : List Bool) :
    Function.update (copyStk i w a) TM2Stack.work w' = copyStk i w' a := by
  funext k; cases k <;> rfl

theorem update_copyStk_aux (i w a a' : List Bool) :
    Function.update (copyStk i w a) TM2Stack.aux a' = copyStk i w a' := by
  funext k; cases k <;> rfl

theorem tm2InitCopy_eq (input : List Bool) :
    tm2InitCopy input = ⟨some .transfer, none, copyStk input [] []⟩ := by
  simp only [tm2InitCopy]
  congr 1
  funext k
  cases k <;> rfl

theorem tm2InitReset_eq (input work : List Bool) :
    tm2InitReset input work = ⟨some .clear, none, copyStk input work []⟩ := by
  simp only [tm2InitReset]
  congr 1
  funext k
  cases k <;> rfl

theorem tm2Run_succ {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (t : ℕ) (cfg : Turing.TM2.Cfg Γ Λ σ) :
    tm2Run M (t + 1) cfg =
      match Turing.TM2.step M cfg with
      | none => some cfg
      | some cfg' => tm2Run M t cfg' := rfl

theorem tm2Run_halt {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (s : ℕ) (var : σ) (stk : ∀ k, List (Γ k)) :
    tm2Run M s ⟨none, var, stk⟩ = some ⟨none, var, stk⟩ := by
  cases s <;> rfl

theorem tm2Copy_transfer (b : Bool) (rest acc work : List Bool) (v : Option Bool) :
    Turing.TM2.step tm2Copy
        ⟨some .transfer, v, copyStk (b :: rest) work acc⟩ =
      some ⟨some .transfer, some b, copyStk rest work (b :: acc)⟩ := by
  simp only [Turing.TM2.step, tm2Copy, Turing.TM2.stepAux, copyStk,
    update_copyStk_input, update_copyStk_aux, List.head?_cons, List.tail_cons,
    Option.isNone_some, cond_false, Option.getD_some]

theorem tm2Copy_transfer_nil (acc work : List Bool) (v : Option Bool) :
    Turing.TM2.step tm2Copy
        ⟨some .transfer, v, copyStk [] work acc⟩ =
      some ⟨some .restore, none, copyStk [] work acc⟩ := by
  simp only [Turing.TM2.step, tm2Copy, Turing.TM2.stepAux, copyStk,
    update_copyStk_input, List.head?_nil, List.tail_nil, Option.isNone_none, cond_true]

theorem tm2Copy_restore (b : Bool) (rest inp work : List Bool) (v : Option Bool) :
    Turing.TM2.step tm2Copy
        ⟨some .restore, v, copyStk inp work (b :: rest)⟩ =
      some ⟨some .restore, some b, copyStk (b :: inp) (b :: work) rest⟩ := by
  simp only [Turing.TM2.step, tm2Copy, Turing.TM2.stepAux, copyStk,
    update_copyStk_aux, update_copyStk_work, update_copyStk_input,
    List.head?_cons, List.tail_cons, Option.isNone_some, cond_false, Option.getD_some]

theorem tm2Copy_restore_nil (inp work : List Bool) (v : Option Bool) :
    Turing.TM2.step tm2Copy
        ⟨some .restore, v, copyStk inp work []⟩ =
      some ⟨none, none, copyStk inp work []⟩ := by
  simp only [Turing.TM2.step, tm2Copy, Turing.TM2.stepAux, copyStk,
    update_copyStk_aux, List.head?_nil, List.tail_nil, Option.isNone_none, cond_true]

theorem tm2Reset_clear (b : Bool) (rest input : List Bool) (v : Option Bool) :
    Turing.TM2.step tm2Reset
        ⟨some .clear, v, copyStk input (b :: rest) []⟩ =
      some ⟨some .clear, some b, copyStk input rest []⟩ := by
  simp only [Turing.TM2.step, tm2Reset, Turing.TM2.stepAux, copyStk,
    update_copyStk_work, List.head?_cons, List.tail_cons, Option.isNone_some,
    cond_false, Option.getD_some]

theorem tm2Reset_clear_nil (input : List Bool) (v : Option Bool) :
    Turing.TM2.step tm2Reset
        ⟨some .clear, v, copyStk input [] []⟩ =
      some ⟨none, none, copyStk input [] []⟩ := by
  simp only [Turing.TM2.step, tm2Reset, Turing.TM2.stepAux, copyStk,
    update_copyStk_work, List.head?_nil, List.tail_nil, Option.isNone_none, cond_true]

theorem transfer_phase (input work acc : List Bool) (v : Option Bool) :
    ∀ (s : ℕ),
      tm2Run tm2Copy (s + input.length + 1) ⟨some .transfer, v, copyStk input work acc⟩ =
        tm2Run tm2Copy s ⟨some .restore, none, copyStk [] work (List.reverse input ++ acc)⟩ := by
  induction input generalizing work acc v with
  | nil =>
    intro s
    rw [tm2Run_succ, tm2Copy_transfer_nil]
    rfl
  | cons b rest ih =>
    intro s
    simp only [List.length_cons]
    rw [show (s + (rest.length + 1) + 1) = ((s + rest.length + 1) + 1) by omega]
    rw [tm2Run_succ, tm2Copy_transfer]
    show tm2Run tm2Copy (s + rest.length + 1) ⟨some .transfer, some b,
        copyStk rest work (b :: acc)⟩ = _
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem restore_phase (aux inp work : List Bool) (v : Option Bool) :
    ∀ (s : ℕ),
      tm2Run tm2Copy (s + aux.length + 1) ⟨some .restore, v, copyStk inp work aux⟩ =
        tm2Run tm2Copy s
          ⟨none, none, copyStk (List.reverse aux ++ inp) (List.reverse aux ++ work) []⟩ := by
  induction aux generalizing inp work v with
  | nil =>
    intro s
    rw [tm2Run_succ, tm2Copy_restore_nil]
    rfl
  | cons b rest ih =>
    intro s
    simp only [List.length_cons]
    rw [show (s + (rest.length + 1) + 1) = ((s + rest.length + 1) + 1) by omega]
    rw [tm2Run_succ, tm2Copy_restore]
    show tm2Run tm2Copy (s + rest.length + 1) ⟨some .restore, some b,
        copyStk (b :: inp) (b :: work) rest⟩ = _
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem reset_phase (input work : List Bool) (v : Option Bool) :
    ∀ (s : ℕ),
      tm2Run tm2Reset (s + work.length + 1) ⟨some .clear, v, copyStk input work []⟩ =
        tm2Run tm2Reset s ⟨none, none, copyStk input [] []⟩ := by
  induction work generalizing input v with
  | nil =>
    intro s
    rw [tm2Run_succ, tm2Reset_clear_nil]
    rfl
  | cons b rest ih =>
    intro s
    simp only [List.length_cons]
    rw [show (s + (rest.length + 1) + 1) = ((s + rest.length + 1) + 1) by omega]
    rw [tm2Run_succ, tm2Reset_clear]
    show tm2Run tm2Reset (s + rest.length + 1) ⟨some .clear, some b, copyStk input rest []⟩ = _
    rw [ih]

theorem tm2Copy_run (input : List Bool) :
    tm2Run tm2Copy (2 * input.length + 2) (tm2InitCopy input) =
      some ⟨none, none, copyStk input input []⟩ := by
  rw [tm2InitCopy_eq]
  rw [show (2 * input.length + 2) = ((input.length + 1) + input.length + 1) by omega]
  rw [transfer_phase input [] [] none (input.length + 1)]
  simp only [List.append_nil]
  rw [show (input.length + 1) = (0 + (List.reverse input).length + 1) by
    rw [List.length_reverse]; omega]
  rw [restore_phase (List.reverse input) [] [] none 0]
  rw [tm2Run_halt]
  simp only [List.reverse_reverse, List.nil_append, List.append_nil]

theorem tm2Reset_run (input work : List Bool) :
    tm2Run tm2Reset (work.length + 1) (tm2InitReset input work) =
      some ⟨none, none, copyStk input [] []⟩ := by
  rw [tm2InitReset_eq]
  rw [show (work.length + 1) = (0 + work.length + 1) by omega]
  rw [reset_phase input work none 0]
  rw [tm2Run_halt]

open Turing

theorem standardBitEncode_injective : Function.Injective standardBitEncode := by
  intro a b h
  unfold standardBitEncode at h
  exact List.map_injective_iff.mpr (Option.some_injective Bool) h

theorem twoTrackBitEncode_injective : Function.Injective twoTrackBitEncode := by
  have hinj : Function.Injective
      (fun b : Bool => (fun t : Fin 2 => if t.val = 0 then some b else none)) := by
    intro b₁ b₂ h
    have h0 := congrFun h (⟨0, by omega⟩ : Fin 2)
    simp only at h0
    exact Option.some.inj h0
  intro a b h
  unfold twoTrackBitEncode tracksEncode at h
  exact List.map_injective_iff.mpr hinj h

theorem delimitedPairEncode_injective : Function.Injective delimitedPairEncode := by
  have hinj : Function.Injective (fun x : Bool => (x, false)) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  intro a b h
  unfold delimitedPairEncode at h
  have h2 : (a.map fun x => (x, false)) = (b.map fun x => (x, false)) :=
    List.append_cancel_right h
  exact List.map_injective_iff.mpr hinj h2

theorem delimitedPairEncode_length (input : List Bool) :
    (delimitedPairEncode input).length = input.length + 1 := by
  simp [delimitedPairEncode]

open Turing

open Turing

open Turing
open scoped Classical

end Qatlib.Concepts.ClassicalTape.TapeCompilation
