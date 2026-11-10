/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeWeightedSamplingDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CappedFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib
open Qatlib
open scoped ENNReal

theorem of_prepend (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (e : NativeTape.Tick Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    RaceOutcome.of (NativeTape.Result.prepend e r) = RaceOutcome.of r := by
  simp [NativeTape.Result.prepend, RaceOutcome.of,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output]

theorem of_eq_left_halted {r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control}
    (h : RaceOutcome.of r = .left) : r.stop = .halted := by
  have h2 : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some false := by
    cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
    | none => simp [RaceOutcome.of, hu] at h
    | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢
  unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output at h2
  by_cases hs : r.stop = .halted
  · exact hs
  · simp [hs] at h2

theorem of_eq_right_halted {r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control}
    (h : RaceOutcome.of r = .right) : r.stop = .halted := by
  have h2 : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some true := by
    cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
    | none => simp [RaceOutcome.of, hu] at h
    | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢
  unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output at h2
  by_cases hs : r.stop = .halted
  · exact hs
  · simp [hs] at h2

theorem positionTape_interior (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a b = Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape (a-1+1) (b-1+1) := by
  cases a with
  | zero => omega
  | succ a =>
    cases b with
    | zero => omega
    | succ b => rfl

theorem head_cell (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Turing.Tape.head (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a b) = .cell := by
  have h := positionTape_interior a b ha hb
  rw [h]
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape, Turing.Tape.mk₂, Turing.Tape.mk',
    Turing.ListBlank.head_mk]

theorem head_left (b : ℕ) (hb : 0 < b) :
    Turing.Tape.head (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape 0 b) = .left := by
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  subst hb'
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape, Turing.Tape.mk₂, Turing.Tape.mk',
    Turing.ListBlank.head_mk]

theorem head_right (a : ℕ) (ha : 0 < a) :
    Turing.Tape.head (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a 0) = .right := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  subst ha'
  simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape, Turing.Tape.mk₂, Turing.Tape.mk',
    Turing.ListBlank.head_mk]

theorem advance_left (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move .left) =
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded (a-1) (b+1) := by
  have h := positionTape_interior a b ha hb
  have hp := Qatlib.Concepts.AdversaryBounds.AdvDuality.position_left (a-1) (b-1)
  have hb2 : b - 1 + 2 = b + 1 := by omega
  simp only [NativeTape.advance,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, TM0StmtApply]
  rw [h, hp, hb2]

theorem advance_right (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move .right) =
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded (a+1) (b-1) := by
  have h := positionTape_interior a b ha hb
  have hp := Qatlib.Concepts.AdversaryBounds.AdvDuality.position_right (a-1) (b-1)
  have ha2 : a - 1 + 2 = a + 1 := by omega
  simp only [NativeTape.advance,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, TM0StmtApply]
  rw [h, hp, ha2]

theorem law_coin (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (n+1) (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) =
      (PMF.uniformOfFintype' Bool).bind fun bit =>
        (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left)))).map
          (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit)) := by
  have hh := head_cell a b ha hb
  simp only [NativeTape.law, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded]
  rw [hh]
  rfl

theorem leftEvent_eq_finished (n a b : ℕ) :
    leftEvent n a b =
      ∑' r, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
        leftIndicator r := by
  unfold leftEvent Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply tsum_congr
  intro r
  by_cases hr : r.stop = .halted
  · rw [NativeTape.finishedMass, if_pos hr]
  · rw [NativeTape.finishedMass, if_neg hr]
    have h1 : leftIndicator r = 0 := by
      by_cases ho : RaceOutcome.of r = .left
      · rw [leftIndicator, if_pos ho]
        exact (hr (of_eq_left_halted ho)).elim
      · rw [leftIndicator, if_neg ho]
    simp [h1]

theorem rightEvent_eq_finished (n a b : ℕ) :
    rightEvent n a b =
      ∑' r, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
        rightIndicator r := by
  unfold rightEvent Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply tsum_congr
  intro r
  by_cases hr : r.stop = .halted
  · rw [NativeTape.finishedMass, if_pos hr]
  · rw [NativeTape.finishedMass, if_neg hr]
    have h1 : rightIndicator r = 0 := by
      by_cases ho : RaceOutcome.of r = .right
      · rw [rightIndicator, if_pos ho]
        exact (hr (of_eq_right_halted ho)).elim
      · rw [rightIndicator, if_neg ho]
    simp [h1]

theorem leftMass_eq_iSup (a b : ℕ) :
    leftMass a b = ⨆ n, leftEvent n a b := by
  have hmono : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      Monotone (fun n => NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r * leftIndicator r) := by
    intro r n m hnm
    exact mul_le_mul_left
      (NativeTape.finishedMass_mono Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r hnm)
      (leftIndicator r)
  have hkey : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      (⨆ n, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          leftIndicator r =
        ⨆ n, (NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          leftIndicator r :=
    fun r => ENNReal.iSup_mul _ _
  unfold leftMass NativeTape.haltedMass
  rw [show (∑' r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      (⨆ n, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
        leftIndicator r) =
      ∑' r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
        ⨆ n, (NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          leftIndicator r by
    apply tsum_congr
    intro r
    exact hkey r]
  rw [NativeTape.tsum_iSup_nat_mono _ hmono]
  apply congrArg (fun f : ℕ → ℝ≥0∞ => ⨆ n, f n)
  funext n
  exact (leftEvent_eq_finished n a b).symm

theorem rightMass_eq_iSup (a b : ℕ) :
    rightMass a b = ⨆ n, rightEvent n a b := by
  have hmono : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      Monotone (fun n => NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r * rightIndicator r) := by
    intro r n m hnm
    exact mul_le_mul_left
      (NativeTape.finishedMass_mono Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r hnm)
      (rightIndicator r)
  have hkey : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      (⨆ n, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          rightIndicator r =
        ⨆ n, (NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          rightIndicator r :=
    fun r => ENNReal.iSup_mul _ _
  unfold rightMass NativeTape.haltedMass
  rw [show (∑' r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      (⨆ n, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
        rightIndicator r) =
      ∑' r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
        ⨆ n, (NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          rightIndicator r by
    apply tsum_congr
    intro r
    exact hkey r]
  rw [NativeTape.tsum_iSup_nat_mono _ hmono]
  apply congrArg (fun f : ℕ → ℝ≥0∞ => ⨆ n, f n)
  funext n
  exact (rightEvent_eq_finished n a b).symm

theorem leftEvent_mono (n m a b : ℕ) (h : n ≤ m) : leftEvent n a b ≤ leftEvent m a b := by
  rw [leftEvent_eq_finished, leftEvent_eq_finished]
  exact ENNReal.tsum_le_tsum fun r =>
    mul_le_mul_left
      (NativeTape.finishedMass_mono Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r h)
      (leftIndicator r)

theorem rightEvent_mono (n m a b : ℕ) (h : n ≤ m) :
    rightEvent n a b ≤ rightEvent m a b := by
  rw [rightEvent_eq_finished, rightEvent_eq_finished]
  exact ENNReal.tsum_le_tsum fun r =>
    mul_le_mul_left
      (NativeTape.finishedMass_mono Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r h)
      (rightIndicator r)

theorem leftIndicator_prepend (a b : ℕ) (bit : Bool)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    leftIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r) =
      leftIndicator r := by
  simp [leftIndicator, of_prepend]

theorem rightIndicator_prepend (a b : ℕ) (bit : Bool)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    rightIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r) =
      rightIndicator r := by
  simp [rightIndicator, of_prepend]

theorem expectation_bind_map {α β γ : Type} (p : PMF α) (q : α → PMF β) (f : α → β → γ)
    (g : γ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (p.bind (fun a => (q a).map (f a))) g =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun a => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (q a) (fun b => g (f a b))) := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  apply congrArg
      (fun h : α → ℝ≥0∞ => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p h)
  funext a
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]

theorem leftEvent_succ (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    leftEvent (n+1) a b =
      (1/2 : ℝ≥0∞) * leftEvent n (a-1) (b+1) + (1/2 : ℝ≥0∞) * leftEvent n (a+1) (b-1) := by
  have hl := law_coin n a b ha hb
  have hinner : ∀ bit : Bool,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left))))
          (fun r => leftIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r)) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left))))
          leftIndicator := by
    intro bit
    apply congrArg (fun g : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control → ℝ≥0∞ =>
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
          (.walk, .move (if bit then .right else .left)))) g)
    funext r
    exact leftIndicator_prepend a b bit r
  unfold leftEvent
  rw [hl]
  rw [expectation_bind_map (PMF.uniformOfFintype' Bool)
    (fun bit => NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
        (.walk, .move (if bit then .right else .left))))
    (fun bit r => NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r) leftIndicator]
  rw [show (fun bit => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left))))
        (fun r => leftIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r))) =
      (fun bit => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left))))
        leftIndicator) from funext hinner]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype'_apply, Fintype.card_bool, Nat.cast_ofNat]
  rw [show (2 : ℝ≥0∞)⁻¹ = (1/2 : ℝ≥0∞) by norm_num]
  simp only [show (if True then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.right from
      if_pos trivial,
    show (if true = true then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.right from rfl,
    show (if false = true then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.left from by simp,
    advance_right a b ha hb, advance_left a b ha hb]
  exact add_comm _ _

theorem rightEvent_succ (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    rightEvent (n+1) a b =
      (1/2 : ℝ≥0∞) * rightEvent n (a-1) (b+1) + (1/2 : ℝ≥0∞) * rightEvent n (a+1) (b-1) := by
  have hl := law_coin n a b ha hb
  have hinner : ∀ bit : Bool,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left))))
          (fun r => rightIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r)) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left))))
          rightIndicator := by
    intro bit
    apply congrArg (fun g : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control → ℝ≥0∞ =>
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
          (.walk, .move (if bit then .right else .left)))) g)
    funext r
    exact rightIndicator_prepend a b bit r
  unfold rightEvent
  rw [hl]
  rw [expectation_bind_map (PMF.uniformOfFintype' Bool)
    (fun bit => NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
        (.walk, .move (if bit then .right else .left))))
    (fun bit r => NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r) rightIndicator]
  rw [show (fun bit => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left))))
        (fun r => rightIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r))) =
      (fun bit => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left))))
        rightIndicator) from funext hinner]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype'_apply, Fintype.card_bool, Nat.cast_ofNat]
  rw [show (2 : ℝ≥0∞)⁻¹ = (1/2 : ℝ≥0∞) by norm_num]
  simp only [show (if True then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.right from
      if_pos trivial,
    show (if true = true then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.right from rfl,
    show (if false = true then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.left from by simp,
    advance_right a b ha hb, advance_left a b ha hb]
  exact add_comm _ _

theorem iSup_add_of_monotone {x y : ℕ → ℝ≥0∞} (hx : Monotone x) (hy : Monotone y) :
    (⨆ n, (x n + y n)) = (⨆ n, x n) + (⨆ n, y n) := by
  have key : ∀ n, (⨆ m, (x n + y m)) ≤ (⨆ k, (x k + y k)) := by
    intro n
    refine iSup_le (fun m => ?_)
    exact (add_le_add (hx (le_max_left n m)) (hy (le_max_right n m))).trans
      (le_iSup (fun k => x k + y k) (max n m))
  have h2 : (⨆ n, x n) + (⨆ n, y n) = (⨆ n, (⨆ m, (x n + y m))) := by
    rw [ENNReal.iSup_add]
    congr 1
    funext n
    exact ENNReal.add_iSup (a := x n) (fun m => y m)
  have hA : (⨆ n, (x n + y n)) ≤ (⨆ n, x n) + (⨆ n, y n) := by
    refine iSup_le (fun n => ?_)
    exact add_le_add (le_iSup x n) (le_iSup y n)
  have hB : (⨆ n, x n) + (⨆ n, y n) ≤ (⨆ n, (x n + y n)) := by
    rw [h2]
    refine iSup_le (fun n => ?_)
    exact key n
  exact le_antisymm hA hB

theorem iSup_shift {g : ℕ → ℝ≥0∞} (hg : Monotone g) :
    (⨆ n, g (n+1)) = ⨆ n, g n := by
  have h1 : (⨆ n, g (n+1)) ≤ (⨆ m, g m) := by
    refine iSup_le (fun n => ?_)
    exact le_iSup g (n+1)
  have h2 : (⨆ n, g n) ≤ (⨆ n, g (n+1)) := by
    refine iSup_le (fun n => ?_)
    exact (hg (Nat.le_succ n)).trans (le_iSup (fun k => g (k+1)) n)
  exact le_antisymm (by simpa using h1) (by simpa using h2)

theorem leftMass_succ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    leftMass a b = (1/2 : ℝ≥0∞) * leftMass (a-1) (b+1) + (1/2 : ℝ≥0∞) * leftMass (a+1) (b-1) := by
  rw [leftMass_eq_iSup, leftMass_eq_iSup, leftMass_eq_iSup]
  have hmono1 : Monotone (fun n => leftEvent n (a-1) (b+1)) :=
    fun n m h => leftEvent_mono n m (a-1) (b+1) h
  have hmono2 : Monotone (fun n => leftEvent n (a+1) (b-1)) :=
    fun n m h => leftEvent_mono n m (a+1) (b-1) h
  have hshift : (⨆ n, leftEvent n a b) = (⨆ n, leftEvent (n+1) a b) := by
    symm
    exact iSup_shift (fun n m h => leftEvent_mono n m a b h)
  rw [hshift]
  have hrec : (⨆ n, leftEvent (n+1) a b) =
      (⨆ n, ((1/2 : ℝ≥0∞) * leftEvent n (a-1) (b+1) +
        (1/2 : ℝ≥0∞) * leftEvent n (a+1) (b-1))) := by
    apply iSup_congr
    intro n
    exact leftEvent_succ n a b ha hb
  rw [hrec]
  calc (⨆ n, ((1/2 : ℝ≥0∞) * leftEvent n (a-1) (b+1) +
        (1/2 : ℝ≥0∞) * leftEvent n (a+1) (b-1)))
      = (⨆ n, ((1/2 : ℝ≥0∞) * (leftEvent n (a-1) (b+1) + leftEvent n (a+1) (b-1)))) := by
        apply iSup_congr
        intro n
        exact (mul_add _ _ _).symm
    _ = (1/2 : ℝ≥0∞) * (⨆ n, (leftEvent n (a-1) (b+1) + leftEvent n (a+1) (b-1))) :=
        (ENNReal.mul_iSup _ _).symm
    _ = (1/2 : ℝ≥0∞) * ((⨆ n, leftEvent n (a-1) (b+1)) +
        (⨆ n, leftEvent n (a+1) (b-1))) := by
        rw [iSup_add_of_monotone hmono1 hmono2]
    _ = (1/2 : ℝ≥0∞) * (⨆ n, leftEvent n (a-1) (b+1)) +
        (1/2 : ℝ≥0∞) * (⨆ n, leftEvent n (a+1) (b-1)) := mul_add _ _ _

theorem rightMass_succ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    rightMass a b = (1/2 : ℝ≥0∞) * rightMass (a-1) (b+1) + (1/2 : ℝ≥0∞) * rightMass (a+1) (b-1) := by
  rw [rightMass_eq_iSup, rightMass_eq_iSup, rightMass_eq_iSup]
  have hmono1 : Monotone (fun n => rightEvent n (a-1) (b+1)) :=
    fun n m h => rightEvent_mono n m (a-1) (b+1) h
  have hmono2 : Monotone (fun n => rightEvent n (a+1) (b-1)) :=
    fun n m h => rightEvent_mono n m (a+1) (b-1) h
  have hshift : (⨆ n, rightEvent n a b) = (⨆ n, rightEvent (n+1) a b) := by
    symm
    exact iSup_shift (fun n m h => rightEvent_mono n m a b h)
  rw [hshift]
  have hrec : (⨆ n, rightEvent (n+1) a b) =
      (⨆ n, ((1/2 : ℝ≥0∞) * rightEvent n (a-1) (b+1) +
        (1/2 : ℝ≥0∞) * rightEvent n (a+1) (b-1))) := by
    apply iSup_congr
    intro n
    exact rightEvent_succ n a b ha hb
  rw [hrec]
  calc (⨆ n, ((1/2 : ℝ≥0∞) * rightEvent n (a-1) (b+1) +
        (1/2 : ℝ≥0∞) * rightEvent n (a+1) (b-1)))
      = (⨆ n, ((1/2 : ℝ≥0∞) * (rightEvent n (a-1) (b+1) + rightEvent n (a+1) (b-1)))) := by
        apply iSup_congr
        intro n
        exact (mul_add _ _ _).symm
    _ = (1/2 : ℝ≥0∞) * (⨆ n, (rightEvent n (a-1) (b+1) + rightEvent n (a+1) (b-1))) :=
        (ENNReal.mul_iSup _ _).symm
    _ = (1/2 : ℝ≥0∞) * ((⨆ n, rightEvent n (a-1) (b+1)) +
        (⨆ n, rightEvent n (a+1) (b-1))) := by
        rw [iSup_add_of_monotone hmono1 hmono2]
    _ = (1/2 : ℝ≥0∞) * (⨆ n, rightEvent n (a-1) (b+1)) +
        (1/2 : ℝ≥0∞) * (⨆ n, rightEvent n (a+1) (b-1)) := mul_add _ _ _

theorem loaded_q (a b : ℕ) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b).q = .walk := rfl

theorem loaded_head (a b : ℕ) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b).Tape.head = Turing.Tape.head (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a b) := rfl

def leftEndpointResult (b : ℕ) : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control :=
  ⟨⟨.done, (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape 0 b).write .out0⟩, [], .halted,
    [(Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 b, none)]⟩

def rightEndpointResult (a : ℕ) : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control :=
  ⟨⟨.done, (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a 0).write .out1⟩, [], .halted,
    [(Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a 0, none)]⟩

def degenerateResult : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control :=
  ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 0, [], .halted, []⟩

theorem law_halted_cfg (m : ℕ) (T : Turing.Tape Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol) :
    NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program m ⟨.done, T⟩ =
      PMF.pure ⟨⟨.done, T⟩, [], .halted, []⟩ := by
  cases m with
  | zero =>
      simp only [NativeTape.law,
          Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program]
  | succ m =>
      simp only [NativeTape.law,
          Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program]

theorem law_left_endpoint (n b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 b) =
      PMF.pure (leftEndpointResult b) := by
  cases n with
  | zero => omega
  | succ n =>
      have hh := head_left b hb
      have hadv : NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 b) (.done, (.write .out0)) =
          ⟨.done, (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape 0 b).write .out0⟩ := by
        simp [NativeTape.advance,
            Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, TM0StmtApply]
      have hhalt :=
          law_halted_cfg n
          ((Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape 0 b).write .out0)
      simp only [NativeTape.law,
          Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program, loaded_q, loaded_head, hh]
      rw [hadv, hhalt, PMF.pure_map]
      rfl

theorem law_right_endpoint (n a : ℕ) (hn : 0 < n) (ha : 0 < a) :
    NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a 0) =
      PMF.pure (rightEndpointResult a) := by
  cases n with
  | zero => omega
  | succ n =>
      have hh := head_right a ha
      have hadv : NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a 0) (.done, (.write .out1)) =
          ⟨.done, (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a 0).write .out1⟩ := by
        simp [NativeTape.advance,
            Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, TM0StmtApply]
      have hhalt :=
          law_halted_cfg n
          ((Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape a 0).write .out1)
      simp only [NativeTape.law,
          Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program, loaded_q, loaded_head, hh]
      rw [hadv, hhalt, PMF.pure_map]
      rfl

theorem law_degenerate (n : ℕ) :
    NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 0) =
      PMF.pure degenerateResult := by
  have hhead : Turing.Tape.head (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape 0 0) = .blank := by
    simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.positionTape, Turing.Tape.mk₂, Turing.Tape.mk',
      Turing.ListBlank.head_mk]
    rfl
  cases n with
  | zero =>
      simp only [NativeTape.law,
          Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program, loaded_q, loaded_head, hhead]
      rfl
  | succ n =>
      simp only [NativeTape.law,
          Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program, loaded_q, loaded_head, hhead]
      rfl

theorem of_leftEndpointResult (b : ℕ) (hb : 0 < b) :
    RaceOutcome.of (leftEndpointResult b) = .left := by
  have hs : (leftEndpointResult b).stop = .halted := rfl
  have hq : (leftEndpointResult b).cfg.q = .done := rfl
  have hh : (leftEndpointResult b).cfg.Tape.head = .out0 := by
    simp [leftEndpointResult, Turing.Tape.write]
  have hout : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output (leftEndpointResult b) = some false := by
    unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output
    rw [hs, hq, hh]
    rfl
  exact RaceOutcome.of_eq_left _ hout

theorem of_rightEndpointResult (a : ℕ) (ha : 0 < a) :
    RaceOutcome.of (rightEndpointResult a) = .right := by
  have hs : (rightEndpointResult a).stop = .halted := rfl
  have hq : (rightEndpointResult a).cfg.q = .done := rfl
  have hh : (rightEndpointResult a).cfg.Tape.head = .out1 := by
    simp [rightEndpointResult, Turing.Tape.write]
  have hout : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output (rightEndpointResult a) = some true := by
    unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output
    rw [hs, hq, hh]
    rfl
  exact RaceOutcome.of_eq_right _ hout

theorem of_degenerateResult : RaceOutcome.of degenerateResult = .none := by
  have hs : degenerateResult.stop = .halted := rfl
  have hq : degenerateResult.cfg.q = .walk := rfl
  have hout : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output degenerateResult = Option.none := by
    unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output
    rw [hs, hq]
    rfl
  exact RaceOutcome.of_eq_none _ hout

theorem expectation_pure {α : Type} (r : α) (f : α → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.pure r) f = f r := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_eq_single r]
  · simp [PMF.pure_apply]
  · intro b hb
    have h0 : (PMF.pure r) b = 0 := by simp [PMF.pure_apply, hb]
    simp [h0]

theorem leftIndicator_le (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    leftIndicator r ≤ 1 := by
  unfold leftIndicator
  split <;> norm_num

theorem rightIndicator_le (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    rightIndicator r ≤ 1 := by
  unfold rightIndicator
  split <;> norm_num

theorem leftEvent_le_one (n a b : ℕ) : leftEvent n a b ≤ 1 := by
  unfold leftEvent Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  calc ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * leftIndicator r
      ≤ ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 := by
        refine ENNReal.tsum_le_tsum (fun r => ?_)
        exact mul_le_mul_of_nonneg_left (leftIndicator_le r) (bot_le)
    _ = 1 := by
        rw [tsum_congr (fun r => by rw [mul_one])]
        exact (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).tsum_coe

theorem rightEvent_le_one (n a b : ℕ) : rightEvent n a b ≤ 1 := by
  unfold rightEvent Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  calc ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * rightIndicator r
      ≤ ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 := by
        refine ENNReal.tsum_le_tsum (fun r => ?_)
        exact mul_le_mul_of_nonneg_left (rightIndicator_le r) (bot_le)
    _ = 1 := by
        rw [tsum_congr (fun r => by rw [mul_one])]
        exact (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).tsum_coe

theorem leftEvent_zero_budget_right (a : ℕ) (ha : 0 < a) : leftEvent 0 a 0 = 0 := by
  unfold leftEvent
  have hlaw : NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program 0 (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a 0) =
      PMF.pure ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a 0, [], .fuel, []⟩ := by
    simp only [NativeTape.law,
        Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program, loaded_q, loaded_head, head_right a ha]
  rw [hlaw, expectation_pure]
  simp [leftIndicator, RaceOutcome.of,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output]

theorem rightEvent_zero_budget_left (b : ℕ) (hb : 0 < b) : rightEvent 0 0 b = 0 := by
  unfold rightEvent
  have hlaw : NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program 0 (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 b) =
      PMF.pure ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded 0 b, [], .fuel, []⟩ := by
    simp only [NativeTape.law,
        Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program, loaded_q, loaded_head, head_left b hb]
  rw [hlaw, expectation_pure]
  simp [rightIndicator, RaceOutcome.of,
      Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output]

theorem leftEvent_zero_left (n b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    leftEvent n 0 b = 1 := by
  unfold leftEvent
  rw [law_left_endpoint n b hn hb]
  rw [expectation_pure]
  simp [leftIndicator, of_leftEndpointResult b hb]

theorem rightEvent_zero_right (n a : ℕ) (hn : 0 < n) (ha : 0 < a) :
    rightEvent n a 0 = 1 := by
  unfold rightEvent
  rw [law_right_endpoint n a hn ha]
  rw [expectation_pure]
  simp [rightIndicator, of_rightEndpointResult a ha]

theorem leftEvent_zero_right (n a : ℕ) (hn : 0 < n) (ha : 0 < a) :
    leftEvent n a 0 = 0 := by
  unfold leftEvent
  rw [law_right_endpoint n a hn ha]
  rw [expectation_pure]
  simp [leftIndicator, of_rightEndpointResult a ha]

theorem rightEvent_zero_left (n b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    rightEvent n 0 b = 0 := by
  unfold rightEvent
  rw [law_left_endpoint n b hn hb]
  rw [expectation_pure]
  simp [rightIndicator, of_leftEndpointResult b hb]

theorem leftEvent_degenerate (n : ℕ) : leftEvent n 0 0 = 0 := by
  unfold leftEvent
  rw [law_degenerate n]
  rw [expectation_pure]
  simp [leftIndicator, of_degenerateResult]

theorem rightEvent_degenerate (n : ℕ) : rightEvent n 0 0 = 0 := by
  unfold rightEvent
  rw [law_degenerate n]
  rw [expectation_pure]
  simp [rightIndicator, of_degenerateResult]

theorem leftMass_le_one (a b : ℕ) : leftMass a b ≤ 1 := by
  rw [leftMass_eq_iSup]
  exact iSup_le (fun n => leftEvent_le_one n a b)

theorem rightMass_le_one (a b : ℕ) : rightMass a b ≤ 1 := by
  rw [rightMass_eq_iSup]
  exact iSup_le (fun n => rightEvent_le_one n a b)

theorem leftMass_zero_left (b : ℕ) (hb : 0 < b) : leftMass 0 b = 1 := by
  rw [leftMass_eq_iSup]
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun n => leftEvent_le_one n 0 b)
  · have h1 : leftEvent 1 0 b = 1 := leftEvent_zero_left 1 b (by omega) hb
    have hle : leftEvent 1 0 b ≤ ⨆ n, leftEvent n 0 b :=
      le_iSup (fun n => leftEvent n 0 b) 1
    rw [h1] at hle
    exact hle

theorem rightMass_zero_right (a : ℕ) (ha : 0 < a) : rightMass a 0 = 1 := by
  rw [rightMass_eq_iSup]
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun n => rightEvent_le_one n a 0)
  · have h1 : rightEvent 1 a 0 = 1 := rightEvent_zero_right 1 a (by omega) ha
    have hle : rightEvent 1 a 0 ≤ ⨆ n, rightEvent n a 0 :=
      le_iSup (fun n => rightEvent n a 0) 1
    rw [h1] at hle
    exact hle

theorem leftMass_zero_right (a : ℕ) (ha : 0 < a) : leftMass a 0 = 0 := by
  rw [leftMass_eq_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun n => ?_)
    cases n with
    | zero => rw [leftEvent_zero_budget_right a ha]
    | succ n => rw [leftEvent_zero_right (n+1) a (by omega) ha]
  · exact bot_le

theorem rightMass_zero_left (b : ℕ) (hb : 0 < b) : rightMass 0 b = 0 := by
  rw [rightMass_eq_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun n => ?_)
    cases n with
    | zero => rw [rightEvent_zero_budget_left b hb]
    | succ n => rw [rightEvent_zero_left (n+1) b (by omega) hb]
  · exact bot_le

theorem leftMass_degenerate : leftMass 0 0 = 0 := by
  rw [leftMass_eq_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun n => ?_)
    rw [leftEvent_degenerate n]
  · exact bot_le

theorem rightMass_degenerate : rightMass 0 0 = 0 := by
  rw [rightMass_eq_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun n => ?_)
    rw [rightEvent_degenerate n]
  · exact bot_le

noncomputable def leftProb (a b : ℕ) : ℝ := (leftMass a b).toReal

noncomputable def rightProb (a b : ℕ) : ℝ := (rightMass a b).toReal

theorem leftMass_ne_top (a b : ℕ) : leftMass a b ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (leftMass_le_one a b) ENNReal.one_lt_top)

theorem rightMass_ne_top (a b : ℕ) : rightMass a b ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (rightMass_le_one a b) ENNReal.one_lt_top)

theorem leftProb_succ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    leftProb a b = (1/2 : ℝ) * leftProb (a-1) (b+1) + (1/2 : ℝ) * leftProb (a+1) (b-1) := by
  unfold leftProb
  rw [leftMass_succ a b ha hb]
  rw [ENNReal.toReal_add]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    norm_num [ENNReal.toReal_inv]
  · exact ENNReal.mul_ne_top (by simp) (leftMass_ne_top (a-1) (b+1))
  · exact ENNReal.mul_ne_top (by simp) (leftMass_ne_top (a+1) (b-1))

theorem rightProb_succ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    rightProb a b = (1/2 : ℝ) * rightProb (a-1) (b+1) + (1/2 : ℝ) * rightProb (a+1) (b-1) := by
  unfold rightProb
  rw [rightMass_succ a b ha hb]
  rw [ENNReal.toReal_add]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
    norm_num [ENNReal.toReal_inv]
  · exact ENNReal.mul_ne_top (by simp) (rightMass_ne_top (a-1) (b+1))
  · exact ENNReal.mul_ne_top (by simp) (rightMass_ne_top (a+1) (b-1))

theorem harmonic_affine {N : ℕ} (hN : 0 < N) (r : ℕ → ℝ) (c0 cN : ℝ)
    (h0 : r 0 = c0) (hN' : r N = cN)
    (hrec : ∀ i, 1 ≤ i → i < N → r (i-1) + r (i+1) = 2 * r i) :
    ∀ i, i ≤ N → r i = c0 + (cN - c0) * (i / N) := by
  have hdiff : ∀ i, 1 ≤ i → i < N → r (i+1) - r i = r i - r (i-1) := by
    intro i hi hiN
    have h := hrec i hi hiN
    linarith
  have hd : ∀ i, 1 ≤ i → i ≤ N → r i - r (i-1) = r 1 - r 0 := by
    intro i
    induction i with
    | zero => intro hi hiN; omega
    | succ i ih =>
        intro hi hiN
        by_cases h1 : i = 0
        · subst h1
          simp
        · have hi2 : 1 ≤ i := by omega
          have hiN' : i < N := by omega
          have hid : (i+1) - 1 = i := by omega
          rw [hid]
          rw [hdiff i hi2 hiN']
          exact ih (by omega) (by omega)
  have hmain : ∀ i, i ≤ N → r i = r 0 + (i : ℝ) * (r 1 - r 0) := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ i ih =>
        intro hi
        by_cases h0i : i = 0
        · subst h0i
          ring
        · have hi1 : 1 ≤ i := by omega
          have hiN' : i < N := by omega
          have hrec' := hrec i hi1 hiN'
          have hd1 : r (i+1) - r i = r 1 - r 0 := hd (i+1) (by omega) (by omega)
          have hstep : r (i+1) = r i + (r 1 - r 0) := by linarith
          rw [hstep, ih (by omega)]
          push_cast
          ring
  intro i hi
  have hm := hmain i hi
  have hNv : r 0 + (N : ℝ) * (r 1 - r 0) = cN := by
    have hNval := hmain N (le_refl N)
    rw [hN'] at hNval
    exact hNval.symm
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hlin : (N : ℝ) * (r 1 - r 0) = cN - c0 := by
    have hNv' : c0 + (N : ℝ) * (r 1 - c0) = cN := by
      rw [← h0]
      exact hNv
    have h2 : (N : ℝ) * (r 1 - c0) = cN - c0 := by linarith [hNv']
    rw [h0]
    exact h2
  have hd1 : r 1 - r 0 = (cN - c0) / N := by
    field_simp
    simpa [mul_comm] using hlin
  rw [hm, hd1, h0]
  field_simp <;> ring

theorem leftProb_eq (a b : ℕ) (hab : 0 < a + b) :
    leftProb a b = (b : ℝ) / (a + b : ℝ) := by
  have hN : 0 < a + b := hab
  have hq0 : (fun i => leftProb i (a + b - i)) 0 = 1 := by
    show leftProb 0 (a + b - 0) = 1
    rw [show a + b - 0 = a + b by omega]
    rw [leftProb, leftMass_zero_left (a + b) (by omega)]
    simp
  have hqN : (fun i => leftProb i (a + b - i)) (a + b) = 0 := by
    show leftProb (a + b) (a + b - (a + b)) = 0
    rw [show a + b - (a + b) = 0 by omega]
    rw [leftProb, leftMass_zero_right (a + b) (by omega)]
    simp
  have hrec : ∀ i, 1 ≤ i → i < a + b →
      (fun j => leftProb j (a + b - j)) (i-1) + (fun j => leftProb j (a + b - j)) (i+1) =
        2 * (fun j => leftProb j (a + b - j)) i := by
    intro i hi hiN
    have hia : 0 < i := hi
    have hib : 0 < a + b - i := by omega
    have hstep := leftProb_succ i (a + b - i) hia hib
    have h1 : a + b - (i-1) = a + b - i + 1 := by omega
    have h2 : a + b - (i+1) = a + b - i - 1 := by omega
    show leftProb (i-1) (a + b - (i-1)) + leftProb (i+1) (a + b - (i+1)) =
      2 * leftProb i (a + b - i)
    rw [h1, h2]
    linarith [hstep]
  have hharm := harmonic_affine (N := a + b) hN (fun i => leftProb i (a + b - i)) 1 0
    hq0 hqN hrec
  have hval := hharm a (by omega)
  have hval0 : leftProb a (a + b - a) = 1 + (0 - 1) * ((a : ℝ) / ((a + b : ℕ) : ℝ)) := by
    simpa using (hharm a (by omega))
  have hba : a + b - a = b := by omega
  rw [hba] at hval0
  have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
  have hval' : leftProb a b = 1 - (a : ℝ) / ((a + b : ℕ) : ℝ) := by linarith
  rw [hval']
  have hcast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by
    exact_mod_cast (Nat.cast_add a b)
  rw [hcast]
  field_simp <;> ring

theorem rightProb_eq (a b : ℕ) (hab : 0 < a + b) :
    rightProb a b = (a : ℝ) / (a + b : ℝ) := by
  have hN : 0 < a + b := hab
  have hq0 : (fun i => rightProb i (a + b - i)) 0 = 0 := by
    show rightProb 0 (a + b - 0) = 0
    rw [show a + b - 0 = a + b by omega]
    rw [rightProb, rightMass_zero_left (a + b) (by omega)]
    simp
  have hqN : (fun i => rightProb i (a + b - i)) (a + b) = 1 := by
    show rightProb (a + b) (a + b - (a + b)) = 1
    rw [show a + b - (a + b) = 0 by omega]
    rw [rightProb, rightMass_zero_right (a + b) (by omega)]
    simp
  have hrec : ∀ i, 1 ≤ i → i < a + b →
      (fun j => rightProb j (a + b - j)) (i-1) + (fun j => rightProb j (a + b - j)) (i+1) =
        2 * (fun j => rightProb j (a + b - j)) i := by
    intro i hi hiN
    have hia : 0 < i := hi
    have hib : 0 < a + b - i := by omega
    have hstep := rightProb_succ i (a + b - i) hia hib
    have h1 : a + b - (i-1) = a + b - i + 1 := by omega
    have h2 : a + b - (i+1) = a + b - i - 1 := by omega
    show rightProb (i-1) (a + b - (i-1)) + rightProb (i+1) (a + b - (i+1)) =
      2 * rightProb i (a + b - i)
    rw [h1, h2]
    linarith [hstep]
  have hharm := harmonic_affine (N := a + b) hN (fun i => rightProb i (a + b - i)) 0 1
    hq0 hqN hrec
  have hval := hharm a (by omega)
  have hval0 : rightProb a (a + b - a) = 0 + (1 - 0) * ((a : ℝ) / ((a + b : ℕ) : ℝ)) := by
    simpa using (hharm a (by omega))
  have hba : a + b - a = b := by omega
  rw [hba] at hval0
  have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
  have hval' : rightProb a b = (a : ℝ) / ((a + b : ℕ) : ℝ) := by linarith
  rw [hval']
  have hcast : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by
    exact_mod_cast (Nat.cast_add a b)
  rw [hcast]

theorem clause23_complete : ∀ a b : ℕ,
    (0 < a + b →
      leftMass a b = ENNReal.ofReal ((b : ℝ) / (a + b : ℝ)) ∧
      rightMass a b = ENNReal.ofReal ((a : ℝ) / (a + b : ℝ))) ∧
    (a + b = 0 → leftMass a b = 0 ∧ rightMass a b = 0) := by
  intro a b
  constructor
  · intro h
    constructor
    · rw [← ENNReal.ofReal_toReal (leftMass_ne_top a b)]
      exact congrArg ENNReal.ofReal (leftProb_eq a b h)
    · rw [← ENNReal.ofReal_toReal (rightMass_ne_top a b)]
      exact congrArg ENNReal.ofReal (rightProb_eq a b h)
  · intro h
    have h1 : a = 0 := by omega
    have h2 : b = 0 := by omega
    subst h1
    subst h2
    exact ⟨leftMass_degenerate, rightMass_degenerate⟩

theorem leftMass_add_rightMass (a b : ℕ) (hab : 0 < a + b) :
    leftMass a b + rightMass a b = 1 := by
  have htoReal : (leftMass a b + rightMass a b).toReal = 1 := by
    rw [ENNReal.toReal_add (leftMass_ne_top a b) (rightMass_ne_top a b)]
    show leftProb a b + rightProb a b = 1
    rw [leftProb_eq a b hab, rightProb_eq a b hab]
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hab
    field_simp
    ring
  calc leftMass a b + rightMass a b
      = ENNReal.ofReal ((leftMass a b + rightMass a b).toReal) :=
        (ENNReal.ofReal_toReal ((ENNReal.add_ne_top).mpr
          ⟨leftMass_ne_top a b, rightMass_ne_top a b⟩)).symm
    _ = ENNReal.ofReal 1 := by rw [htoReal]
    _ = 1 := by simp

theorem indicator_sum_le_one (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    leftIndicator r + rightIndicator r ≤ 1 := by
  by_cases h1 : RaceOutcome.of r = .left
  · rw [leftIndicator, if_pos h1]
    have h2 : RaceOutcome.of r ≠ .right := by
      intro h2r
      rw [h1] at h2r
      exact RaceOutcome.noConfusion h2r
    rw [rightIndicator, if_neg h2]
    norm_num
  · by_cases h2 : RaceOutcome.of r = .right
    · rw [leftIndicator, if_neg h1, rightIndicator, if_pos h2]
      norm_num
    · rw [leftIndicator, if_neg h1, rightIndicator, if_neg h2]
      norm_num

theorem haltedMass_pointwise (a b : ℕ)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
        (leftIndicator r + rightIndicator r) ≤
      NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r := by
  have hge : ∀ n : ℕ,
      (NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          (leftIndicator r + rightIndicator r) ≤
        (⨆ m : ℕ, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program m (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) := by
    intro n
    by_cases hr : r.stop = .halted
    · rw [NativeTape.finishedMass, if_pos hr]
      have hmul : (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
            (leftIndicator r + rightIndicator r) ≤
          (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 :=
        mul_le_mul_of_nonneg_left (indicator_sum_le_one r) (bot_le)
      calc (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
            (leftIndicator r + rightIndicator r) ≤
          (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 := hmul
        _ = _ := by rw [mul_one]
        _ ≤ (⨆ m : ℕ, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program m (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) := by
          have hle' : NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r ≤
              (⨆ m : ℕ, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program m (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) :=
            le_iSup (fun m => NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program m (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) n
          simpa [NativeTape.finishedMass, hr] using hle'
    · rw [NativeTape.finishedMass, if_neg hr]
      simp
  unfold NativeTape.haltedMass
  rw [ENNReal.iSup_mul]
  show (⨆ n : ℕ, (NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
        (leftIndicator r + rightIndicator r)) ≤
      (⨆ n : ℕ, NativeTape.finishedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r)
  exact iSup_le hge

theorem haltedMass_sum_eq_one (a b : ℕ) (hab : 0 < a + b) :
    (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) = 1 := by
  have hsum : leftMass a b + rightMass a b ≤
      (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) := by
    calc leftMass a b + rightMass a b
        = ∑' r, (NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
            (leftIndicator r + rightIndicator r)) := by
          unfold leftMass rightMass
          rw [← ENNReal.tsum_add]
          apply tsum_congr
          intro r
          rw [mul_add]
        _ ≤ ∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r := by
          refine ENNReal.tsum_le_tsum (fun r => ?_)
          exact haltedMass_pointwise a b r
  have hle : (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) ≤ 1 :=
    NativeTape.haltedMass_sum_le_one Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
  rw [leftMass_add_rightMass a b hab] at hsum
  exact le_antisymm hle hsum

theorem clause24_complete : ∀ a b : ℕ, 0 < a + b →
    raceNeverMass a b = 0 ∧
    (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) = 1 := by
  intro a b hab
  constructor
  · unfold raceNeverMass
    rw [NativeTape.neverMass, haltedMass_sum_eq_one a b hab]
    simp
  · exact haltedMass_sum_eq_one a b hab

theorem encoded_ledger (A B n : ℕ) (ha : 0 < A) (hb : 0 < B) (bs : List Bool) :
    (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A+1+n) bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).steps =
      (A+1) + (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A+1+n) bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).bits.length +
        (if (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs A B).out.isSome then 1 else 0) := by
  have h := Qatlib.Concepts.AdversaryBounds.AdvDuality.positive_clock (A-1) (B-1) n bs
  simpa [show (A - 1) + 2 = A + 1 by omega, show (A - 1) + 1 = A by omega,
    show (B - 1) + 1 = B by omega] using h

theorem loaded_workspace (n a b : ℕ) (bs : List Bool) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.workspace a b
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).trace).card = a + b + 1 := by
  exact Qatlib.Concepts.AdversaryBounds.AdvDuality.walk_workspace_card n bs a b

theorem leftEvent_le_leftMass (n a b : ℕ) : leftEvent n a b ≤ leftMass a b := by
  rw [leftMass_eq_iSup]
  exact le_iSup (fun m => leftEvent m a b) n

theorem rightEvent_le_rightMass (n a b : ℕ) : rightEvent n a b ≤ rightMass a b := by
  rw [rightMass_eq_iSup]
  exact le_iSup (fun m => rightEvent m a b) n

theorem outcome_sum_eq_one (a b : ℕ) (hab : 0 < a + b) :
    leftMass a b + rightMass a b = 1 :=
  leftMass_add_rightMass a b hab

end Qatlib.Concepts.AdversaryBounds.AdvDuality
