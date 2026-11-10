/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNative
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib
open Qatlib
open scoped ENNReal

inductive RaceOutcome
  | left | right | none
  deriving DecidableEq, Fintype, Inhabited

def RaceOutcome.of (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : RaceOutcome :=
  match Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | some false => .left
  | some true => .right
  | Option.none => .none

theorem RaceOutcome.of_eq_left (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some false) : RaceOutcome.of r = .left := by
  cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => simp [RaceOutcome.of, hu] at h
  | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢

theorem RaceOutcome.of_eq_right (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some true) : RaceOutcome.of r = .right := by
  cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => simp [RaceOutcome.of, hu] at h
  | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢

theorem RaceOutcome.of_eq_none (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = Option.none) : RaceOutcome.of r = .none := by
  cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => simp [RaceOutcome.of, hu]
  | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢

theorem RaceOutcome.of_eq_left_or_right {r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control} (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some false ∨
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some true) :
    RaceOutcome.of r = .left ∨ RaceOutcome.of r = .right := by
  rcases h with h | h
  · exact Or.inl (RaceOutcome.of_eq_left r h)
  · exact Or.inr (RaceOutcome.of_eq_right r h)

noncomputable def raceLaw (a b : ℕ) :
    PMF (Option (NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)) :=
  NativeTape.terminalLaw Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)

noncomputable def outcomeLaw (a b : ℕ) : PMF RaceOutcome :=
  (raceLaw a b).map (fun z => match z with
    | some r => RaceOutcome.of r
    | Option.none => .none)

def leftIndicator (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : ℝ≥0∞ :=
  if RaceOutcome.of r = .left then 1 else 0

def rightIndicator (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : ℝ≥0∞ :=
  if RaceOutcome.of r = .right then 1 else 0

noncomputable def leftMass (a b : ℕ) : ℝ≥0∞ :=
  ∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r * leftIndicator r

noncomputable def rightMass (a b : ℕ) : ℝ≥0∞ :=
  ∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r * rightIndicator r

noncomputable def leftEvent (n a b : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b))
    leftIndicator

noncomputable def rightEvent (n a b : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b))
    rightIndicator

noncomputable def raceNeverMass (a b : ℕ) : ℝ≥0∞ :=
  NativeTape.neverMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)

def encodedWeight (a b : ℕ) : ℕ := a + b

def encodedInput (a b : ℕ) :
    List Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol :=
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.inputWord a b

theorem encodedInput_length (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (encodedInput a b).length = encodedWeight a b + 1 := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  subst ha'
  subst hb'
  simp [encodedInput, encodedWeight, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.inputWord, List.length_append,
    List.length_replicate]
  omega

theorem encodedInput_length_le (a b : ℕ) :
    (encodedInput a b).length ≤ encodedWeight a b + 3 := by
  cases a <;> cases b <;>
    simp [encodedInput, encodedWeight, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.inputWord, List.length_append,
      List.length_replicate] <;> omega

end Qatlib.Concepts.AdversaryBounds.AdvDuality
