/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNative

/-!
# Native weighted sampling laws

This module defines the probability laws and outcome observables for the native fair-bit race.
`RaceOutcome` classifies decoded results, `raceLaw` retains terminal executions and
nontermination, and `outcomeLaw` maps them to left, right, or no decoded outcome. The native
machine representation belongs to the classical computation setting discussed in
[KitaevShenVyalyi2002].

The declarations `leftMass` and `rightMass` collect the eventual masses of the two outcomes,
while `leftEvent` and `rightEvent` measure the corresponding events under a bounded execution
law. `raceNeverMass` records nontermination, and `encodedWeight` and `encodedInput` describe the
input representation used by later sampling proofs.

## Main statements

* `RaceOutcome.of_eq_left`, `RaceOutcome.of_eq_right`, and `RaceOutcome.of_eq_none` relate
  decoding to the three outcome constructors.
* `raceLaw`, `outcomeLaw`, `leftMass`, and `rightMass` provide the terminal laws and outcome
  masses.
* `encodedInput_length` gives the exact input length for positive weights, and
  `encodedInput_length_le` bounds it for all weights.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

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

/-- The decoded race outcome: left, right, or no decoded Boolean output. -/
inductive RaceOutcome
  | left | right | none
  deriving DecidableEq, Fintype, Inhabited

/-- Classifies a native execution result by its decoded output, sending `some false` to left,
`some true` to right, and absent output to none. -/
def RaceOutcome.of (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : RaceOutcome :=
  match Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | some false => .left
  | some true => .right
  | Option.none => .none

/-- A native result with decoded output `some false` is classified as a left outcome. -/
theorem RaceOutcome.of_eq_left (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some false) : RaceOutcome.of r = .left := by
  cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => simp [RaceOutcome.of, hu] at h
  | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢

/-- A native result with decoded output `some true` is classified as a right outcome. -/
theorem RaceOutcome.of_eq_right (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some true) : RaceOutcome.of r = .right := by
  cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => simp [RaceOutcome.of, hu] at h
  | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢

/-- A native result with no decoded output is classified as having no race outcome. -/
theorem RaceOutcome.of_eq_none (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)
    (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = Option.none) : RaceOutcome.of r = .none := by
  cases hu : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => simp [RaceOutcome.of, hu]
  | some b => cases b <;> simp [RaceOutcome.of, hu] at h ⊢

/-- A result whose decoded output is either Boolean value has either a left or a right race
outcome. -/
theorem RaceOutcome.of_eq_left_or_right {r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control} (h : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some false ∨
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = some true) :
    RaceOutcome.of r = .left ∨ RaceOutcome.of r = .right := by
  rcases h with h | h
  · exact Or.inl (RaceOutcome.of_eq_left r h)
  · exact Or.inr (RaceOutcome.of_eq_right r h)

/-- The terminal law of the native race program started at `loaded a b`, with nontermination
represented by the outer `Option.none`. -/
noncomputable def raceLaw (a b : ℕ) :
    PMF (Option (NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control)) :=
  NativeTape.terminalLaw Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)

/-- The race law mapped to decoded outcomes, assigning `RaceOutcome.none` to nontermination and
to results with no decoded output. -/
noncomputable def outcomeLaw (a b : ℕ) : PMF RaceOutcome :=
  (raceLaw a b).map (fun z => match z with
    | some r => RaceOutcome.of r
    | Option.none => .none)

/-- The extended nonnegative real indicator of a result having the left race outcome. -/
def leftIndicator (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : ℝ≥0∞ :=
  if RaceOutcome.of r = .left then 1 else 0

/-- The extended nonnegative real indicator of a result having the right race outcome. -/
def rightIndicator (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) : ℝ≥0∞ :=
  if RaceOutcome.of r = .right then 1 else 0

/-- The total halted mass of results with left outcome for the race started at `loaded a b`. -/
noncomputable def leftMass (a b : ℕ) : ℝ≥0∞ :=
  ∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r * leftIndicator r

/-- The total halted mass of results with right outcome for the race started at `loaded a b`. -/
noncomputable def rightMass (a b : ℕ) : ℝ≥0∞ :=
  ∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r * rightIndicator r

/-- The expectation of the left-outcome indicator under the execution law with budget `n`
started at `loaded a b`. -/
noncomputable def leftEvent (n a b : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b))
    leftIndicator

/-- The expectation of the right-outcome indicator under the execution law with budget `n`
started at `loaded a b`. -/
noncomputable def rightEvent (n a b : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b))
    rightIndicator

/-- The nontermination mass of the native race program started at `loaded a b`. -/
noncomputable def raceNeverMass (a b : ℕ) : ℝ≥0∞ :=
  NativeTape.neverMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)

/-- The total encoded weight `a + b` of the two endpoint distances. -/
def encodedWeight (a b : ℕ) : ℕ := a + b

/-- The native input word encoding the two weights, defined by `RandomBitsNativeDefs.inputWord a
b`. -/
def encodedInput (a b : ℕ) :
    List Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol :=
    Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.inputWord a b

/-- For positive weights `a` and `b`, the encoded input length is the total encoded weight plus
one. -/
theorem encodedInput_length (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (encodedInput a b).length = encodedWeight a b + 1 := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  subst ha'
  subst hb'
  simp [encodedInput, encodedWeight, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.inputWord, List.length_append,
    List.length_replicate]
  omega

/-- For arbitrary weights, the encoded input length is at most the total encoded weight plus
three. -/
theorem encodedInput_length_le (a b : ℕ) :
    (encodedInput a b).length ≤ encodedWeight a b + 3 := by
  cases a <;> cases b <;>
    simp [encodedInput, encodedWeight, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.inputWord, List.length_append,
      List.length_replicate] <;> omega

end Qatlib.Concepts.AdversaryBounds.AdvDuality
