/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-!
# Checked translation words and unsafe offsets

This module defines Boolean-controlled translations in an additive commutative group.
`checkedRun` stops at one of four exceptional inputs for an enabled increment, while `idealRun`
executes the translations without checks. The recursively computed `unsafeOffsets` characterizes
failure exactly.

For finite groups, counting unsafe nonzero offsets yields `nonzeroFailureProbability` and a
bound proportional to word length. The construction abstracts the exceptional-input analysis
motivating random offsets in [RoettelerEtAl2017].

## Main statements

* `checkedRun_sound`: every successful checked execution agrees with ideal execution.
* `checkedRun_eq_none`: failure is equivalent to membership in `unsafeOffsets`.
* `unsafeOffsets_card`: at most four unsafe offsets are introduced per instruction.
* `random_offset_failure_le`: bound the nonzero-offset failure ratio by the word length.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A Boolean control paired with a group increment. -/
abbrev Instruction (G : Type*) := Bool × G

/-- The exceptional inputs `0`, `B`, `-B`, and `-(B + B)` for translation by `B`. -/
def badInputs (B : G) : Finset G := {0, B, -B, -(B + B)}

/-- There are at most four exceptional inputs for each increment. -/
theorem badInputs_card (B : G) : (badInputs B).card ≤ 4 := by
  unfold badInputs
  exact (Finset.card_insert_le _ _).trans (by
    have := Finset.card_insert_le B ({-B, -(B+B)} : Finset G)
    have := Finset.card_insert_le (-B) ({-(B+B)} : Finset G)
    simp only [Finset.card_singleton] at *
    omega)

/-- Execute controlled translations, returning `none` when an enabled increment encounters an
exceptional input. -/
def checkedRun (a : G) : List (Instruction G) → Option G
  | [] => some a
  | (c, B) :: w => if c then
      if a ∈ badInputs B then none else checkedRun (a + B) w
    else checkedRun a w

/-- Execute controlled translations without checking exceptional inputs. -/
def idealRun (a : G) : List (Instruction G) → G
  | [] => a
  | (c, B) :: w => idealRun (if c then a + B else a) w

/-- Every successful checked execution agrees with ideal execution. -/
theorem checkedRun_sound (w : List (Instruction G)) (a z : G)
    (h : checkedRun a w = some z) : idealRun a w = z := by
  induction w generalizing a with
  | nil => simpa [checkedRun, idealRun] using h
  | cons s w ih =>
    obtain ⟨c, B⟩ := s
    cases c
    · exact ih a (by simpa [checkedRun] using h)
    · by_cases hb : a ∈ badInputs B
      · simp [checkedRun, hb] at h
      · exact ih (a + B) (by simpa [checkedRun, hb] using h)

/-- The finite set of initial offsets causing checked execution to fail, computed by pulling
back later failures through enabled translations. -/
def unsafeOffsets : List (Instruction G) → Finset G
  | [] => ∅
  | (c, B) :: w => if c then
      badInputs B ∪ (unsafeOffsets w).image (fun z => z - B)
    else unsafeOffsets w

/-- Checked execution fails exactly on the unsafe offsets. -/
theorem checkedRun_eq_none (w : List (Instruction G)) (a : G) :
    checkedRun a w = none ↔ a ∈ unsafeOffsets w := by
  induction w generalizing a with
  | nil => simp [checkedRun, unsafeOffsets]
  | cons s w ih =>
    obtain ⟨c, B⟩ := s
    cases c
    · simpa [checkedRun, unsafeOffsets] using ih a
    · simp only [checkedRun, ↓reduceIte, unsafeOffsets, Finset.mem_union]
      by_cases hb : a ∈ badInputs B
      · simp [hb]
      · simp only [hb, ↓reduceIte, false_or, ih]
        constructor
        · intro ha
          exact Finset.mem_image.mpr ⟨a + B, ha, add_sub_cancel_right a B⟩
        · intro ha
          obtain ⟨z, hz, he⟩ := Finset.mem_image.mp ha
          have : z = a + B := (sub_eq_iff_eq_add.mp he).symm.symm
          simpa [this] using hz

/-- The number of unsafe offsets is at most four times the word length. -/
theorem unsafeOffsets_card (w : List (Instruction G)) :
    (unsafeOffsets w).card ≤ 4 * w.length := by
  induction w with
  | nil => simp [unsafeOffsets]
  | cons s w ih =>
    obtain ⟨c, B⟩ := s
    cases c
    · simp only [unsafeOffsets, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [unsafeOffsets, ↓reduceIte, List.length_cons]
      calc
        _ ≤ (badInputs B).card + ((unsafeOffsets w).image (fun z => z - B)).card :=
          Finset.card_union_le _ _
        _ ≤ 4 + (unsafeOffsets w).card :=
          Nat.add_le_add (badInputs_card B) Finset.card_image_le
        _ ≤ 4 * (w.length + 1) := by omega

omit [DecidableEq G] in

/-- Ideal execution is translation by the result obtained from the zero offset. -/
theorem idealRun_translate (w : List (Instruction G)) (a : G) :
    idealRun a w = a + idealRun 0 w := by
  induction w generalizing a with
  | nil => simp [idealRun]
  | cons s w ih =>
    obtain ⟨c, B⟩ := s
    cases c <;> simp only [idealRun, Bool.false_eq_true, ↓reduceIte]
    · exact ih a
    · rw [zero_add, ih (a+B), ih B]
      simp [add_assoc]

variable [Fintype G]

/-- The ratio of the number of nonzero unsafe offsets to the number of nonzero group elements. -/
noncomputable def nonzeroFailureProbability (w : List (Instruction G)) : ℝ :=
  (((unsafeOffsets w).erase 0).card : ℝ) / (Fintype.card G - 1 : ℕ)

/-- The nonzero failure ratio is bounded by four times the word length divided by the number of
nonzero group elements. -/
theorem random_offset_failure_le (w : List (Instruction G)) :
    nonzeroFailureProbability w ≤ (4 * w.length : ℕ) / (Fintype.card G - 1 : ℕ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_erase_le.trans (unsafeOffsets_card w))

omit [Fintype G] in

/-- A successful checked execution translates the initial offset by the ideal result from zero. -/
theorem checkedRun_translation (w : List (Instruction G)) (a z : G)
    (h : checkedRun a w = some z) : z = a + idealRun 0 w := by
  rw [← checkedRun_sound w a z h]
  exact idealRun_translate w a

end Qatlib.Concepts.FiniteCounts.OffsetWord
