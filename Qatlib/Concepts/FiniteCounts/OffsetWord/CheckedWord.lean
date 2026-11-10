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

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

abbrev Instruction (G : Type*) := Bool × G

def badInputs (B : G) : Finset G := {0, B, -B, -(B + B)}

theorem badInputs_card (B : G) : (badInputs B).card ≤ 4 := by
  unfold badInputs
  exact (Finset.card_insert_le _ _).trans (by
    have := Finset.card_insert_le B ({-B, -(B+B)} : Finset G)
    have := Finset.card_insert_le (-B) ({-(B+B)} : Finset G)
    simp only [Finset.card_singleton] at *
    omega)

def checkedRun (a : G) : List (Instruction G) → Option G
  | [] => some a
  | (c, B) :: w => if c then
      if a ∈ badInputs B then none else checkedRun (a + B) w
    else checkedRun a w

def idealRun (a : G) : List (Instruction G) → G
  | [] => a
  | (c, B) :: w => idealRun (if c then a + B else a) w

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

def unsafeOffsets : List (Instruction G) → Finset G
  | [] => ∅
  | (c, B) :: w => if c then
      badInputs B ∪ (unsafeOffsets w).image (fun z => z - B)
    else unsafeOffsets w

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

noncomputable def nonzeroFailureProbability (w : List (Instruction G)) : ℝ :=
  (((unsafeOffsets w).erase 0).card : ℝ) / (Fintype.card G - 1 : ℕ)

theorem random_offset_failure_le (w : List (Instruction G)) :
    nonzeroFailureProbability w ≤ (4 * w.length : ℕ) / (Fintype.card G - 1 : ℕ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_erase_le.trans (unsafeOffsets_card w))

omit [Fintype G] in

theorem checkedRun_translation (w : List (Instruction G)) (a z : G)
    (h : checkedRun a w = some z) : z = a + idealRun 0 w := by
  rw [← checkedRun_sound w a z h]
  exact idealRun_translate w a

end Qatlib.Concepts.FiniteCounts.OffsetWord
