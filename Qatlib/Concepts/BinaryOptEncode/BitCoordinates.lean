/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Boolean and spin coordinates

This module identifies Boolean coordinates with integer spins taking values in {−1, 1}. The
equivalence `boolSpinEquiv` sends false to −1 and true to 1, and `spinAssignments` extends it
pointwise to indexed assignments. These coordinate conventions support binary optimization
encodings such as those considered in [SongEtAl2023].

## Main statements

* `family_card`: the cardinality of a finite dependent sum is the sum of its fiber
  cardinalities.
* `spinAssignment_card`: a finite index type I has 2^|I| spin assignments.

## References

* [Song et al., 2023][SongEtAl2023]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.BinaryOptEncode.BitCoordinates
open scoped BigOperators

/-- The type of integer spins with values 1 or −1. -/
def Spin := {s : ℤ // s = 1 ∨ s = -1}

/-- The equivalence between Booleans and spins sending false to −1 and true to 1. -/
def boolSpinEquiv : Bool ≃ Spin where
  toFun b := ⟨if b then 1 else -1, by cases b <;> simp⟩
  invFun s := decide (s.val = 1)
  left_inv b := by cases b <;> decide
  right_inv s := by
    apply Subtype.ext
    rcases s.property with h | h <;> simp [h]

instance spin_fintype : Fintype Spin := Fintype.ofEquiv Bool boolSpinEquiv

/-- The pointwise equivalence between Boolean assignments and spin assignments on the same index
type. -/
def spinAssignments (I : Type*) : (I → Bool) ≃ (I → Spin) :=
  Equiv.piCongrRight fun _ => boolSpinEquiv

/-- The cardinality of a dependent sum over a finite base is the sum of the cardinalities of its
finite fibers. -/
theorem family_card {T : Type*} [Fintype T] (D : T → Type*) [∀ t, Fintype (D t)] :
    Fintype.card (Sigma D) = ∑ t, Fintype.card (D t) := Fintype.card_sigma

/-- The number of spin assignments on a finite index type I is 2 raised to the cardinality of I. -/
theorem spinAssignment_card (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype.card (I → Spin) = 2 ^ Fintype.card I := by
  calc
    Fintype.card (I → Spin) = Fintype.card (I → Bool) :=
      (Fintype.card_congr (spinAssignments I)).symm
    _ = 2 ^ Fintype.card I := by simp

end Qatlib.Concepts.BinaryOptEncode.BitCoordinates
