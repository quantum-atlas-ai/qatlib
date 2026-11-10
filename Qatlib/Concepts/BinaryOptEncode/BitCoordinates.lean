/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false
namespace Qatlib.Concepts.BinaryOptEncode.BitCoordinates
open scoped BigOperators

def Spin := {s : ℤ // s = 1 ∨ s = -1}

def boolSpinEquiv : Bool ≃ Spin where
  toFun b := ⟨if b then 1 else -1, by cases b <;> simp⟩
  invFun s := decide (s.val = 1)
  left_inv b := by cases b <;> decide
  right_inv s := by
    apply Subtype.ext
    rcases s.property with h | h <;> simp [h]

instance spin_fintype : Fintype Spin := Fintype.ofEquiv Bool boolSpinEquiv

def spinAssignments (I : Type*) : (I → Bool) ≃ (I → Spin) :=
  Equiv.piCongrRight fun _ => boolSpinEquiv

theorem family_card {T : Type*} [Fintype T] (D : T → Type*) [∀ t, Fintype (D t)] :
    Fintype.card (Sigma D) = ∑ t, Fintype.card (D t) := Fintype.card_sigma

theorem spinAssignment_card (I : Type*) [Fintype I] [DecidableEq I] :
    Fintype.card (I → Spin) = 2 ^ Fintype.card I := by
  calc
    Fintype.card (I → Spin) = Fintype.card (I → Bool) :=
      (Fintype.card_congr (spinAssignments I)).symm
    _ = 2 ^ Fintype.card I := by simp

end Qatlib.Concepts.BinaryOptEncode.BitCoordinates
