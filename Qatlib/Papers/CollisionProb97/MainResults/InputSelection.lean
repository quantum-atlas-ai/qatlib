/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.InputSelection
variable {X : Type} [Fintype X] [DecidableEq X]

def select (k : ℕ) : Finset X := Finset.univ.filter fun x => (Fintype.equivFin X x).val < k

omit [DecidableEq X] in

theorem select_card (k : ℕ) (hk : k ≤ Fintype.card X) : (select (X := X) k).card = k := by
  suffices he : (select (X := X) k).card = (Finset.range k).card by simpa using he
  apply Finset.card_bij (fun x _ => (Fintype.equivFin X x).val)
  · intro x hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  · intro x _ y _ he
    exact (Fintype.equivFin X).injective (Fin.ext he)
  · intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    let x := (Fintype.equivFin X).symm ⟨i,lt_of_lt_of_le hik hk⟩
    refine ⟨x, ?_, ?_⟩
    · simp [select, x, hik]
    · simp [x]

omit [DecidableEq X] in

theorem select_nonempty (k : ℕ) (hk0 : 0 < k) (hk : k ≤ Fintype.card X) :
    (select (X := X) k).Nonempty := by
  apply Finset.card_pos.mp
  rw [select_card k hk]
  exact hk0

end Qatlib.Papers.CollisionProb97.MainResults.InputSelection
