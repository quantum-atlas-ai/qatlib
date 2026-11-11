/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Selecting a finite input table

This module defines `select` by taking the inputs whose indices under `Fintype.equivFin` are
less than `k`. It supplies concrete input tables for the collision and claw algorithms of
[BrassardHoyerTapp1998Collision].

The results `select_card` and `select_nonempty` establish the size and nonemptiness needed by
subsequent algorithm constructions.

## Main statements

* `select_card`: If `k` does not exceed the domain cardinality, `select k` has exactly `k`
  elements.
* `select_nonempty`: If `0 < k ≤ Fintype.card X`, the selected input set is nonempty.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.InputSelection
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The finite set of inputs whose indices under `Fintype.equivFin` are strictly less than `k`. -/
def select (k : ℕ) : Finset X := Finset.univ.filter fun x => (Fintype.equivFin X x).val < k

omit [DecidableEq X] in

/-- If `k` does not exceed the domain cardinality, `select k` has exactly `k` elements. -/
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

/-- If `0 < k ≤ Fintype.card X`, the selected input set is nonempty. -/
theorem select_nonempty (k : ℕ) (hk0 : 0 < k) (hk : k ≤ Fintype.card X) :
    (select (X := X) k).Nonempty := by
  apply Finset.card_pos.mp
  rw [select_card k hk]
  exact hk0

end Qatlib.Papers.CollisionProb97.MainResults.InputSelection
