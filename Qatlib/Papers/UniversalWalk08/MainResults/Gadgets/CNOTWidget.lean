/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.Gadgets.GateWidgets
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic

/-!
# Controlled-NOT permutations and widget counts

This module realizes controlled-NOT as the permutation exchanging `(1, 0)` and `(1, 1)` and as
its permutation matrix. It verifies the basis-state action, involutivity, and unitarity, and
counts the spectator-bit assignments used for gate widgets in [Childs2009].

## Main statements

* `cnotMatrix_unitary`: The controlled-NOT matrix satisfies both unitary identities.
* `cnotMatrix_mulVec_single`: Describe its action on a computational basis vector.
* `cnotWidgetCount`: Count the assignments indexing controlled-NOT widgets.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.Gates

open Matrix

set_option autoImplicit false

/-- The permutation exchanging `(1, 0)` and `(1, 1)` and fixing the other two bit pairs. -/
noncomputable def cnotPerm : Equiv.Perm (Fin 2 × Fin 2) :=
  Equiv.swap ((1 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (1 : Fin 2))

/-- The complex permutation matrix associated with `cnotPerm`. -/
noncomputable def cnotMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  cnotPerm.permMatrix ℂ

/-- The controlled-NOT permutation fixes `(0, 0)`. -/
theorem cnotPerm_zero_zero : cnotPerm ((0 : Fin 2), (0 : Fin 2)) =
    ((0 : Fin 2), (0 : Fin 2)) := by
  unfold cnotPerm
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

/-- The controlled-NOT permutation fixes `(0, 1)`. -/
theorem cnotPerm_zero_one : cnotPerm ((0 : Fin 2), (1 : Fin 2)) =
    ((0 : Fin 2), (1 : Fin 2)) := by
  unfold cnotPerm
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

/-- The controlled-NOT permutation sends `(1, 0)` to `(1, 1)`. -/
theorem cnotPerm_one_zero : cnotPerm ((1 : Fin 2), (0 : Fin 2)) =
    ((1 : Fin 2), (1 : Fin 2)) := by
  unfold cnotPerm
  exact Equiv.swap_apply_left _ _

/-- The controlled-NOT permutation sends `(1, 1)` to `(1, 0)`. -/
theorem cnotPerm_one_one : cnotPerm ((1 : Fin 2), (1 : Fin 2)) =
    ((1 : Fin 2), (0 : Fin 2)) := by
  unfold cnotPerm
  exact Equiv.swap_apply_right _ _

/-- The controlled-NOT permutation is involutive. -/
theorem cnotPerm_involutive : Function.Involutive cnotPerm := by
  intro p
  unfold cnotPerm
  exact Equiv.swap_apply_self _ _ _

/-- The inverse of the controlled-NOT permutation is itself. -/
theorem cnotPerm_symm : cnotPerm.symm = cnotPerm := by
  apply Equiv.ext
  intro p
  rw [Equiv.symm_apply_eq]
  exact (cnotPerm_involutive p).symm

/-- The inverse controlled-NOT permutation fixes `(0, 0)`. -/
theorem cnotPerm_symm_zero_zero : cnotPerm.symm ((0 : Fin 2), (0 : Fin 2)) =
    ((0 : Fin 2), (0 : Fin 2)) := by
  rw [cnotPerm_symm, cnotPerm_zero_zero]

/-- The inverse controlled-NOT permutation fixes `(0, 1)`. -/
theorem cnotPerm_symm_zero_one : cnotPerm.symm ((0 : Fin 2), (1 : Fin 2)) =
    ((0 : Fin 2), (1 : Fin 2)) := by
  rw [cnotPerm_symm, cnotPerm_zero_one]

/-- The inverse controlled-NOT permutation sends `(1, 0)` to `(1, 1)`. -/
theorem cnotPerm_symm_one_zero : cnotPerm.symm ((1 : Fin 2), (0 : Fin 2)) =
    ((1 : Fin 2), (1 : Fin 2)) := by
  rw [cnotPerm_symm, cnotPerm_one_zero]

/-- The inverse controlled-NOT permutation sends `(1, 1)` to `(1, 0)`. -/
theorem cnotPerm_symm_one_one : cnotPerm.symm ((1 : Fin 2), (1 : Fin 2)) =
    ((1 : Fin 2), (0 : Fin 2)) := by
  rw [cnotPerm_symm, cnotPerm_one_one]

/-- The square of the controlled-NOT matrix is the identity. -/
theorem cnotMatrix_mul_self : cnotMatrix * cnotMatrix = 1 := by
  unfold cnotMatrix
  have h : cnotPerm * cnotPerm = 1 := by
    apply Equiv.ext
    intro p
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    simpa using cnotPerm_involutive p
  rw [← Matrix.permMatrix_mul, h, Matrix.permMatrix_one]

/-- The controlled-NOT matrix satisfies both unitary identities [Childs2009]. -/
theorem cnotMatrix_unitary :
    cnotMatrix * cnotMatrixᴴ = 1 ∧ cnotMatrixᴴ * cnotMatrix = 1 := by
  constructor
  · unfold cnotMatrix
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  · unfold cnotMatrix
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp

/-- The controlled-NOT matrix sends the basis vector at `p` to the basis vector at
`cnotPerm.symm p`. -/
theorem cnotMatrix_mulVec_single (p : Fin 2 × Fin 2) :
    cnotMatrix *ᵥ (Pi.single p (1 : ℂ)) =
      Pi.single (cnotPerm.symm p) (1 : ℂ) := by
  unfold cnotMatrix
  rw [Matrix.permMatrix_mulVec]
  ext q
  simp only [Function.comp_apply, Pi.single_apply, Pi.one_apply]
  by_cases h : cnotPerm q = p
  · rw [if_pos h, if_pos ((Equiv.eq_symm_apply cnotPerm).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((Equiv.eq_symm_apply cnotPerm).mp hh))]

/-- The controlled-NOT matrix sends the basis state `(1, 0)` to `(1, 1)` [Childs2009]. -/
theorem cnotMatrix_sends_one_zero :
    cnotMatrix *ᵥ (Pi.single ((1 : Fin 2), (0 : Fin 2)) (1 : ℂ)) =
      Pi.single ((1 : Fin 2), (1 : Fin 2)) (1 : ℂ) := by
  rw [cnotMatrix_mulVec_single, cnotPerm_symm_one_zero]

/-- The controlled-NOT matrix sends the basis state `(1, 1)` to `(1, 0)` [Childs2009]. -/
theorem cnotMatrix_sends_one_one :
    cnotMatrix *ᵥ (Pi.single ((1 : Fin 2), (1 : Fin 2)) (1 : ℂ)) =
      Pi.single ((1 : Fin 2), (0 : Fin 2)) (1 : ℂ) := by
  rw [cnotMatrix_mulVec_single, cnotPerm_symm_one_one]

/-- The controlled-NOT matrix fixes the basis state `(0, 0)`. -/
theorem cnotMatrix_fixes_zero_zero :
    cnotMatrix *ᵥ (Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)) =
      Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ) := by
  rw [cnotMatrix_mulVec_single, cnotPerm_symm_zero_zero]

/-- The controlled-NOT matrix fixes the basis state `(0, 1)`. -/
theorem cnotMatrix_fixes_zero_one :
    cnotMatrix *ᵥ (Pi.single ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ)) =
      Pi.single ((0 : Fin 2), (1 : Fin 2)) (1 : ℂ) := by
  rw [cnotMatrix_mulVec_single, cnotPerm_symm_zero_one]

/-- The number of assignments of `n - 2` spectator bits is `2 ^ (n - 2)` [Childs2009]. -/
theorem cnotWidgetCount (n : ℕ) :
    Fintype.card (Fin (n - 2) → Fin 2) = 2 ^ (n - 2) := by
  simp [Fintype.card_fun]

/-- The number of assignments of `n - 1` spectator bits is `2 ^ (n - 1)` [Childs2009]. -/
theorem singleQubitWidgetCount (n : ℕ) :
    Fintype.card (Fin (n - 1) → Fin 2) = 2 ^ (n - 1) := by
  simp [Fintype.card_fun]

end Qatlib.Papers.UniversalWalk08.MainResults.Gates
