/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs

@[expose] public section

/-!
# Weight-zero eigenvector of the symmetric problem Hamiltonian

The symmetric problem Hamiltonian is diagonal in the weight basis. Its zero-weight vector
is nonzero, and multiplying it by the operator uses only the zero energy at that weight.
-/

set_option autoImplicit false

open scoped Matrix
open Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
open Qatlib.Papers.AdiabaticPath02.MainResults.SymmetricDefs

namespace Qatlib.Papers.AdiabaticPath02.MainResults

/-- The all-zero weight vector is annihilated by the symmetric problem operator. -/
theorem hp_ground_eigenvector (n : ℕ) :
    toOperator (symHP n) *ᵥ hpGroundVec n = 0 := by
  rw [toOperator, symHP, Matrix.diagonal_map Complex.ofReal_zero]
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : i.val = 0
  · simp [hpGroundVec, hi, hpEnergy_zero]
  · simp [hpGroundVec, hi]

/-- The weight-zero eigenvector has a nonzero entry at the zero-weight basis label. -/
theorem hp_ground_vector_ne_zero (n : ℕ) : hpGroundVec n ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Fin (n + 1))
  simp [hpGroundVec] at hzero

end Qatlib.Papers.AdiabaticPath02.MainResults
