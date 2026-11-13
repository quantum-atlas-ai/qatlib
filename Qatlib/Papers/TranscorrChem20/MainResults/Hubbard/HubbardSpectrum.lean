/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.Hubbard.Gutzwiller
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic polynomial of the corrected Hubbard Hamiltonian

This module proves that finite Gutzwiller conjugation preserves characteristic polynomials.
Applying the explicit hopping formula shows that the corrected Hubbard matrix has the same
characteristic polynomial as the original Hamiltonian. See [McArdleTew2020].

## Main statements

* `actual_gutzwiller_charpoly`: Invariance under Gutzwiller similarity.
* `actual_corrected_hubbard_charpoly`: Characteristic-polynomial equality for the corrected
  Hubbard matrix.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.TranscorrChem20.MainResults.Hubbard

/-- The Gutzwiller exponentials with parameters `J` and `-J` multiply to the identity. -/
theorem actual_gutzwiller_inverse (N : ℕ) (J : ℂ) :
    exp (J • doubleOp N) * exp ((-J) • doubleOp N) = 1 := by
  simpa only [neg_neg, Matrix.diagonal_one, Matrix.mul_one] using!
    (actual_gutzwiller_diagonal (N := N) (fun _ => 1) (-J))

/-- Conjugating a finite matrix by the Gutzwiller exponentials preserves its characteristic
polynomial. -/
theorem actual_gutzwiller_charpoly {N : ℕ}
    (H : Matrix (Reg (2*N)) (Reg (2*N)) ℂ) (J : ℂ) :
    (exp ((-J) • doubleOp N) * H * exp (J • doubleOp N)).charpoly = H.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, actual_gutzwiller_inverse,
    Matrix.one_mul]

/-- For edges with distinct endpoints, adding the explicit Gutzwiller correction preserves the
Hubbard characteristic polynomial. See [McArdleTew2020]. -/
theorem actual_corrected_hubbard_charpoly {N e : ℕ} (src dst : Fin e → Fin N)
    (hedge : ∀ a, src a ≠ dst a) (t U J : ℂ) :
    (hubbard src dst t U + hubbardCorrection src dst t J).charpoly =
      (hubbard src dst t U).charpoly := by
  rw [← actual_gutzwiller_hubbard src dst hedge t U J]
  exact actual_gutzwiller_charpoly (hubbard src dst t U) J

end Qatlib.Papers.TranscorrChem20.MainResults.Hubbard
