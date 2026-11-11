/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm.CharacterTarget

/-!
# Shift spectra in the character Fourier basis

The columns of `characterQFT` are eigenvectors of the regular group shifts. This module records
the eigenvalue convention `labels j (-b)`, assembles the column identities into matrix
diagonalization, and specializes the result to the cyclic shift on `ZMod q`. The development
follows [Kitaev1995].

## Main statements

* `characterQFT_shift_mul`: diagonalizes a regular shift in the character Fourier basis.
* `characterQFT_cyclic_shift`: specializes diagonalization to the shift by one on a cyclic
  group.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm

open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open Matrix

/-- The `j`th character Fourier column is an eigenvector of the shift by `b` with eigenvalue
`labels j (-b)`. -/
theorem characterQFT_shift_eigen (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) (b j : E) :
    orbitRegMatrix E b *ᵥ (fun x => characterQFT E labels x j)
      = (labels j (-b)) • (fun x => characterQFT E labels x j) := by
  have h := (orbitFourierBasisSubgoal E).2.1 b (labels j)
  simpa [characterQFT] using! h

/-- Multiplying the character Fourier matrix by a regular shift equals multiplying it on the
right by the diagonal matrix of character values at `-b`, as used in [Kitaev1995]. -/
theorem characterQFT_shift_mul (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) (b : E) :
    orbitRegMatrix E b * characterQFT E labels
      = characterQFT E labels * Matrix.diagonal (fun j => labels j (-b)) := by
  ext x j
  rw [Matrix.mul_diagonal]
  change (orbitRegMatrix E b *ᵥ (fun k => characterQFT E labels k j)) x
      = characterQFT E labels x j * (labels j (-b))
  rw [characterQFT_shift_eigen E labels b j]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The cyclic shift by one on `ZMod q` is diagonalized by the character Fourier matrix with
eigenvalues given by the characters evaluated at negative one. -/
theorem characterQFT_cyclic_shift (q : ℕ) [NeZero q]
    (labels : ZMod q ≃ AddChar (ZMod q) ℂ) :
    orbitRegMatrix (ZMod q) (1 : ZMod q) * characterQFT (ZMod q) labels
      = characterQFT (ZMod q) labels *
          Matrix.diagonal (fun j => labels j (-(1 : ZMod q))) :=
  characterQFT_shift_mul (ZMod q) labels (1 : ZMod q)

end Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm
