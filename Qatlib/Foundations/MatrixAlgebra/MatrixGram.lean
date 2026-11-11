/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.Sqrt
import Mathlib.Tactic

/-!
# Gram factors from positive semidefinite square roots

`gramFactor` uses the Hermitian square root of a real positive semidefinite matrix.
`gramFactor_identity` proves that its transpose-product recovers the original matrix.

This is the finite-dimensional square-root construction of a Gram factor; see [Bhatia1997] for
matrix positivity and square roots.

## Main statements

* `gramFactor`: Square-root Gram factor of a real positive semidefinite matrix.
* `gramFactor_identity`: The factor satisfies `Fᵀ * F = D`.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.MatrixGram
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real matrix obtained from the Hermitian square root of the positive semidefinite matrix
`D`. -/
def gramFactor (D : Matrix I I ℝ) (hD : D.PosSemidef) : Matrix I I ℝ :=
  (HermitianMat.sqrt (⟨D,hD.isHermitian⟩ : HermitianMat I ℝ)).mat

/-- The transpose of the square-root Gram factor multiplied by the factor equals the original
positive semidefinite matrix. -/
theorem gramFactor_identity (D : Matrix I I ℝ) (hD : D.PosSemidef) :
    (gramFactor D hD)ᵀ*gramFactor D hD=D := by
  have hs : (gramFactor D hD)ᵀ=gramFactor D hD := by
    simpa only [gramFactor,Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (HermitianMat.sqrt (⟨D,hD.isHermitian⟩ : HermitianMat I ℝ)).H
  rw [hs]
  exact HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hD)
end Qatlib.Foundations.MatrixAlgebra.MatrixGram
