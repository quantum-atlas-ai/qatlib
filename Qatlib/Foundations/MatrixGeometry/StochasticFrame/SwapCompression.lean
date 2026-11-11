/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.StochasticFrame.RowFrame

/-!
# Swap compression of stochastic frames

Defines the permutation matrix `swap` exchanging the two coordinates of the product index type
and proves its Hermitian and unitary identities. The mixed frame compression `mixed_compression`
computes entries as `√(P x y * Q y x)` under nonnegativity of `P`. See
[ClaudonPiquemalMonmarche2025] for related background.

## Main statements

* `swap_unitary`: The adjoint of the coordinate-swap matrix multiplied by the matrix itself
  equals the identity.
* `mixed_compression`: If `P` has nonnegative entries, the entry at `(x, y)` of `(rowFrame P)ᴴ *
  swap * rowFrame Q` is the complex cast of `√(P x y * Q y x)`.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.StochasticFrame
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The permutation matrix that exchanges the two coordinates of a product index. -/
def swap : Matrix (I × I) (I × I) ℂ :=
    Equiv.Perm.permMatrix ℂ (Equiv.prodComm I I : Equiv.Perm (I × I))
omit [Fintype I] in

/-- The coordinate-swap matrix is Hermitian. -/
theorem swap_adjoint : (swap (I := I))ᴴ=swap := by
  rw [swap,Matrix.conjTranspose_permMatrix]
  rfl

/-- The coordinate-swap matrix squares to the identity. -/
theorem swap_squared : swap (I := I)*swap=1 := by
  have he : (Equiv.prodComm I I : Equiv.Perm (I × I))*(Equiv.prodComm I I)=1 := by
    apply Equiv.ext
    rintro ⟨x,y⟩
    rfl
  rw [swap,← Matrix.permMatrix_mul,he,Matrix.permMatrix_one]

/-- The adjoint of the coordinate-swap matrix multiplied by the matrix itself equals the
identity. -/
theorem swap_unitary : (swap (I := I))ᴴ*swap=1 := by rw [swap_adjoint,swap_squared]

/-- Multiplying a row frame on the left by `swap` exchanges the coordinates of its row index. -/
theorem swap_frame (P : Matrix I I ℝ) : (swap*rowFrame P : Matrix (I × I) I ℂ)=fun a x => rowFrame P (a.2,a.1) x := by
  ext a x
  change ((Equiv.prodComm I I).toPEquiv.toMatrix * rowFrame P : Matrix (I × I) I ℂ) a x = _
  rw [PEquiv.toMatrix_mul_apply]
  rfl

/-- If `P` has nonnegative entries, the entry at `(x, y)` of `(rowFrame P)ᴴ * swap * rowFrame Q`
is the complex cast of `√(P x y * Q y x)`. -/
theorem mixed_compression (P Q : Matrix I I ℝ) (hP : ∀ x y,0 ≤ P x y) :
    (rowFrame P)ᴴ*swap*rowFrame Q=fun x y => (Real.sqrt (P x y*Q y x) : ℂ) := by
  calc
    _ = (rowFrame P)ᴴ*(swap (I := I)*rowFrame Q) := Matrix.mul_assoc _ _ _
    _ = _ := by
      rw [swap_frame (I := I) Q]
      ext x y
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,rowFrame,Matrix.of_apply,Fintype.sum_prod_type]
      have hmul : (Real.sqrt (P x y) : ℂ)*(Real.sqrt (Q y x) : ℂ)=(Real.sqrt (P x y*Q y x) : ℂ) := by
        rw [← Complex.ofReal_mul,← Real.sqrt_mul (hP x y)]
      dsimp
      simpa [apply_ite, ite_mul] using! hmul

end Qatlib.Foundations.MatrixGeometry.StochasticFrame
