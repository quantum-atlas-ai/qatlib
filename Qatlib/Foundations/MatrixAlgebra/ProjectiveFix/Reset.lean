/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ProjectiveFix.Instrument
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis

/-!
# Maximally mixed local reset

`resetOp` constructs matrix-unit Kraus operators on the first factor of a finite product
register. Their normalized sum defines `localReset`, whose entry formula replaces that factor by
the maximally mixed matrix while retaining the partial trace over it.

The module proves positive semidefiniteness, trace preservation for a nonempty reset factor, and
preservation of constraints acting on the untouched factor. This models the local replacement
operation in [SattathArad2015].

## Main statements

* `localReset_entry`: explicit entries of the local reset map.
* `localReset_trace`: local reset preserves trace when the reset register is nonempty.
* `localReset_outside_preserves`: constraints on the untouched register retain left
  annihilation.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

set_option autoImplicit false
open scoped BigOperators ComplexOrder Matrix Kronecker
namespace Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
noncomputable section
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The matrix unit indexed by `ab` on the first register, tensored with the identity on the
second register. -/
def resetOp (ab : A × A) : Matrix (A × B) (A × B) ℂ :=
  Matrix.single ab.1 ab.2 1 ⊗ₖ (1 : Matrix B B ℂ)

/-- The Gram matrix of a reset operator is the diagonal matrix unit at `ab.2`, tensored with the
identity. -/
theorem resetOp_gram (ab : A × A) :
    (resetOp (B := B) ab)ᴴ * resetOp ab =
      Matrix.single ab.2 ab.2 1 ⊗ₖ (1 : Matrix B B ℂ) := by
  simp [resetOp, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

/-- The sum of the reset operators' Gram matrices is the identity scaled by the cardinality of
the reset register. -/
theorem resetOp_complete :
    ∑ ab : A × A, (resetOp (B := B) ab)ᴴ * resetOp ab =
      (Fintype.card A : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) := by
  simp only [resetOp_gram, Fintype.sum_prod_type]
  have hsum : ∑ b : A, Matrix.single b b (1 : ℂ) ⊗ₖ (1 : Matrix B B ℂ) = 1 := by
    ext x y
    by_cases hx : x.1 = y.1 <;> by_cases hy : x.2 = y.2
    all_goals simp [Matrix.single, Matrix.one_apply, Matrix.sum_apply, Prod.ext_iff, hx, hy]
  simp_rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ (Fintype.card A) (1 : Matrix (A × B) (A × B) ℂ)).symm

/-- The matrix-unit Kraus sum scaled by the reciprocal cardinality of the first register. -/
def localReset (M : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  ((Fintype.card A : ℝ)⁻¹) • kraus (resetOp (A := A) (B := B)) M

/-- The entries of local reset are the partial trace over the first register, divided by its
cardinality on equal first coordinates, and zero otherwise. This is the maximally mixed
replacement in [SattathArad2015]. -/
theorem localReset_entry (M : Matrix (A × B) (A × B) ℂ) (x y : A × B) :
    localReset M x y = if x.1 = y.1 then
      ((Fintype.card A : ℝ)⁻¹ : ℂ) * ∑ a, M (a, x.2) (a, y.2) else 0 := by
  simp only [localReset, kraus, Matrix.smul_apply, Matrix.sum_apply, resetOp,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply ]
  by_cases h : x.1 = y.1
  · simp [Matrix.single, Matrix.one_apply, ite_and, apply_ite, h, Complex.real_smul]
  · simp [Matrix.single, Matrix.one_apply, ite_and, apply_ite, h, Ne.symm h]

/-- Local reset preserves positive semidefiniteness. -/
theorem localReset_pos {M : Matrix (A × B) (A × B) ℂ} (hM : M.PosSemidef) :
    (localReset M).PosSemidef := by
  exact (kraus_pos _ hM).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Local reset preserves the input trace when the reset register is nonempty, as in the
replacement operation of [SattathArad2015]. -/
theorem localReset_trace [Nonempty A] (M : Matrix (A × B) (A × B) ℂ) :
    (localReset M).trace = M.trace := by
  have hc : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [localReset, Matrix.trace_smul, trace_kraus, resetOp_complete,
    Matrix.smul_mul, one_mul, Matrix.trace_smul]
  simp only [Complex.real_smul, smul_eq_mul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Every reset Kraus operator commutes with any operator acting only on the second register. -/
theorem resetOp_outside_commutes (Q : Matrix B B ℂ) (ab : A × A) :
    ((1 : Matrix A A ℂ) ⊗ₖ Q) * resetOp ab =
      resetOp ab * ((1 : Matrix A A ℂ) ⊗ₖ Q) := by
  simp [resetOp, ← Matrix.mul_kronecker_mul]

/-- An operator acting on the second register that annihilates `M` on the left also annihilates
its local reset. -/
theorem localReset_outside_preserves (Q : Matrix B B ℂ)
    (M : Matrix (A × B) (A × B) ℂ)
    (hM : ((1 : Matrix A A ℂ) ⊗ₖ Q) * M = 0) :
    ((1 : Matrix A A ℂ) ⊗ₖ Q) * localReset M = 0 := by
  have h := kraus_preserves (resetOp (A := A) (B := B)) _ M
    (resetOp_outside_commutes Q) hM
  simp only [localReset, Matrix.mul_smul, h, smul_zero]

end
end Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
