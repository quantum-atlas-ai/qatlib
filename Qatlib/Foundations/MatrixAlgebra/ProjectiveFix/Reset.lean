/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ProjectiveFix.Instrument
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis

set_option autoImplicit false
open scoped BigOperators ComplexOrder Matrix Kronecker
namespace Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
noncomputable section
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def resetOp (ab : A × A) : Matrix (A × B) (A × B) ℂ :=
  Matrix.single ab.1 ab.2 1 ⊗ₖ (1 : Matrix B B ℂ)

theorem resetOp_gram (ab : A × A) :
    (resetOp (B := B) ab)ᴴ * resetOp ab =
      Matrix.single ab.2 ab.2 1 ⊗ₖ (1 : Matrix B B ℂ) := by
  simp [resetOp, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

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

def localReset (M : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  ((Fintype.card A : ℝ)⁻¹) • kraus (resetOp (A := A) (B := B)) M

theorem localReset_entry (M : Matrix (A × B) (A × B) ℂ) (x y : A × B) :
    localReset M x y = if x.1 = y.1 then
      ((Fintype.card A : ℝ)⁻¹ : ℂ) * ∑ a, M (a, x.2) (a, y.2) else 0 := by
  simp only [localReset, kraus, Matrix.smul_apply, Matrix.sum_apply, resetOp,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply ]
  by_cases h : x.1 = y.1
  · simp [Matrix.single, Matrix.one_apply, ite_and, apply_ite, h, Complex.real_smul]
  · simp [Matrix.single, Matrix.one_apply, ite_and, apply_ite, h, Ne.symm h]

theorem localReset_pos {M : Matrix (A × B) (A × B) ℂ} (hM : M.PosSemidef) :
    (localReset M).PosSemidef := by
  exact (kraus_pos _ hM).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem localReset_trace [Nonempty A] (M : Matrix (A × B) (A × B) ℂ) :
    (localReset M).trace = M.trace := by
  have hc : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [localReset, Matrix.trace_smul, trace_kraus, resetOp_complete,
    Matrix.smul_mul, one_mul, Matrix.trace_smul]
  simp only [Complex.real_smul, smul_eq_mul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem resetOp_outside_commutes (Q : Matrix B B ℂ) (ab : A × A) :
    ((1 : Matrix A A ℂ) ⊗ₖ Q) * resetOp ab =
      resetOp ab * ((1 : Matrix A A ℂ) ⊗ₖ Q) := by
  simp [resetOp, ← Matrix.mul_kronecker_mul]

theorem localReset_outside_preserves (Q : Matrix B B ℂ)
    (M : Matrix (A × B) (A × B) ℂ)
    (hM : ((1 : Matrix A A ℂ) ⊗ₖ Q) * M = 0) :
    ((1 : Matrix A A ℂ) ⊗ₖ Q) * localReset M = 0 := by
  have h := kraus_preserves (resetOp (A := A) (B := B)) _ M
    (resetOp_outside_commutes Q) hM
  simp only [localReset, Matrix.mul_smul, h, smul_zero]

end
end Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
