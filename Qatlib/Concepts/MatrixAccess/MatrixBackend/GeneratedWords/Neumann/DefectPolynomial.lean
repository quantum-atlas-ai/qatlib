/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.ReciprocalApproximation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

/-!
Finite defect polynomials and the reciprocal approximation identity.

The reciprocal approximation identity includes empty sums. No numerical-range or resolvent access premise is introduced.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The orientation realized by fresh flags followed by the final inverse query. -/
def leftDefectNeumann (S : Matrix I I ℂ) (b : ℕ) : Matrix I I ℂ :=
  Sᴴ * ∑ k ∈ Finset.range b, (1 - S * Sᴴ) ^ k

/-- The exact `defect_intertwine` invariant under the original hypotheses and resource conventions. -/
private theorem defect_intertwine (S : Matrix I I ℂ) (k : ℕ) :
    (1 - Sᴴ * S) ^ k * Sᴴ = Sᴴ * (1 - S * Sᴴ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    have h : (1 - Sᴴ * S) * Sᴴ = Sᴴ * (1 - S * Sᴴ) := by noncomm_ring
    rw [h, Matrix.mul_assoc, ← pow_succ']

/-- Fresh-flag orientation equals the pinned library's Gram-polynomial target,
including the empty sum. No inverse or spectral decomposition is an input. -/
theorem leftDefectNeumann_eq_reciprocalMatrixApprox (S : Matrix I I ℂ) (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann S b = Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalMatrixApprox S b := by
  have he : aeval (Sᴴ * S) ((Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalFactor b).map Complex.ofRealHom) =
      ∑ k ∈ Finset.range b, (1 - Sᴴ * S) ^ k := by
    simp [Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalFactor, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  rw [Qatlib.Concepts.QsvtCore.LinearSystems.reciprocalMatrixApprox, he, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_pow, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Finset.sum_mul]
  simp only [defect_intertwine]
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
  rw [Finset.mul_sum]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
