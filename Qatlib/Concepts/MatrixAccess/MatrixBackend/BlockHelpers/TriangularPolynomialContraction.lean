/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# A polynomial contraction from a triangular block matrix

This module proves that `B + A * A` has operator norm at most one whenever the upper triangular
block matrix with diagonal blocks A and upper-right block B is a contraction. The proof uses
`triangular_defect_certificate` to express the polynomial defect as a congruence of the block
matrix defect.

The positivity and operator norm arguments use the matrix analysis framework of [Bhatia1997]; a
one-dimensional example attains the bound.

## Main statements

* `triangular_joint_polynomial_norm_le_one`: proves the polynomial contraction bound.
* `triangular_joint_polynomial_norm_attainer`: exhibits equality in dimension one.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.TriangularPolynomialContraction

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable local instance triangularMatrixCStar {J : Type}
    [Fintype J] [DecidableEq J] : CStarAlgebra (Matrix J J ℂ) where

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The congruence of the defect of the block matrix [[A, B], [0, A]] by the block column [A; I]
equals the defect of B + A². -/
theorem triangular_defect_certificate (A B : Matrix R R ℂ) :
    (Matrix.fromRows A (1 : Matrix R R ℂ))ᴴ *
      (1 - (Matrix.fromBlocks A B 0 A)ᴴ * Matrix.fromBlocks A B 0 A) *
      Matrix.fromRows A (1 : Matrix R R ℂ) =
        1 - (B + A * A)ᴴ * (B + A * A) := by
  let Δ : Matrix (R ⊕ R) (R ⊕ R) ℂ := Matrix.fromBlocks A B 0 A
  let H : Matrix (R ⊕ R) R ℂ := Matrix.fromRows A 1
  change Hᴴ * (1 - Δᴴ * Δ) * H = 1 - (B + A * A)ᴴ * (B + A * A)
  have hresponse : Δ * H = Matrix.fromRows (B + A * A) A := by
    dsimp [Δ, H]
    simp only [Matrix.fromBlocks_mul_fromRows, Matrix.mul_one,
      Matrix.zero_mul, add_zero, add_comm]
  calc
    Hᴴ * (1 - Δᴴ * Δ) * H = Hᴴ * H - (Δ * H)ᴴ * (Δ * H) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 - (B + A * A)ᴴ * (B + A * A) := by
      rw [hresponse]
      dsimp [H]
      simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
        Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_one, Matrix.one_mul]
      abel

/-- A finite complex matrix has operator norm at most one if I - MᴴM is positive semidefinite. -/
private theorem triangular_norm_le_one_of_defect (M : Matrix R R ℂ)
    (hdefect : (1 - Mᴴ * M).PosSemidef) : ‖M‖ ≤ 1 := by
  have hp : 0 ≤ Mᴴ * M := (Matrix.posSemidef_conjTranspose_mul_self M).nonneg
  have hle : Mᴴ * M ≤ 1 := Matrix.le_iff.mpr hdefect
  have hn : ‖Mᴴ * M‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mpr hle
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg M]

/-- If the block matrix [[A, B], [0, A]] is a contraction, then B + A² is a contraction in the
L2 operator norm. -/
theorem triangular_joint_polynomial_norm_le_one (A B : Matrix R R ℂ)
    (hΔ : ‖Matrix.fromBlocks A B 0 A‖ ≤ 1) : ‖B + A * A‖ ≤ 1 := by
  let Δ : Matrix (R ⊕ R) (R ⊕ R) ℂ := Matrix.fromBlocks A B 0 A
  let H : Matrix (R ⊕ R) R ℂ := Matrix.fromRows A 1
  have hΔnorm : ‖Δ‖ ≤ 1 := hΔ
  have hp : 0 ≤ Δᴴ * Δ := (Matrix.posSemidef_conjTranspose_mul_self Δ).nonneg
  have hle : Δᴴ * Δ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mp (by
      rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      nlinarith [norm_nonneg Δ])
  have hdefect : (1 - Δᴴ * Δ).PosSemidef := Matrix.le_iff.mp hle
  have hpoly : (1 - (B + A * A)ᴴ * (B + A * A)).PosSemidef := by
    have h := hdefect.conjTranspose_mul_mul_same H
    have hcertificate := triangular_defect_certificate A B
    change Hᴴ * (1 - Δᴴ * Δ) * H = _ at hcertificate
    rwa [hcertificate] at h
  exact triangular_norm_le_one_of_defect (B + A * A) hpoly

/-- The block matrix [[0, I], [0, 0]] has operator norm at most one. -/
theorem triangular_identity_injection_admissible :
    ‖Matrix.fromBlocks (0 : Matrix R R ℂ) (1 : Matrix R R ℂ)
      (0 : Matrix R R ℂ) (0 : Matrix R R ℂ)‖ ≤ 1 := by
  let Δ : Matrix (R ⊕ R) (R ⊕ R) ℂ :=
    Matrix.fromBlocks (0 : Matrix R R ℂ) (1 : Matrix R R ℂ)
      (0 : Matrix R R ℂ) (0 : Matrix R R ℂ)
  let K : Matrix R (R ⊕ R) ℂ :=
    Matrix.fromCols (1 : Matrix R R ℂ) (0 : Matrix R R ℂ)
  have hsum : Δᴴ * Δ + Kᴴ * K = 1 := by
    dsimp [Δ, K]
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero,
      Matrix.fromBlocks_add, Matrix.fromBlocks_one]
  have hdefect : (1 - Δᴴ * Δ).PosSemidef := by
    have he : 1 - Δᴴ * Δ = Kᴴ * K := by rw [← hsum]; abel
    rw [he]
    exact Matrix.posSemidef_conjTranspose_mul_self K
  exact triangular_norm_le_one_of_defect Δ hdefect

/-- The choice A = 0 and B = I in dimension one satisfies the block contraction condition and
gives ‖B + A²‖ = 1. -/
theorem triangular_joint_polynomial_norm_attainer :
    ‖Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin 1) ℂ)‖ ≤ 1 ∧
      ‖(1 : Matrix (Fin 1) (Fin 1) ℂ) +
        (0 : Matrix (Fin 1) (Fin 1) ℂ) * (0 : Matrix (Fin 1) (Fin 1) ℂ)‖ = 1 := by
  refine ⟨triangular_identity_injection_admissible, ?_⟩
  simp

end Qatlib.Concepts.MatrixAccess.MatrixBackend.TriangularPolynomialContraction
