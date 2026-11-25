/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! # Affine conjugation in a skew-Hermitian direction

Conjugating by `1 + t • Ω`, with real `t` and skew-Hermitian `Ω`, gives a matrix
polynomial of degree at most two. Taking its commutator with a fixed matrix
preserves the polynomial expansion. In particular, the linear coefficient of
the gradient map along `U + t • (Ω * U)` agrees with [LaiAnHuWen2026], Lemma 6,
Eq. (B7). The identity concerns the affine ray. The five-factor retraction
and the norm estimate in Eq. (B8) require separate analysis.

[Paper](https://arxiv.org/abs/2603.26039v3)
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Foundations.MatrixAlgebra.SpectralPerturb

/-- The additive commutator `AB - BA` of two matrices. -/
def matrixCommutator {n : Type*} [Fintype n] (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

/-- The gradient map defined by the commutator of `H` with `U * P * Uᴴ`. -/
def conjugationGradient {n : Type*} [Fintype n] (H P U : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixCommutator H (U * P * Uᴴ)

/-- Affine conjugation by a skew-Hermitian direction has an exact quadratic expansion. -/
theorem affine_conjugation_eq {n : Type*} [Fintype n] [DecidableEq n]
    (P Ω : Matrix n n ℂ) (t : ℝ) (hΩ : Ωᴴ = -Ω) :
    (1 + (t : ℂ) • Ω) * P * (1 + (t : ℂ) • Ω)ᴴ
      = P + (t : ℂ) • matrixCommutator Ω P - (t : ℂ) ^ 2 • (Ω * P * Ω) := by
  have ht : star (t : ℂ) = (t : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, ht, hΩ]
  unfold matrixCommutator
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, smul_add, smul_sub, smul_neg, smul_smul, pow_two]
  abel

/-- The commutator with a fixed matrix distributes over a linear combination. -/
theorem matrix_commutator_add_smul_sub_smul {n : Type*} [Fintype n]
    (H X C Z : Matrix n n ℂ) (a b : ℂ) :
    matrixCommutator H (X + a • C - b • Z)
      = matrixCommutator H X + a • matrixCommutator H C - b • matrixCommutator H Z := by
  unfold matrixCommutator
  simp only [sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_neg, add_assoc]
  abel

/-- The exact affine expansion of the gradient map has a double commutator as its linear
coefficient. This is the algebra underlying [LaiAnHuWen2026], Lemma 6, Eq. (B7). -/
theorem conjugation_gradient_affine_eq {n : Type*} [Fintype n] [DecidableEq n]
    (H P Ω U : Matrix n n ℂ) (t : ℝ) (hΩ : Ωᴴ = -Ω) :
    conjugationGradient H P (U + (t : ℂ) • (Ω * U))
      = conjugationGradient H P U
        + (t : ℂ) • matrixCommutator H (matrixCommutator Ω (U * P * Uᴴ))
        - (t : ℂ) ^ 2 • matrixCommutator H (Ω * (U * P * Uᴴ) * Ω) := by
  unfold conjugationGradient
  have hleft : U + (t : ℂ) • (Ω * U) = (1 + (t : ℂ) • Ω) * U := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hleft, Matrix.conjTranspose_mul]
  rw [show (1 + (t : ℂ) • Ω) * U * P * (Uᴴ * (1 + (t : ℂ) • Ω)ᴴ)
        = (1 + (t : ℂ) • Ω) * (U * P * Uᴴ) * (1 + (t : ℂ) • Ω)ᴴ by noncomm_ring]
  rw [affine_conjugation_eq (U * P * Uᴴ) Ω t hΩ]
  exact matrix_commutator_add_smul_sub_smul H (U * P * Uᴴ) (matrixCommutator Ω (U * P * Uᴴ))
    (Ω * (U * P * Uᴴ) * Ω) t ((t : ℂ) ^ 2)

end Qatlib.Foundations.MatrixAlgebra.SpectralPerturb
