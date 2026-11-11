/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DirichletForm.KmsDirichlet.KmsInnerProduct

/-!
# Fourth-root weights and parent factors

This module defines fourth-root weighted conjugations, their associated parent-factor linear
map, and a finite Gram sum of parent-factor outputs. For positive definite weights it relates
the common kernel to commutation after inverse weighting. The square-root and positivity
arguments use the matrix-analysis framework of [Bhatia1997].

## Main statements

* `parentFactor_sqrt`: The square root of a positive definite weight lies in each parent-factor
  kernel.
* `parentFactor_eq_zero_iff`: Vanishing is equivalent to commutation after inverse weighting.
* `parentGram_eq_zero_iff`: The Gram sum vanishes exactly when every parent factor vanishes.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D : ℕ}

/-- The iterated functional-calculus square root `CFC.sqrt (CFC.sqrt ρ)`. -/
noncomputable def fourthRoot (ρ : Operator D) : Operator D := CFC.sqrt (CFC.sqrt ρ)

/-- The weighted conjugation `fourthRoot ρ * B * (fourthRoot ρ)⁻¹`. -/
noncomputable def sharp (ρ B : Operator D) : Operator D :=
  fourthRoot ρ * B * (fourthRoot ρ)⁻¹

/-- The inverse weighted conjugation `(fourthRoot ρ)⁻¹ * B * fourthRoot ρ`. -/
noncomputable def flat (ρ B : Operator D) : Operator D :=
  (fourthRoot ρ)⁻¹ * B * fourthRoot ρ

/-- The complex linear map sending `X` to `sharp ρ B * X - X * flat ρ B`. -/
noncomputable def parentFactor (ρ B : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  LinearMap.mulLeft ℂ (sharp ρ B) - LinearMap.mulRight ℂ (flat ρ B)

section Proofs

/-- Application of the parent factor is left multiplication by `sharp ρ B` minus right
multiplication by `flat ρ B`. -/
theorem parentFactor_apply (ρ B X : Operator D) :
    parentFactor ρ B X = sharp ρ B * X - X * flat ρ B := rfl

/-- The product of the fourth root with itself equals the functional-calculus square root. -/
theorem fourthRoot_mul_self (ρ : Operator D) :
    fourthRoot ρ * fourthRoot ρ = CFC.sqrt ρ := by
  unfold fourthRoot
  exact CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)

/-- For a positive definite matrix, the product of four fourth-root factors equals the original
matrix. -/
theorem fourthRoot_mul_self_pow {ρ : Operator D} (hρ : ρ.PosDef) :
    fourthRoot ρ * fourthRoot ρ * (fourthRoot ρ * fourthRoot ρ) = ρ := by
  rw [fourthRoot_mul_self]
  exact CFC.sqrt_mul_sqrt_self ρ (Matrix.PosSemidef.nonneg (Matrix.PosDef.posSemidef hρ))

/-- The fourth root of a positive definite matrix has nonzero determinant. -/
theorem fourthRoot_det_ne_zero {ρ : Operator D} (hρ : ρ.PosDef) :
    (fourthRoot ρ).det ≠ 0 := by
  intro h
  have hdet : ρ.det = 0 := by
    conv_lhs => rw [← fourthRoot_mul_self_pow hρ]
    simp only [Matrix.det_mul]
    rw [h]
    ring
  exact (Matrix.PosDef.det_pos hρ).ne' hdet

/-- For a positive definite weight, the inverse fourth root times the fourth root equals
identity. -/
theorem fourthRoot_inv_mul {ρ : Operator D} (hρ : ρ.PosDef) :
    (fourthRoot ρ)⁻¹ * fourthRoot ρ = 1 :=
  Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ (fourthRoot_det_ne_zero hρ))

/-- For a positive definite weight, the fourth root times its inverse equals identity. -/
theorem fourthRoot_mul_inv {ρ : Operator D} (hρ : ρ.PosDef) :
    fourthRoot ρ * (fourthRoot ρ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (fourthRoot_det_ne_zero hρ))

/-- The parent factor annihilates `CFC.sqrt ρ` whenever `ρ` is positive definite. -/
theorem parentFactor_sqrt {ρ B : Operator D} (hρ : ρ.PosDef) :
    parentFactor ρ B (CFC.sqrt ρ) = 0 := by
  have h1 : (fourthRoot ρ)⁻¹ * CFC.sqrt ρ = fourthRoot ρ := by
    rw [← fourthRoot_mul_self ρ, ← Matrix.mul_assoc, fourthRoot_inv_mul hρ, Matrix.one_mul]
  have h2 : CFC.sqrt ρ * (fourthRoot ρ)⁻¹ = fourthRoot ρ := by
    rw [← fourthRoot_mul_self ρ, Matrix.mul_assoc, fourthRoot_mul_inv hρ, Matrix.mul_one]
  have hL : sharp ρ B * CFC.sqrt ρ = fourthRoot ρ * B * fourthRoot ρ := by
    unfold sharp
    simp only [Matrix.mul_assoc]
    rw [h1]
  have hR : CFC.sqrt ρ * flat ρ B = fourthRoot ρ * B * fourthRoot ρ := by
    unfold flat
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt ρ) (fourthRoot ρ)⁻¹ (B * fourthRoot ρ), h2]
  rw [parentFactor_apply, hL, hR, sub_self]

/-- For positive definite `ρ`, the parent factor is the commutator with `B` of the
inverse-weighted `X`, sandwiched by `fourthRoot ρ`. -/
theorem parentFactor_conj {ρ B X : Operator D} (hρ : ρ.PosDef) :
    parentFactor ρ B X
      = fourthRoot ρ * (B * ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹)
          - ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹) * B) * fourthRoot ρ := by
  rw [parentFactor_apply]
  unfold sharp flat
  simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, fourthRoot_inv_mul hρ,
    Matrix.mul_one]
  rw [show fourthRoot ρ * ((fourthRoot ρ)⁻¹ * (X * ((fourthRoot ρ)⁻¹ * (B * fourthRoot ρ))))
        = X * ((fourthRoot ρ)⁻¹ * (B * fourthRoot ρ)) from by
      rw [← Matrix.mul_assoc, fourthRoot_mul_inv hρ, Matrix.one_mul]]

/-- The fourth root of a positive definite matrix is invertible. -/
theorem fourthRoot_isUnit {ρ : Operator D} (hρ : ρ.PosDef) : IsUnit (fourthRoot ρ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (fourthRoot_det_ne_zero hρ)

/-- For positive definite `ρ`, the parent factor vanishes exactly when `B` commutes with
`(fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹`. -/
theorem parentFactor_eq_zero_iff {ρ B X : Operator D} (hρ : ρ.PosDef) :
    parentFactor ρ B X = 0 ↔
      B * ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹)
        = ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹) * B := by
  have hu : IsUnit (fourthRoot ρ) := fourthRoot_isUnit hρ
  rw [parentFactor_conj hρ]
  constructor
  · intro h
    have h2 : fourthRoot ρ * (B * ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹)
        - ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹) * B) = 0 :=
      (IsUnit.mul_left_eq_zero hu).mp h
    exact sub_eq_zero.mp ((IsUnit.mul_right_eq_zero hu).mp h2)
  · intro h
    rw [sub_eq_zero.mpr h]
    simp

/-- For positive definite `ρ`, all parent factors in a family vanish exactly when every family
member commutes with the same inverse-weighted matrix `X`. -/
theorem parentFactor_fam_eq_zero_iff {ι : Type*} {ρ : Operator D} (hρ : ρ.PosDef)
    (B : ι → Operator D) (X : Operator D) :
    (∀ i, parentFactor ρ (B i) X = 0) ↔
      ∀ i, B i * ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹)
        = ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹) * B i := by
  simp only [parentFactor_eq_zero_iff hρ]

/-- The finite sum of each parent-factor output's conjugate transpose times that output. -/
noncomputable def parentGram {ι : Type*} [Fintype ι] (ρ : Operator D) (B : ι → Operator D)
    (X : Operator D) : Operator D :=
  ∑ i, (parentFactor ρ (B i) X)ᴴ * (parentFactor ρ (B i) X)

/-- For positive definite `ρ`, the parent Gram sum is zero exactly when every parent-factor
output is zero. -/
theorem parentGram_eq_zero_iff {ι : Type*} [Fintype ι] {ρ : Operator D} (hρ : ρ.PosDef)
    (B : ι → Operator D) (X : Operator D) :
    parentGram ρ B X = 0 ↔ ∀ i, parentFactor ρ (B i) X = 0 := by
  classical
  constructor
  · intro h i
    have hnonneg : ∀ j, (0 : Operator D) ≤
        (parentFactor ρ (B j) X)ᴴ * (parentFactor ρ (B j) X) :=
      fun j => Matrix.PosSemidef.nonneg (Matrix.posSemidef_conjTranspose_mul_self _)
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => (parentFactor ρ (B j) X)ᴴ * (parentFactor ρ (B j) X))
      (fun j _ => hnonneg j) (Finset.mem_univ i)
    rw [parentGram] at h
    rw [h] at hle
    exact Matrix.conjTranspose_mul_self_eq_zero.mp (le_antisymm hle (hnonneg i))
  · intro h
    rw [parentGram]
    exact Finset.sum_eq_zero fun i _ => by rw [h i, Matrix.mul_zero]

end Proofs

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
