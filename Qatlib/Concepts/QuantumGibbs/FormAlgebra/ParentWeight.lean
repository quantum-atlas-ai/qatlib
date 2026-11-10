/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.DirichletForm.KmsDirichlet.KmsInnerProduct
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D : ℕ}

noncomputable def fourthRoot (ρ : Operator D) : Operator D := CFC.sqrt (CFC.sqrt ρ)

noncomputable def sharp (ρ B : Operator D) : Operator D :=
  fourthRoot ρ * B * (fourthRoot ρ)⁻¹

noncomputable def flat (ρ B : Operator D) : Operator D :=
  (fourthRoot ρ)⁻¹ * B * fourthRoot ρ

noncomputable def parentFactor (ρ B : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  LinearMap.mulLeft ℂ (sharp ρ B) - LinearMap.mulRight ℂ (flat ρ B)

section Proofs

theorem parentFactor_apply (ρ B X : Operator D) :
    parentFactor ρ B X = sharp ρ B * X - X * flat ρ B := rfl

theorem fourthRoot_mul_self (ρ : Operator D) :
    fourthRoot ρ * fourthRoot ρ = CFC.sqrt ρ := by
  unfold fourthRoot
  exact CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)

theorem fourthRoot_mul_self_pow {ρ : Operator D} (hρ : ρ.PosDef) :
    fourthRoot ρ * fourthRoot ρ * (fourthRoot ρ * fourthRoot ρ) = ρ := by
  rw [fourthRoot_mul_self]
  exact CFC.sqrt_mul_sqrt_self ρ (Matrix.PosSemidef.nonneg (Matrix.PosDef.posSemidef hρ))

theorem fourthRoot_det_ne_zero {ρ : Operator D} (hρ : ρ.PosDef) :
    (fourthRoot ρ).det ≠ 0 := by
  intro h
  have hdet : ρ.det = 0 := by
    conv_lhs => rw [← fourthRoot_mul_self_pow hρ]
    simp only [Matrix.det_mul]
    rw [h]
    ring
  exact (Matrix.PosDef.det_pos hρ).ne' hdet

theorem fourthRoot_inv_mul {ρ : Operator D} (hρ : ρ.PosDef) :
    (fourthRoot ρ)⁻¹ * fourthRoot ρ = 1 :=
  Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ (fourthRoot_det_ne_zero hρ))

theorem fourthRoot_mul_inv {ρ : Operator D} (hρ : ρ.PosDef) :
    fourthRoot ρ * (fourthRoot ρ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ (fourthRoot_det_ne_zero hρ))

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

theorem fourthRoot_isUnit {ρ : Operator D} (hρ : ρ.PosDef) : IsUnit (fourthRoot ρ) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr (fourthRoot_det_ne_zero hρ)

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

theorem parentFactor_fam_eq_zero_iff {ι : Type*} {ρ : Operator D} (hρ : ρ.PosDef)
    (B : ι → Operator D) (X : Operator D) :
    (∀ i, parentFactor ρ (B i) X = 0) ↔
      ∀ i, B i * ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹)
        = ((fourthRoot ρ)⁻¹ * X * (fourthRoot ρ)⁻¹) * B i := by
  simp only [parentFactor_eq_zero_iff hρ]

noncomputable def parentGram {ι : Type*} [Fintype ι] (ρ : Operator D) (B : ι → Operator D)
    (X : Operator D) : Operator D :=
  ∑ i, (parentFactor ρ (B i) X)ᴴ * (parentFactor ρ (B i) X)

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
