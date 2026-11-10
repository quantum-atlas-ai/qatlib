/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.ReverseKernel.TimeReverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MarkovChains.ReverseKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

def flat (P : Matrix I I ℝ) : Matrix I I ℝ := fun x y => Real.sqrt (P x y*P y x)

def curved (P : Matrix I I ℝ) (π : I → ℝ) : Matrix I I ℝ :=
  fun x y => Real.sqrt (P x y*reverse P π y x)

def weight (π : I → ℝ) : Matrix I I ℝ := diagonal (fun x => Real.sqrt (π x))

def weightInv (π : I → ℝ) : Matrix I I ℝ := diagonal (fun x => (Real.sqrt (π x))⁻¹)

theorem weight_mul_inverse (π : I → ℝ) (hπ : ∀ x,0 < π x) : weight π*weightInv π=1 := by
  rw [weight,weightInv,Matrix.diagonal_mul_diagonal]
  have h (x : I) : Real.sqrt (π x)*(Real.sqrt (π x))⁻¹=1 :=
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hπ x)))
  simp_rw [h]
  exact Matrix.diagonal_one

theorem inverse_mul_weight (π : I → ℝ) (hπ : ∀ x,0 < π x) : weightInv π*weight π=1 := by
  rw [weightInv,weight,Matrix.diagonal_mul_diagonal]
  have h (x : I) : (Real.sqrt (π x))⁻¹*Real.sqrt (π x)=1 :=
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hπ x)))
  simp_rw [h]
  exact Matrix.diagonal_one

theorem curved_entry (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (x y : I) :
    curved P π x y=Real.sqrt (π x)*P x y/Real.sqrt (π y) := by
  unfold curved reverse
  rw [show P x y*(π x*P x y/π y)=π x*(P x y)^2/π y by ring]
  rw [Real.sqrt_div (mul_nonneg (hπ x).le (sq_nonneg _)),Real.sqrt_mul (hπ x).le,Real.sqrt_sq (hP.1 x y)]

theorem curved_similarity (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) :
    curved P π=weight π*P*weightInv π := by
  ext x y
  rw [curved_entry P π hP hπ,weight,weightInv,Matrix.mul_diagonal,Matrix.diagonal_mul]
  ring
omit [Fintype I] [DecidableEq I] in

theorem curved_reverse (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) :
    curved (reverse P π) π=(curved P π)ᵀ := by
  ext x y
  change Real.sqrt (reverse P π x y*reverse (reverse P π) π y x)=Real.sqrt (P y x*reverse P π x y)
  rw [reverse_reverse P π hπ,mul_comm]

theorem curved_gram_similarity (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (hstat : Stationary P π) :
    (curved P π)ᵀ*curved P π=weight π*(reverse P π*P)*weightInv π := by
  rw [← curved_reverse P π hπ,curved_similarity (reverse P π) π (reverse_stochastic P π hP hπ hstat) hπ,
    curved_similarity P π hP hπ]
  calc
    _ = weight π*reverse P π*(weightInv π*weight π)*P*weightInv π := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [inverse_mul_weight π hπ,Matrix.mul_one];simp only [Matrix.mul_assoc]

theorem diagonal_charpoly (A : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) :
    (weight π*A*weightInv π).charpoly=A.charpoly := by
  rw [Matrix.mul_assoc,Matrix.charpoly_mul_comm,Matrix.mul_assoc,inverse_mul_weight π hπ,Matrix.mul_one]

theorem curved_charpoly (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) : (curved P π).charpoly=P.charpoly := by
  rw [curved_similarity P π hP hπ,diagonal_charpoly P π hπ]

theorem curved_gram_charpoly (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (hstat : Stationary P π) :
    ((curved P π)ᵀ*curved P π).charpoly=(reverse P π*P).charpoly := by
  rw [curved_gram_similarity P π hP hπ hstat,diagonal_charpoly _ π hπ]
end Qatlib.Foundations.MarkovChains.ReverseKernel
