/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MarkovChains.ReverseKernel.TimeReverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Weighted discriminants and diagonal similarity

`flat` and `curved` define discriminant matrices from a real matrix and its weighted reverse.
For a row-stochastic matrix and positive weights, `curved_similarity` identifies the curved
discriminant with conjugation by the diagonal matrix of square-root weights.

This similarity transports characteristic polynomials, and `curved_gram_similarity` relates the
discriminant Gram matrix to the reverse-forward product when the weights are stationary. For the
nonreversible quantum-walk setting, see [ClaudonPiquemalMonmarche2025].

## Main statements

* `curved_similarity`: Positive diagonal similarity of the curved discriminant.
* `curved_gram_similarity`: Similarity for the Gram matrix under stationarity.
* `curved_gram_charpoly`: Characteristic polynomial of the reverse-forward product.

## References

* [Claudon et al., 2025][ClaudonPiquemalMonmarche2025]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MarkovChains.ReverseKernel
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The real matrix with entries `sqrt (P x y * P y x)`. -/
def flat (P : Matrix I I ℝ) : Matrix I I ℝ := fun x y => Real.sqrt (P x y*P y x)

/-- The real matrix with entries `sqrt (P x y * reverse P π y x)`. -/
def curved (P : Matrix I I ℝ) (π : I → ℝ) : Matrix I I ℝ :=
  fun x y => Real.sqrt (P x y*reverse P π y x)

/-- The diagonal matrix of square roots of the weights `π`. -/
def weight (π : I → ℝ) : Matrix I I ℝ := diagonal (fun x => Real.sqrt (π x))

/-- The diagonal matrix of reciprocals of the square roots of the weights `π`. -/
def weightInv (π : I → ℝ) : Matrix I I ℝ := diagonal (fun x => (Real.sqrt (π x))⁻¹)

/-- For strictly positive weights, `weight π * weightInv π` is the identity. -/
theorem weight_mul_inverse (π : I → ℝ) (hπ : ∀ x,0 < π x) : weight π*weightInv π=1 := by
  rw [weight,weightInv,Matrix.diagonal_mul_diagonal]
  have h (x : I) : Real.sqrt (π x)*(Real.sqrt (π x))⁻¹=1 :=
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hπ x)))
  simp_rw [h]
  exact Matrix.diagonal_one

/-- For strictly positive weights, `weightInv π * weight π` is the identity. -/
theorem inverse_mul_weight (π : I → ℝ) (hπ : ∀ x,0 < π x) : weightInv π*weight π=1 := by
  rw [weightInv,weight,Matrix.diagonal_mul_diagonal]
  have h (x : I) : (Real.sqrt (π x))⁻¹*Real.sqrt (π x)=1 :=
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hπ x)))
  simp_rw [h]
  exact Matrix.diagonal_one

/-- For a row-stochastic matrix and positive weights, each curved discriminant entry is `sqrt (π
x) * P x y / sqrt (π y)`. -/
theorem curved_entry (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (x y : I) :
    curved P π x y=Real.sqrt (π x)*P x y/Real.sqrt (π y) := by
  unfold curved reverse
  rw [show P x y*(π x*P x y/π y)=π x*(P x y)^2/π y by ring]
  rw [Real.sqrt_div (mul_nonneg (hπ x).le (sq_nonneg _)),Real.sqrt_mul (hπ x).le,Real.sqrt_sq (hP.1 x y)]

/-- The curved discriminant of a row-stochastic matrix with positive weights is `weight π * P *
weightInv π`. -/
theorem curved_similarity (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) :
    curved P π=weight π*P*weightInv π := by
  ext x y
  rw [curved_entry P π hP hπ,weight,weightInv,Matrix.mul_diagonal,Matrix.diagonal_mul]
  ring
omit [Fintype I] [DecidableEq I] in

/-- With strictly positive weights, the curved discriminant of the reversed matrix is the
transpose of the original curved discriminant. -/
theorem curved_reverse (P : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) :
    curved (reverse P π) π=(curved P π)ᵀ := by
  ext x y
  change Real.sqrt (reverse P π x y*reverse (reverse P π) π y x)=Real.sqrt (P y x*reverse P π x y)
  rw [reverse_reverse P π hπ,mul_comm]

/-- For a row-stochastic matrix with positive stationary weights, the curved discriminant Gram
matrix is diagonally similar to `reverse P π * P`. -/
theorem curved_gram_similarity (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (hstat : Stationary P π) :
    (curved P π)ᵀ*curved P π=weight π*(reverse P π*P)*weightInv π := by
  rw [← curved_reverse P π hπ,curved_similarity (reverse P π) π (reverse_stochastic P π hP hπ hstat) hπ,
    curved_similarity P π hP hπ]
  calc
    _ = weight π*reverse P π*(weightInv π*weight π)*P*weightInv π := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [inverse_mul_weight π hπ,Matrix.mul_one];simp only [Matrix.mul_assoc]

/-- Conjugating a real matrix by the square-root weight matrix and its inverse preserves its
characteristic polynomial. -/
theorem diagonal_charpoly (A : Matrix I I ℝ) (π : I → ℝ) (hπ : ∀ x,0 < π x) :
    (weight π*A*weightInv π).charpoly=A.charpoly := by
  rw [Matrix.mul_assoc,Matrix.charpoly_mul_comm,Matrix.mul_assoc,inverse_mul_weight π hπ,Matrix.mul_one]

/-- The curved discriminant of a row-stochastic matrix with positive weights has the same
characteristic polynomial as the matrix. -/
theorem curved_charpoly (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) : (curved P π).charpoly=P.charpoly := by
  rw [curved_similarity P π hP hπ,diagonal_charpoly P π hπ]

/-- For positive stationary weights, the curved discriminant Gram matrix and the reverse-forward
product have the same characteristic polynomial. -/
theorem curved_gram_charpoly (P : Matrix I I ℝ) (π : I → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ I) (hπ : ∀ x,0 < π x) (hstat : Stationary P π) :
    ((curved P π)ᵀ*curved P π).charpoly=(reverse P π*P).charpoly := by
  rw [curved_gram_similarity P π hP hπ hstat,diagonal_charpoly _ π hπ]
end Qatlib.Foundations.MarkovChains.ReverseKernel
