/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation.BireflectionFactorization
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

/-!
# A complete right singular family for a real matrix

[KerenidisPrakash2017], Section 5.2, uses a singular-value expansion of the
input. The Gram matrix supplies a complete orthonormal right basis, including
the entire right null space. For positive singular values the associated left
images form an orthonormal family. The ensuing decomposition into walk
eigenphases is a separate step.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation (frobSq frobSq_eq_norm_sq)
open scoped BigOperators Matrix.Norms.Frobenius

variable {rows columns : ℕ}

/-- The Gram matrix on the input column space. -/
def rightGram (A : Matrix (Fin rows) (Fin columns) ℝ) : Matrix (Fin columns) (Fin columns) ℝ := Aᵀ * A

/-- A Gram pairing is the dot product of the two matrix images. -/
private theorem right_gram_dot_product (A : Matrix (Fin rows) (Fin columns) ℝ) (x y : Fin columns → ℝ) :
    x ⬝ᵥ (rightGram A *ᵥ y) = (A *ᵥ x) ⬝ᵥ (A *ᵥ y) := by
  unfold rightGram
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Aᵀ, Matrix.vecMul_transpose]

/-- The right Gram matrix is positive semidefinite. -/
theorem right_gram_pos_semidef (A : Matrix (Fin rows) (Fin columns) ℝ) : (rightGram A).PosSemidef := by
  have hHermitian : (rightGram A).IsHermitian := by
    simpa only [rightGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian fun x => ?_
  rw [star_trivial, right_gram_dot_product]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((A *ᵥ x) i)

/-- A choice of complete right singular basis, indexed by the input dimension. -/
def rightSingularBasis (A : Matrix (Fin rows) (Fin columns) ℝ) :
    OrthonormalBasis (Fin columns) ℝ (EuclideanSpace ℝ (Fin columns)) :=
  (right_gram_pos_semidef A).isHermitian.eigenvectorBasis

/-- Right singular vectors as real coordinate functions. -/
def rightSingularVector (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : Fin columns → ℝ :=
  WithLp.ofLp (rightSingularBasis A j)

/-- Singular values are the square roots of the positive semidefinite Gram spectrum. -/
def rightSingularValue (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : ℝ :=
  Real.sqrt ((right_gram_pos_semidef A).isHermitian.eigenvalues j)

/-- The Gram eigenvalue is the square of the corresponding singular value. -/
theorem right_singular_value_sq (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) :
    rightSingularValue A j ^ 2 = (right_gram_pos_semidef A).isHermitian.eigenvalues j :=
  Real.sq_sqrt ((right_gram_pos_semidef A).eigenvalues_nonneg j)

/-- Each right singular vector is a Gram eigenvector. -/
theorem right_gram_mulVec_singular_vector (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) :
    rightGram A *ᵥ rightSingularVector A j = (rightSingularValue A j ^ 2) • rightSingularVector A j := by
  rw [right_singular_value_sq]
  exact (right_gram_pos_semidef A).isHermitian.mulVec_eigenvectorBasis j

/-- Right singular vectors have Kronecker-delta real dot products. -/
theorem right_singular_vectors_orthonormal (A : Matrix (Fin rows) (Fin columns) ℝ) (j k : Fin columns) :
    rightSingularVector A j ⬝ᵥ rightSingularVector A k = if j = k then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (rightSingularBasis A).orthonormal) k j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa only [rightSingularVector, star_trivial, eq_comm] using h

/-- Every real user row has its full expansion in the right singular basis. -/
theorem right_singular_vector_expansion (A : Matrix (Fin rows) (Fin columns) ℝ) (x : Fin columns → ℝ) :
    (∑ j, (x ⬝ᵥ rightSingularVector A j) • rightSingularVector A j) = x := by
  have h := congrArg WithLp.ofLp ((rightSingularBasis A).sum_repr' (WithLp.toLp 2 x))
  simpa only [rightSingularVector, WithLp.ofLp_sum, WithLp.ofLp_smul,
    EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using h

/-- The squared singular values sum to the squared Frobenius norm. -/
theorem sum_right_singular_value_sq (A : Matrix (Fin rows) (Fin columns) ℝ) :
    ∑ j, rightSingularValue A j ^ 2 = ‖A‖ ^ 2 := by
  simp_rw [right_singular_value_sq]
  rw [← frobSq_eq_norm_sq]
  calc
    _ = (rightGram A).trace := by
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using
        (right_gram_pos_semidef A).isHermitian.trace_eq_sum_eigenvalues.symm
    _ = _ := by
      change (∑ j, ∑ i, A i j * A i j) = ∑ i, ∑ j, A i j ^ 2
      simp only [pow_two]
      exact Finset.sum_comm

/-- Every singular value lies between zero and the Frobenius norm. -/
theorem right_singular_value_bounds (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) :
    0 ≤ rightSingularValue A j ∧ rightSingularValue A j ≤ ‖A‖ := by
  have hj : 0 ≤ rightSingularValue A j := Real.sqrt_nonneg _
  refine ⟨hj, (sq_le_sq₀ hj (norm_nonneg _)).mp ?_⟩
  rw [← sum_right_singular_value_sq]
  exact Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => sq_nonneg (rightSingularValue A k))
    (Finset.mem_univ j)

/-- A zero right singular value supplies a null vector even for a wide matrix. -/
theorem mulVec_right_singular_vector_eq_zero (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns)
    (h : rightSingularValue A j = 0) : A *ᵥ rightSingularVector A j = 0 := by
  let v := rightSingularVector A j
  have hGram : rightGram A *ᵥ v = 0 := by
    simp [v, right_gram_mulVec_singular_vector, h]
  have hSq : ∑ i, (A *ᵥ v) i ^ 2 = 0 := by
    have hDot := (right_gram_dot_product A v v).symm
    rw [hGram, dotProduct_zero] at hDot
    simpa only [pow_two, dotProduct] using hDot
  funext i
  have hi := Finset.single_le_sum (f := fun k => (A *ᵥ v) k ^ 2)
    (fun k _ => sq_nonneg ((A *ᵥ v) k)) (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp (le_antisymm (hi.trans_eq hSq) (sq_nonneg _))

/-- The left vector associated to a positive singular value is its normalized matrix image. -/
def leftSingularVectorOfPositive (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : Fin rows → ℝ :=
  (rightSingularValue A j)⁻¹ • (A *ᵥ rightSingularVector A j)

/-- A positive singular value has both singular vector equations. -/
theorem positive_singular_pair (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns)
    (h : 0 < rightSingularValue A j) :
    A *ᵥ rightSingularVector A j = rightSingularValue A j • leftSingularVectorOfPositive A j ∧
    Aᵀ *ᵥ leftSingularVectorOfPositive A j = rightSingularValue A j • rightSingularVector A j := by
  unfold leftSingularVectorOfPositive
  constructor
  · rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]
  · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    change (rightSingularValue A j)⁻¹ • (rightGram A *ᵥ rightSingularVector A j) = _
    rw [right_gram_mulVec_singular_vector, smul_smul, pow_two, ← mul_assoc, inv_mul_cancel₀ h.ne', one_mul]

/-- The left vectors associated to positive singular values are orthonormal. -/
theorem positive_left_singular_vectors_orthonormal (A : Matrix (Fin rows) (Fin columns) ℝ) (j k : Fin columns)
    (hj : 0 < rightSingularValue A j) :
    leftSingularVectorOfPositive A j ⬝ᵥ leftSingularVectorOfPositive A k = if j = k then 1 else 0 := by
  have hDot : (A *ᵥ rightSingularVector A j) ⬝ᵥ (A *ᵥ rightSingularVector A k) =
      rightSingularVector A j ⬝ᵥ (rightGram A *ᵥ rightSingularVector A k) := by
    exact (right_gram_dot_product A _ _).symm
  unfold leftSingularVectorOfPositive
  rw [smul_dotProduct, dotProduct_smul, hDot, right_gram_mulVec_singular_vector,
    dotProduct_smul, right_singular_vectors_orthonormal]
  by_cases h : j = k
  · subst k
    simp only [ite_true, smul_eq_mul, mul_one, pow_two]
    field_simp [hj.ne']
  · simp [h]

end Qatlib.Papers.QRecommender16.Recommendations
