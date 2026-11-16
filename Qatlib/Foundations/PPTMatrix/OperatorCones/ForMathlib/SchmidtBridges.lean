/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtNumber

@[expose] public section




/-!
# Coefficient rank, orthonormal tensor families, and reference isometries.

Finite coordinate isometries preserve coefficient-matrix ranks. Rank factorization and orthonormal columns then identify the number of nonzero Schmidt terms and construct the actual reference isometry used by the lifting argument.
-/

open Matrix
open scoped Kronecker

namespace Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSchmidt

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype r] [DecidableEq m] in
/-- Matrix columns are orthonormal exactly when their Gram matrix is the identity. -/
theorem orthonormal_columns_iff (U : Matrix m r ℂ) :
    Orthonormal ℂ (fun j => WithLp.toLp 2 (Uᵀ j)) ↔ Uᴴ * U = 1 := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h
    ext i j
    rw [← inner_matrix_col_col, h, Matrix.one_apply]
  · intro h i j
    rw [inner_matrix_col_col, h, Matrix.one_apply]

omit [DecidableEq m] [DecidableEq n] in
/-- A left inverse preserves the rank of a matrix multiplied on the left. -/
theorem rank_left_isometry (U : Matrix m r ℂ) (A : Matrix r n ℂ)
    (hU : Uᴴ * U = 1) : (U * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc
    A.rank = (Uᴴ * (U * A)).rank := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ ≤ (U * A).rank := Matrix.rank_mul_le_right _ _

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- A right inverse preserves the rank of a matrix multiplied on the right. -/
theorem rank_right_coisometry (A : Matrix m r ℂ) (V : Matrix n r ℂ)
    (hV : Vᴴ * V = 1) : (A * Vᴴ).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  calc
    A.rank = (A * Vᴴ * V).rank := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
    _ ≤ (A * Vᴴ).rank := Matrix.rank_mul_le_left _ _

omit [DecidableEq m] [DecidableEq n] in
/-- The rank of a thin orthonormal SVD is its number of nonzero coefficients.
No positivity assumption is needed for this algebraic identity. -/
theorem rank_orthonormal_diagonal (U : Matrix m r ℂ) (V : Matrix n r ℂ)
    (s : r → ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U * diagonal s * Vᴴ).rank = Fintype.card {j // s j ≠ 0} := by
  classical
  rw [rank_right_coisometry _ _ hV, rank_left_isometry _ _ hU, Matrix.rank_diagonal]

omit [DecidableEq m] [DecidableEq n] in
/-- In tensor coordinates the second factor is not conjugated. This is the
rank/count identity for any actual orthonormal Schmidt expansion. -/
theorem schmidtRank_eq_nonzero_terms
    (a : r → EuclideanSpace ℂ m) (b : r → EuclideanSpace ℂ n)
    (s : r → ℝ) (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b) :
    schmidtRank (fun ij : m × n => ∑ j, (s j : ℂ) * a j ij.1 * b j ij.2) =
      Fintype.card {j // s j ≠ 0} := by
  classical
  let U : Matrix m r ℂ := fun i j => a j i
  let V : Matrix n r ℂ := fun i j => star (b j i)
  have hU : Uᴴ * U = 1 := by
    apply (orthonormal_columns_iff U).mp
    change Orthonormal ℂ a
    exact ha
  let B₀ : Matrix n r ℂ := fun i j => b j i
  have hB : B₀ᴴ * B₀ = 1 := by
    apply (orthonormal_columns_iff B₀).mp
    change Orthonormal ℂ b
    exact hb
  have hV : Vᴴ * V = 1 := by
    apply Matrix.ext
    intro i j
    change (∑ k, star (star (b i k)) * star (b j k)) =
      if i = j then (1 : ℂ) else 0
    have hij : (∑ k, star (b i k) * b j k) =
        (if i = j then (1 : ℂ) else 0) :=
      congrArg (fun M : Matrix r r ℂ => M i j) hB
    have h := congrArg star hij
    simpa only [star_sum, star_mul, star_star, apply_ite,
      star_one, star_zero, mul_comm] using h
  have hcoeff : coeffMatrix (fun ij : m × n => ∑ j, (s j : ℂ) * a j ij.1 * b j ij.2) =
      U * diagonal (fun j => (s j : ℂ)) * Vᴴ := by
    apply Matrix.ext
    intro i k
    have hentry : (U * diagonal (fun j => (s j : ℂ)) * Vᴴ) i k =
        ∑ j, (U i j * (s j : ℂ)) * star (V k j) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [hentry]
    simp only [coeffMatrix_apply, U, V, star_star]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold schmidtRank
  rw [hcoeff, rank_orthonormal_diagonal _ _ _ hU hV]
  simp only [ne_eq, Complex.ofReal_eq_zero]

omit [DecidableEq m] in
/-- Every coefficient matrix has an orthonormal basis of its actual column
space, including rank zero. The second factor is its coordinate matrix. -/
theorem exists_isometry_rank_factorization (A : Matrix m n ℂ) :
    ∃ U : Matrix m (Fin A.rank) ℂ,
      Uᴴ * U = 1 ∧ A = U * (Uᴴ * A) ∧
        ∀ j, ∃ z : n → ℂ, A *ᵥ z = Uᵀ j := by
  classical
  let T := A.toEuclideanLin
  have hd : Module.finrank ℂ T.range = A.rank := by
    exact (A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℂ).toBasis
      (EuclideanSpace.basisFun n ℂ).toBasis).symm
  let b : OrthonormalBasis (Fin A.rank) ℂ T.range :=
    (stdOrthonormalBasis ℂ T.range).reindex (finCongr hd)
  let U : Matrix m (Fin A.rank) ℂ := fun i j => (b j : EuclideanSpace ℂ m) i
  have hU : Uᴴ * U = 1 := by
    ext i j
    rw [← inner_matrix_col_col]
    change inner ℂ (b i) (b j) = (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) i j
    rw [b.inner_eq_ite, Matrix.one_apply]
  let col : n → T.range := fun j =>
    ⟨T (WithLp.toLp 2 (Pi.single j 1)), LinearMap.mem_range_self _ _⟩
  have hcol (j : n) (i : m) : (col j : EuclideanSpace ℂ m) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    exact congrFun (Matrix.mulVec_single_one A j) i
  let B : Matrix (Fin A.rank) n ℂ := fun k j => b.repr (col j) k
  have hA : A = U * B := by
    ext i j
    have h := congrArg (fun x : T.range => (x : EuclideanSpace ℂ m) i) (b.sum_repr (col j))
    rw [Matrix.mul_apply]
    calc
      A i j = (col j : EuclideanSpace ℂ m) i := (hcol j i).symm
      _ = ∑ k, b.repr (col j) k * (b k : EuclideanSpace ℂ m) i := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum,
          Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] using h.symm
      _ = ∑ k, U i k * B k j := by
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  refine ⟨U, hU, ?_, ?_⟩
  · have hB : Uᴴ * A = B := by
      calc
        Uᴴ * A = Uᴴ * (U * B) :=
          congrArg (fun X : Matrix m n ℂ => Uᴴ * X) hA
        _ = B := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    exact hA.trans (congrArg (fun X : Matrix (Fin A.rank) n ℂ => U * X) hB.symm)
  · intro j
    obtain ⟨z, hz⟩ := (b j).property
    refine ⟨WithLp.ofLp z, ?_⟩
    exact congrArg WithLp.ofLp hz

omit [DecidableEq m] in
/-- Exact reference-isometry realization of a vector on its Schmidt-rank
dimensional reference space; no normalization or nonzero hypothesis is used. -/
theorem exists_reference_isometry (v : m × n → ℂ) :
    ∃ (U : Matrix m (Fin (schmidtRank v)) ℂ)
      (w : Fin (schmidtRank v) × n → ℂ),
      Uᴴ * U = 1 ∧ v = (U ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ w := by
  unfold schmidtRank
  obtain ⟨U, hU, hA, -⟩ := exists_isometry_rank_factorization (coeffMatrix v)
  let w : Fin (coeffMatrix v).rank × n → ℂ := fun ij => (Uᴴ * coeffMatrix v) ij.1 ij.2
  refine ⟨U, w, hU, ?_⟩
  have h : coeffMatrix v = coeffMatrix ((U ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ w) := by
    rw [coeffMatrix_kronecker_mulVec, Matrix.transpose_one, Matrix.mul_one]
    exact hA
  funext ij
  exact congrFun (congrFun h ij.1) ij.2

end Qatlib.Foundations.PPTMatrix.OperatorCones.ManuscriptSchmidt
