/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic.Module

@[expose] public section


noncomputable section



/-!
# Rank factorization of complex matrices

Reusable linear-algebra facts about `Matrix.rank` over `ℂ`:

* `Qatlib.Foundations.PPTMatrix.OperatorCones.exists_mul_eq_rank`: every matrix `V` factors as `V = W * V'` through
  `Fin V.rank`.
* `Qatlib.Foundations.PPTMatrix.OperatorCones.rank_le_iff_exists_mul`: `V.rank ≤ r` if and only if `V` factors through
  `Fin r`.
* `Qatlib.Foundations.PPTMatrix.OperatorCones.exists_eq_vecMulVec_of_rank_le_one` and
  `Qatlib.Foundations.PPTMatrix.OperatorCones.rank_vecMulVec_le_one`: the matrices of rank at most one are exactly the
  outer products `Matrix.vecMulVec a b`.
* `Qatlib.Foundations.PPTMatrix.OperatorCones.rank_add_le` and `Qatlib.Foundations.PPTMatrix.OperatorCones.rank_fromRows_le`: subadditivity of
  the rank under addition and under stacking of rows.
* `Qatlib.Foundations.PPTMatrix.OperatorCones.exists_sum_vecMulVec_of_posSemidef`: every positive semidefinite matrix is
  a finite sum of rank-one matrices `Matrix.vecMulVec v (star v)`.
-/

open scoped ComplexOrder MatrixOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

/-- Rank factorization: every matrix `V` is a product `W * V'` whose intermediate index type is
`Fin V.rank`. The columns of `W` form a basis of the column space of `V`, and the columns of `V'`
are the coordinates of the columns of `V` in that basis. -/
theorem exists_mul_eq_rank {m n : Type*} [Fintype n] (V : Matrix m n ℂ) :
    ∃ (W : Matrix m (Fin V.rank) ℂ) (V' : Matrix (Fin V.rank) n ℂ), V = W * V' := by
  classical
  have hd : Module.finrank ℂ (LinearMap.range V.mulVecLin) = V.rank := rfl
  have b := Module.finBasisOfFinrankEq ℂ (LinearMap.range V.mulVecLin) hd
  have key : ∀ j : n, ∃ c : Fin V.rank → ℂ, ∀ i : m,
      V i j = ∑ k, c k * ((b k : LinearMap.range V.mulVecLin) : m → ℂ) i := by
    intro j
    obtain ⟨y, hy⟩ : ∃ y : LinearMap.range V.mulVecLin,
        (y : m → ℂ) = V.mulVecLin (Pi.single j 1) :=
      ⟨⟨V.mulVecLin (Pi.single j 1), LinearMap.mem_range_self V.mulVecLin (Pi.single j 1)⟩, rfl⟩
    refine ⟨fun k => b.repr y k, fun i => ?_⟩
    have h1 : ((∑ k, b.repr y k • b k : LinearMap.range V.mulVecLin) : m → ℂ) i =
        (y : m → ℂ) i := by
      rw [b.sum_repr y]
    have h2 : (y : m → ℂ) i = V i j := by
      rw [hy, Matrix.mulVecLin_apply]
      exact congrFun (Matrix.mulVec_single_one V j) i
    have h3 : ((∑ k, b.repr y k • b k : LinearMap.range V.mulVecLin) : m → ℂ) i =
        ∑ k, b.repr y k * ((b k : LinearMap.range V.mulVecLin) : m → ℂ) i := by
      simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
        smul_eq_mul]
    exact h2.symm.trans (h1.symm.trans h3)
  choose c hc using key
  refine ⟨Matrix.of fun i k => ((b k : LinearMap.range V.mulVecLin) : m → ℂ) i,
    Matrix.of fun k j => c j k, ?_⟩
  ext i j
  rw [hc j i, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.of_apply]
  exact mul_comm _ _

/-- Rank factorization with padding: a matrix of rank at most `r` factors through `Fin r`. -/
theorem exists_mul_eq_of_rank_le {m n : Type*} [Fintype n] {V : Matrix m n ℂ} {r : ℕ}
    (h : V.rank ≤ r) :
    ∃ (W : Matrix m (Fin r) ℂ) (V' : Matrix (Fin r) n ℂ), V = W * V' := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨W₀, V₀, hV⟩ := exists_mul_eq_rank V
  have e : Fin (V.rank + s) ≃ Fin V.rank ⊕ Fin s := finSumFinEquiv.symm
  refine ⟨(Matrix.fromCols W₀ (0 : Matrix m (Fin s) ℂ)).submatrix id e,
    (Matrix.fromRows V₀ (0 : Matrix (Fin s) n ℂ)).submatrix e id, ?_⟩
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
    Matrix.submatrix_id_id]
  exact hV

/-- A product through `Fin r` has rank at most `r`. -/
theorem rank_mul_le_card {m n : Type*} [Fintype n] {r : ℕ} (W : Matrix m (Fin r) ℂ)
    (V' : Matrix (Fin r) n ℂ) : (W * V').rank ≤ r :=
  (Matrix.rank_mul_le_right W V').trans
    ((Matrix.rank_le_card_height V').trans_eq (Fintype.card_fin r))

/-- A matrix has rank at most `r` if and only if it factors through `Fin r`. -/
theorem rank_le_iff_exists_mul {m n : Type*} [Fintype n] {V : Matrix m n ℂ} {r : ℕ} :
    V.rank ≤ r ↔ ∃ (W : Matrix m (Fin r) ℂ) (V' : Matrix (Fin r) n ℂ), V = W * V' := by
  constructor
  · exact exists_mul_eq_of_rank_le
  · rintro ⟨W, V', rfl⟩
    exact rank_mul_le_card W V'

/-- A matrix of rank at most one is an outer product. -/
theorem exists_eq_vecMulVec_of_rank_le_one {m n : Type*} [Fintype n]
    {V : Matrix m n ℂ} (h : V.rank ≤ 1) :
    ∃ (a : m → ℂ) (b : n → ℂ), V = Matrix.vecMulVec a b := by
  obtain ⟨W, V', hV⟩ := exists_mul_eq_of_rank_le h
  refine ⟨fun i => W i 0, fun j => V' 0 j, ?_⟩
  rw [hV]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.vecMulVec_apply]

/-- An outer product has rank at most one. -/
theorem rank_vecMulVec_le_one {m n : Type*} [Fintype n] (a : m → ℂ) (b : n → ℂ) :
    (Matrix.vecMulVec a b).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le a b

/-- The rank of complex matrices is subadditive. -/
theorem rank_add_le {m n : Type*} [Fintype n] (A B : Matrix m n ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine Submodule.mem_sup.mpr ⟨A.mulVecLin v, LinearMap.mem_range_self _ _,
      B.mulVecLin v, LinearMap.mem_range_self _ _, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
  have h1 : Module.finrank ℂ (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank ℂ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank ℂ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) ≤
      Module.finrank ℂ (LinearMap.range A.mulVecLin) +
        Module.finrank ℂ (LinearMap.range B.mulVecLin) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  exact h1.trans h2

/-- Stacking bound: the rank of two matrices stacked on top of each other is at most the sum of
their ranks. -/
theorem rank_fromRows_le {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂] [Fintype n]
    (V₁ : Matrix m₁ n ℂ) (V₂ : Matrix m₂ n ℂ) :
    (Matrix.fromRows V₁ V₂).rank ≤ V₁.rank + V₂.rank := by
  classical
  have h1 : (Matrix.fromRows V₁ (0 : Matrix m₂ n ℂ)).rank ≤ V₁.rank := by
    have e : Matrix.fromRows V₁ (0 : Matrix m₂ n ℂ) =
        Matrix.fromRows (1 : Matrix m₁ m₁ ℂ) (0 : Matrix m₂ m₁ ℂ) * V₁ := by
      rw [Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    rw [e]
    exact Matrix.rank_mul_le_right _ _
  have h2 : (Matrix.fromRows (0 : Matrix m₁ n ℂ) V₂).rank ≤ V₂.rank := by
    have e : Matrix.fromRows (0 : Matrix m₁ n ℂ) V₂ =
        Matrix.fromRows (0 : Matrix m₁ m₂ ℂ) (1 : Matrix m₂ m₂ ℂ) * V₂ := by
      rw [Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    rw [e]
    exact Matrix.rank_mul_le_right _ _
  have hsum : Matrix.fromRows V₁ V₂ =
      Matrix.fromRows V₁ (0 : Matrix m₂ n ℂ) + Matrix.fromRows (0 : Matrix m₁ n ℂ) V₂ := by
    ext (i | i) j <;> simp
  rw [hsum]
  exact (rank_add_le _ _).trans (add_le_add h1 h2)

/-- Every positive semidefinite matrix is a finite sum of rank-one matrices of the form
`Matrix.vecMulVec v (star v)`, obtained from the rows of a Gram factor `X = star G * G`. -/
theorem exists_sum_vecMulVec_of_posSemidef {n : Type*} [Fintype n] {X : Matrix n n ℂ}
    (hX : X.PosSemidef) :
    ∃ (N : ℕ) (v : Fin N → n → ℂ), X = ∑ k, Matrix.vecMulVec (v k) (star (v k)) := by
  classical
  obtain ⟨G, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX.nonneg
  refine ⟨Fintype.card n, fun k i => star (G ((Fintype.equivFin n).symm k) i), ?_⟩
  ext i j
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_star,
    Matrix.mul_apply, Matrix.star_apply]
  exact (Equiv.sum_comp (Fintype.equivFin n).symm (fun k => star (G k i) * G k j)).symm

end Qatlib.Foundations.PPTMatrix.OperatorCones
