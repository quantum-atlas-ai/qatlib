/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Hermitian block lifts and compression

`lift` places a rectangular complex matrix and its adjoint in opposite off-diagonal blocks,
producing a Hermitian matrix. For a unitary square matrix, this lift squares to the identity;
block-diagonal isometric embeddings transport compression to the lift of the compressed matrix.

`native` reindexes the construction by a qubit and the original basis, while `controlled_swap`
factors the lift through a block-diagonal matrix and a swap. For the quantum linear-algebra
background, see [NielsenChuang2010].

## Main statements

* `lift_adjoint`: Hermitian block lift of any rectangular matrix.
* `compression`: Compatibility of the lift with block compression.
* `native_controlled_swap`: Qubit-indexed controlled-swap factorization.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.HermitianLift
variable {M L R : Type*} [Fintype M] [Fintype L] [Fintype R]
variable [DecidableEq M] [DecidableEq L] [DecidableEq R]

/-- The Hermitian block matrix with zero diagonal blocks and off-diagonal blocks `A` and `Aᴴ`. -/
def lift (A : Matrix L R ℂ) : Matrix (L ⊕ R) (L ⊕ R) ℂ :=
  Matrix.fromBlocks 0 A Aᴴ 0
omit [Fintype M] [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

/-- The block lift of any rectangular complex matrix is self-adjoint. -/
theorem lift_adjoint (A : Matrix L R ℂ) : (lift A)ᴴ = lift A := by
  simp [lift, Matrix.fromBlocks_conjTranspose]
omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in

/-- The lift of a square matrix satisfying both unitary identities squares to the identity. -/
theorem lift_squared (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    lift U*lift U=1 := by
  simp [lift, Matrix.fromBlocks_multiply, hU, hU', Matrix.fromBlocks_one]
omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in

/-- For a square matrix satisfying both unitary identities, the lift satisfies `lift U` adjoint
times `lift U` equal to the identity. -/
theorem lift_unitary (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    (lift U)ᴴ*lift U=1 := by rw [lift_adjoint,lift_squared U hU hU']

/-- The block-diagonal embedding with diagonal blocks `E` and `F`. -/
def embedding (E : Matrix M L ℂ) (F : Matrix M R ℂ) : Matrix (M ⊕ M) (L ⊕ R) ℂ :=
  Matrix.fromBlocks E 0 0 F
omit [Fintype L] [Fintype R] [DecidableEq M] in

/-- If `E` and `F` have identity column Gram matrices, their block-diagonal embedding also has
identity column Gram matrix. -/
theorem embedding_gram (E : Matrix M L ℂ) (F : Matrix M R ℂ)
    (hE : Eᴴ*E=1) (hF : Fᴴ*F=1) : (embedding E F)ᴴ*embedding E F=1 := by
  simp [embedding, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hE, hF,
    Matrix.fromBlocks_one]
omit [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

/-- Compressing `lift U` by the block-diagonal embedding of `E` and `F` gives `lift (Eᴴ * U *
F)`. -/
theorem compression (U : Matrix M M ℂ) (E : Matrix M L ℂ) (F : Matrix M R ℂ) :
    (embedding E F)ᴴ*lift U*embedding E F=lift (Eᴴ*U*F) := by
  simp [embedding,lift,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_mul,Matrix.mul_assoc]
omit [Fintype M] [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

/-- The equivalence identifying a qubit-indexed basis with two disjoint copies of the original
basis. -/
def qubitSplit : Fin 2 × M ≃ M ⊕ M where
  toFun p := if p.1=0 then Sum.inl p.2 else Sum.inr p.2
  invFun x := Sum.elim (fun m => (0,m)) (fun m => (1,m)) x
  left_inv := by rintro ⟨b,x⟩;fin_cases b <;> rfl
  right_inv := by intro x;cases x <;> rfl

/-- The Hermitian lift reindexed by a qubit and the original matrix index. -/
def native (U : Matrix M M ℂ) : Matrix (Fin 2 × M) (Fin 2 × M) ℂ :=
  (lift U).submatrix qubitSplit qubitSplit
omit [Fintype M] [DecidableEq M] in

/-- The qubit-indexed lift is self-adjoint. -/
theorem native_adjoint (U : Matrix M M ℂ) : (native U)ᴴ=native U := by
  rw [native,Matrix.conjTranspose_submatrix,lift_adjoint]

/-- The qubit-indexed lift of a square matrix satisfying both unitary identities squares to the
identity. -/
theorem native_squared (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    native U*native U=1 := by
  rw [native,Matrix.submatrix_mul_equiv _ _ _ qubitSplit, lift_squared U hU hU',
    Matrix.submatrix_one_equiv]

/-- For a square matrix satisfying both unitary identities, the qubit-indexed lift has identity
adjoint-product. -/
theorem native_unitary (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    (native U)ᴴ*native U=1 := by rw [native_adjoint,native_squared U hU hU']

/-- The block-diagonal matrix with diagonal blocks `U` and `Uᴴ`. -/
def controlled (U : Matrix M M ℂ) : Matrix (M ⊕ M) (M ⊕ M) ℂ :=
  Matrix.fromBlocks U 0 0 Uᴴ
omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in

/-- Multiplying the block-diagonal matrix with blocks `U` and `Uᴴ` by the swap `lift 1` gives
`lift U`. -/
theorem controlled_swap (U : Matrix M M ℂ) : controlled U*lift (1 : Matrix M M ℂ)=lift U := by
  simp [controlled,lift,Matrix.fromBlocks_multiply]

/-- The block-diagonal embedding reindexed on its target by a qubit and the original basis. -/
def nativeEmbedding (E : Matrix M L ℂ) (F : Matrix M R ℂ) : Matrix (Fin 2 × M) (L ⊕ R) ℂ :=
  (embedding E F).submatrix qubitSplit id
omit [Fintype L] [Fintype R] [DecidableEq M] in

/-- If `E` and `F` have identity column Gram matrices, their qubit-indexed embedding also has
identity column Gram matrix. -/
theorem nativeEmbedding_gram (E : Matrix M L ℂ) (F : Matrix M R ℂ)
    (hE : Eᴴ*E=1) (hF : Fᴴ*F=1) : (nativeEmbedding E F)ᴴ*nativeEmbedding E F=1 := by
  unfold nativeEmbedding
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv _ _ _ qubitSplit,
    embedding_gram E F hE hF]
  rfl
omit [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

/-- Compressing the qubit-indexed lift through `nativeEmbedding E F` gives `lift (Eᴴ * U * F)`. -/
theorem native_compression (U : Matrix M M ℂ) (E : Matrix M L ℂ) (F : Matrix M R ℂ) :
    (nativeEmbedding E F)ᴴ*native U*nativeEmbedding E F=lift (Eᴴ*U*F) := by
  unfold nativeEmbedding native
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv _ _ _ qubitSplit,
    Matrix.submatrix_mul_equiv _ _ _ qubitSplit,compression]
  rfl

/-- After qubit reindexing, multiplying the controlled block matrix by the qubit swap gives
`native U`. -/
theorem native_controlled_swap (U : Matrix M M ℂ) :
    (controlled U).submatrix qubitSplit qubitSplit*native (1 : Matrix M M ℂ)=native U := by
  unfold native
  rw [Matrix.submatrix_mul_equiv _ _ _ qubitSplit,controlled_swap]
end Qatlib.Foundations.MatrixAlgebra.HermitianLift
