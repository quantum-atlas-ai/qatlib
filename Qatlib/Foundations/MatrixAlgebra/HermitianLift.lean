/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.HermitianLift
variable {M L R : Type*} [Fintype M] [Fintype L] [Fintype R]
variable [DecidableEq M] [DecidableEq L] [DecidableEq R]

def lift (A : Matrix L R ℂ) : Matrix (L ⊕ R) (L ⊕ R) ℂ :=
  Matrix.fromBlocks 0 A Aᴴ 0
omit [Fintype M] [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

theorem lift_adjoint (A : Matrix L R ℂ) : (lift A)ᴴ = lift A := by
  simp [lift, Matrix.fromBlocks_conjTranspose]
omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in

theorem lift_squared (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    lift U*lift U=1 := by
  simp [lift, Matrix.fromBlocks_multiply, hU, hU', Matrix.fromBlocks_one]
omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in

theorem lift_unitary (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    (lift U)ᴴ*lift U=1 := by rw [lift_adjoint,lift_squared U hU hU']

def embedding (E : Matrix M L ℂ) (F : Matrix M R ℂ) : Matrix (M ⊕ M) (L ⊕ R) ℂ :=
  Matrix.fromBlocks E 0 0 F
omit [Fintype L] [Fintype R] [DecidableEq M] in

theorem embedding_gram (E : Matrix M L ℂ) (F : Matrix M R ℂ)
    (hE : Eᴴ*E=1) (hF : Fᴴ*F=1) : (embedding E F)ᴴ*embedding E F=1 := by
  simp [embedding, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hE, hF,
    Matrix.fromBlocks_one]
omit [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

theorem compression (U : Matrix M M ℂ) (E : Matrix M L ℂ) (F : Matrix M R ℂ) :
    (embedding E F)ᴴ*lift U*embedding E F=lift (Eᴴ*U*F) := by
  simp [embedding,lift,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_mul,Matrix.mul_assoc]
omit [Fintype M] [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

def qubitSplit : Fin 2 × M ≃ M ⊕ M where
  toFun p := if p.1=0 then Sum.inl p.2 else Sum.inr p.2
  invFun x := Sum.elim (fun m => (0,m)) (fun m => (1,m)) x
  left_inv := by rintro ⟨b,x⟩;fin_cases b <;> rfl
  right_inv := by intro x;cases x <;> rfl

def native (U : Matrix M M ℂ) : Matrix (Fin 2 × M) (Fin 2 × M) ℂ :=
  (lift U).submatrix qubitSplit qubitSplit
omit [Fintype M] [DecidableEq M] in

theorem native_adjoint (U : Matrix M M ℂ) : (native U)ᴴ=native U := by
  rw [native,Matrix.conjTranspose_submatrix,lift_adjoint]

theorem native_squared (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    native U*native U=1 := by
  rw [native,Matrix.submatrix_mul_equiv _ _ _ qubitSplit, lift_squared U hU hU',
    Matrix.submatrix_one_equiv]

theorem native_unitary (U : Matrix M M ℂ) (hU : Uᴴ*U=1) (hU' : U*Uᴴ=1) :
    (native U)ᴴ*native U=1 := by rw [native_adjoint,native_squared U hU hU']

def controlled (U : Matrix M M ℂ) : Matrix (M ⊕ M) (M ⊕ M) ℂ :=
  Matrix.fromBlocks U 0 0 Uᴴ
omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in

theorem controlled_swap (U : Matrix M M ℂ) : controlled U*lift (1 : Matrix M M ℂ)=lift U := by
  simp [controlled,lift,Matrix.fromBlocks_multiply]

def nativeEmbedding (E : Matrix M L ℂ) (F : Matrix M R ℂ) : Matrix (Fin 2 × M) (L ⊕ R) ℂ :=
  (embedding E F).submatrix qubitSplit id
omit [Fintype L] [Fintype R] [DecidableEq M] in

theorem nativeEmbedding_gram (E : Matrix M L ℂ) (F : Matrix M R ℂ)
    (hE : Eᴴ*E=1) (hF : Fᴴ*F=1) : (nativeEmbedding E F)ᴴ*nativeEmbedding E F=1 := by
  unfold nativeEmbedding
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv _ _ _ qubitSplit,
    embedding_gram E F hE hF]
  rfl
omit [Fintype L] [Fintype R] [DecidableEq M] [DecidableEq L] [DecidableEq R] in

theorem native_compression (U : Matrix M M ℂ) (E : Matrix M L ℂ) (F : Matrix M R ℂ) :
    (nativeEmbedding E F)ᴴ*native U*nativeEmbedding E F=lift (Eᴴ*U*F) := by
  unfold nativeEmbedding native
  rw [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv _ _ _ qubitSplit,
    Matrix.submatrix_mul_equiv _ _ _ qubitSplit,compression]
  rfl

theorem native_controlled_swap (U : Matrix M M ℂ) :
    (controlled U).submatrix qubitSplit qubitSplit*native (1 : Matrix M M ℂ)=native U := by
  unfold native
  rw [Matrix.submatrix_mul_equiv _ _ _ qubitSplit,controlled_swap]
end Qatlib.Foundations.MatrixAlgebra.HermitianLift
