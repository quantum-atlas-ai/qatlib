/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Separable

@[expose] public section




/-!
# Operators with a qubit reference: block calculus

Elementary lemmas about `qubitBlocks A B C D`, the operator on `ℂ² ⊗ ℂ^n` with blocks
`[[A, B], [C, D]]`: entries, blocks, linearity, compatibility with `refMap`, partial
transposition, conjugate transposition, and the comparison with `Matrix.fromBlocks`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n p : Type*}

/-! ### Entries and blocks -/

/-- Establishes `qubitBlocks_apply_zero_zero`: `qubitBlocks A B C D (0, a) (0, b) = A a b`, for the stated parameters. -/
@[simp]
theorem qubitBlocks_apply_zero_zero (A B C D : Matrix n n ℂ) (a b : n) :
    qubitBlocks A B C D (0, a) (0, b) = A a b :=
  rfl

/-- Establishes `qubitBlocks_apply_zero_one`: `qubitBlocks A B C D (0, a) (1, b) = B a b`, for the stated parameters. -/
@[simp]
theorem qubitBlocks_apply_zero_one (A B C D : Matrix n n ℂ) (a b : n) :
    qubitBlocks A B C D (0, a) (1, b) = B a b :=
  rfl

/-- Establishes `qubitBlocks_apply_one_zero`: `qubitBlocks A B C D (1, a) (0, b) = C a b`, for the stated parameters. -/
@[simp]
theorem qubitBlocks_apply_one_zero (A B C D : Matrix n n ℂ) (a b : n) :
    qubitBlocks A B C D (1, a) (0, b) = C a b :=
  rfl

/-- Establishes `qubitBlocks_apply_one_one`: `qubitBlocks A B C D (1, a) (1, b) = D a b`, for the stated parameters. -/
@[simp]
theorem qubitBlocks_apply_one_one (A B C D : Matrix n n ℂ) (a b : n) :
    qubitBlocks A B C D (1, a) (1, b) = D a b :=
  rfl

/-- Establishes `block_qubitBlocks_zero_zero`: `block (qubitBlocks A B C D) 0 0 = A`, for the stated parameters. -/
@[simp]
theorem block_qubitBlocks_zero_zero (A B C D : Matrix n n ℂ) :
    block (qubitBlocks A B C D) 0 0 = A :=
  rfl

/-- Establishes `block_qubitBlocks_zero_one`: `block (qubitBlocks A B C D) 0 1 = B`, for the stated parameters. -/
@[simp]
theorem block_qubitBlocks_zero_one (A B C D : Matrix n n ℂ) :
    block (qubitBlocks A B C D) 0 1 = B :=
  rfl

/-- Establishes `block_qubitBlocks_one_zero`: `block (qubitBlocks A B C D) 1 0 = C`, for the stated parameters. -/
@[simp]
theorem block_qubitBlocks_one_zero (A B C D : Matrix n n ℂ) :
    block (qubitBlocks A B C D) 1 0 = C :=
  rfl

/-- Establishes `block_qubitBlocks_one_one`: `block (qubitBlocks A B C D) 1 1 = D`, for the stated parameters. -/
@[simp]
theorem block_qubitBlocks_one_one (A B C D : Matrix n n ℂ) :
    block (qubitBlocks A B C D) 1 1 = D :=
  rfl

/-- Every operator with a qubit reference is determined by its four blocks. -/
theorem qubitBlocks_block (X : Matrix (Fin 2 × n) (Fin 2 × n) ℂ) :
    qubitBlocks (block X 0 0) (block X 0 1) (block X 1 0) (block X 1 1) = X := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-! ### Linearity -/

/-- Establishes `qubitBlocks_zero`: `qubitBlocks (0 : Matrix n n ℂ) 0 0 0 = 0`, for the stated parameters. -/
theorem qubitBlocks_zero : qubitBlocks (0 : Matrix n n ℂ) 0 0 0 = 0 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `qubitBlocks_add`: `qubitBlocks (A + A') (B + B') (C + C') (D + D') = qubitBlocks A B C D + qubitBlocks A' B' C' D'`, for the stated parameters. -/
theorem qubitBlocks_add (A B C D A' B' C' D' : Matrix n n ℂ) :
    qubitBlocks (A + A') (B + B') (C + C') (D + D') =
      qubitBlocks A B C D + qubitBlocks A' B' C' D' := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `qubitBlocks_smul`: `qubitBlocks (c • A) (c • B) (c • C) (c • D) = c • qubitBlocks A B C D`, for the stated parameters. -/
theorem qubitBlocks_smul (c : ℂ) (A B C D : Matrix n n ℂ) :
    qubitBlocks (c • A) (c • B) (c • C) (c • D) = c • qubitBlocks A B C D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `qubitBlocks_sum`: `qubitBlocks (∑ k ∈ s, A k) (∑ k ∈ s, B k) (∑ k ∈ s, C k) (∑ k ∈ s, D k) = ∑ k ∈ s, qubitBlocks (A k) (B k) (C k) (D k)`, for the stated parameters. -/
theorem qubitBlocks_sum {ι : Type*} (s : Finset ι) (A B C D : ι → Matrix n n ℂ) :
    qubitBlocks (∑ k ∈ s, A k) (∑ k ∈ s, B k) (∑ k ∈ s, C k) (∑ k ∈ s, D k) =
      ∑ k ∈ s, qubitBlocks (A k) (B k) (C k) (D k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qubitBlocks_zero]
  | insert a s ha ih => simp only [Finset.sum_insert ha, qubitBlocks_add, ih]

/-! ### Kronecker products, `refMap`, transposes -/

/-- A product operator with a qubit reference, in block form. -/
theorem kronecker_eq_qubitBlocks (r : Matrix (Fin 2) (Fin 2) ℂ) (Q : Matrix n n ℂ) :
    r ⊗ₖ Q = qubitBlocks (r 0 0 • Q) (r 0 1 • Q) (r 1 0 • Q) (r 1 1 • Q) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `refMap_qubitBlocks`: `refMap (Fin 2) Φ (qubitBlocks A B C D) = qubitBlocks (Φ A) (Φ B) (Φ C) (Φ D)`, for the stated parameters. -/
theorem refMap_qubitBlocks (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) (A B C D : Matrix n n ℂ) :
    refMap (Fin 2) Φ (qubitBlocks A B C D) = qubitBlocks (Φ A) (Φ B) (Φ C) (Φ D) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Partial transposition on the qubit swaps the off-diagonal blocks. -/
theorem partialTransposeRef_qubitBlocks (A B C D : Matrix n n ℂ) :
    partialTransposeRef (qubitBlocks A B C D) = qubitBlocks A C B D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Establishes `conjTranspose_qubitBlocks`: `(qubitBlocks A B C D)ᴴ = qubitBlocks Aᴴ Cᴴ Bᴴ Dᴴ`, for the stated parameters. -/
theorem conjTranspose_qubitBlocks (A B C D : Matrix n n ℂ) :
    (qubitBlocks A B C D)ᴴ = qubitBlocks Aᴴ Cᴴ Bᴴ Dᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Exchanging the two reference basis states exchanges the blocks. -/
theorem qubitBlocks_submatrix_swap (A B C D : Matrix n n ℂ) :
    (qubitBlocks A B C D).submatrix
        (fun x : Fin 2 × n => ((![1, 0] : Fin 2 → Fin 2) x.1, x.2))
        (fun x : Fin 2 × n => ((![1, 0] : Fin 2 → Fin 2) x.1, x.2)) =
      qubitBlocks D C B A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-! ### Comparison with `Matrix.fromBlocks` -/

/-- Establishes `qubitBlocks_submatrix_sum`: `(qubitBlocks A B C D).submatrix (Sum.elim (fun a : n => ((0 : Fin 2), a)) (fun a : n => ((1 : Fin 2), a))) (Sum.elim (fun a : n => ((0 : Fin 2), a)) (fun a : n => ((1 : Fin 2), a))) = Matrix.fromBlocks A B C D`, for the stated parameters. -/
theorem qubitBlocks_submatrix_sum (A B C D : Matrix n n ℂ) :
    (qubitBlocks A B C D).submatrix
        (Sum.elim (fun a : n => ((0 : Fin 2), a)) (fun a : n => ((1 : Fin 2), a)))
        (Sum.elim (fun a : n => ((0 : Fin 2), a)) (fun a : n => ((1 : Fin 2), a))) =
      Matrix.fromBlocks A B C D := by
  ext (a | a) (b | b) <;> rfl

/-- Establishes `fromBlocks_submatrix_qubit`: `(Matrix.fromBlocks A B C D).submatrix (fun x : Fin 2 × n => (![Sum.inl x.2, Sum.inr x.2] : Fin 2 → n ⊕ n) x.1) (fun x : Fin 2 × n => (![Sum.inl x.2, Sum.inr x.2] : Fin 2 → n ⊕ n) x.1) = qubitBlocks A B C D`, for the stated parameters. -/
theorem fromBlocks_submatrix_qubit (A B C D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).submatrix
        (fun x : Fin 2 × n => (![Sum.inl x.2, Sum.inr x.2] : Fin 2 → n ⊕ n) x.1)
        (fun x : Fin 2 × n => (![Sum.inl x.2, Sum.inr x.2] : Fin 2 → n ⊕ n) x.1) =
      qubitBlocks A B C D := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;> rfl

/-- Positivity of a qubit-reference block operator is positivity of the block matrix. -/
theorem posSemidef_qubitBlocks_iff {A B C D : Matrix n n ℂ} :
    (qubitBlocks A B C D).PosSemidef ↔ (Matrix.fromBlocks A B C D).PosSemidef := by
  constructor
  · intro h
    have h' := h.submatrix
      (Sum.elim (fun a : n => ((0 : Fin 2), a)) (fun a : n => ((1 : Fin 2), a)))
    rwa [qubitBlocks_submatrix_sum] at h'
  · intro h
    have h' := h.submatrix
      (fun x : Fin 2 × n => (![Sum.inl x.2, Sum.inr x.2] : Fin 2 → n ⊕ n) x.1)
    rwa [fromBlocks_submatrix_qubit] at h'

/-- Gram matrices of column selections. -/
theorem conjTranspose_submatrix_mul_submatrix {r m k l : Type*} [Fintype r] (A : Matrix r m ℂ)
    (f : k → m) (g : l → m) :
    (A.submatrix id f)ᴴ * A.submatrix id g = (Aᴴ * A).submatrix f g := by
  ext a b
  simp [Matrix.mul_apply]

end Qatlib.Foundations.PPTMatrix.OperatorCones
