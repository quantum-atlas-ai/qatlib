/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option backward.isDefEq.respectTransparency false

/-!
# Sign embedding representation for ordinary Sylvester equations

Source: Y. Wang and J.-P. Liu, *Sign Embedding Quantum Algorithms for Matrix Equations and
Matrix Functions*, arXiv:2604.25333v2, Section 3 (Definition 3.1, Remark 3.2 and Theorem 3.3).

Theorem 3.3 (Higham's sign function identity) asserts that for the block upper triangular
augmented matrix

`M = !![A, C; 0, -B]`

with `spec A` in the open right half plane and `spec (-B)` in the open left half plane, the
matrix sign of `M` is

`sign M = !![I, 2X; 0, -I]`

where `X` is the solution of the Sylvester equation `A X + X B = C`.  The source proof has two
ingredients: `sign M` is a holomorphic function of `M` (hence commutes with `M`, is an
involution and inherits the block upper triangular shape with diagonal blocks `sign A = I` and
`sign (-B) = -I`), and comparing the `(1,2)` blocks of `M sign M` and `sign M M` gives the
equation `A Y + Y B = 2 C`.

This module formalizes exactly that algebraic content: for the *candidate* signed block matrix
`S = !![I, 2X; 0, -I]` it proves `S * S = 1`, proves that `S` commutes with `M` if and only if
`X` solves the Sylvester equation, and records the four blocks of `S`.  The identification of
`S` with the matrix sign itself (holomorphic functional calculus, Remark 3.2) is *not* part of
this module; see `SourceSylvesterUnique` for the uniqueness of `X` that the source obtains from
the half-plane separation.
-/

namespace Qatlib.Papers.SignEmbed26.SignCore

open Matrix

set_option autoImplicit false

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The augmented block upper triangular matrix `!![A, C; 0, -B]` of the Sylvester equation
`A X + X B = C`, indexed by `n ⊕ n` (source: the matrix `M` of Theorem 3.3). -/
def augmented (A C B : Matrix n n 𝕜) : Matrix (n ⊕ n) (n ⊕ n) 𝕜 :=
  fromBlocks A C 0 (-B)

/-- The candidate signed block matrix `!![I, 2X; 0, -I]` whose `(1,2)` block carries twice the
Sylvester solution (source: the right-hand side of the identity in Theorem 3.3). -/
def signEmbedding (X : Matrix n n 𝕜) : Matrix (n ⊕ n) (n ⊕ n) 𝕜 :=
  fromBlocks 1 ((2 : 𝕜) • X) 0 (-1)

/-- The signed block matrix `!![I, 2X; 0, -I]` is an involution.  This is the `sign(M)^2 = I`
half of Remark 3.2 for the candidate sign; it holds for every `X`, independently of any
Sylvester equation. -/
theorem signEmbedding_mul_self (X : Matrix n n 𝕜) :
    signEmbedding X * signEmbedding X = 1 := by
  rw [signEmbedding, fromBlocks_multiply]
  rw [show (1 : Matrix (n ⊕ n) (n ⊕ n) 𝕜) = fromBlocks 1 0 0 1 from fromBlocks_one.symm]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- Left multiplication of the augmented matrix by the signed block matrix: the `(1,2)` block is
`C - 2 • (X * B)`. -/
theorem signEmbedding_mul_augmented (A C B X : Matrix n n 𝕜) :
    signEmbedding X * augmented A C B = fromBlocks A (C - (2 : 𝕜) • (X * B)) 0 B := by
  rw [signEmbedding, augmented, fromBlocks_multiply]
  simp [sub_eq_add_neg]

/-- Right multiplication of the augmented matrix by the signed block matrix: the `(1,2)` block is
`2 • (A * X) - C`. -/
theorem augmented_mul_signEmbedding (A C B X : Matrix n n 𝕜) :
    augmented A C B * signEmbedding X = fromBlocks A ((2 : 𝕜) • (A * X) - C) 0 B := by
  rw [signEmbedding, augmented, fromBlocks_multiply]
  simp [sub_eq_add_neg]

/-- **Comparing the `(1,2)` blocks** (the last step of the proof of Theorem 3.3): the signed
block matrix `!![I, 2X; 0, -I]` commutes with the augmented matrix `!![A, C; 0, -B]` exactly
when `X` solves the Sylvester equation `A X + X B = C`.  The scalar `2` must be a nonzerodivisor,
as in the source where the field is `ℂ`. -/
theorem signEmbedding_commute_iff (A C B X : Matrix n n 𝕜) (h2 : (2 : 𝕜) ≠ 0) :
    signEmbedding X * augmented A C B = augmented A C B * signEmbedding X ↔
      A * X + X * B = C := by
  rw [signEmbedding_mul_augmented, augmented_mul_signEmbedding, fromBlocks_inj]
  have key : ∀ a b c : Matrix n n 𝕜, (c - b = a - c ↔ a + b = c + c) := by
    intro a b c
    constructor
    · intro h
      calc a + b = (a - c) + c + b := by abel
        _ = (c - b) + c + b := by rw [h]
        _ = c + c := by abel
    · intro h
      calc c - b = c + c - b - c := by abel
        _ = (a + b) - b - c := by rw [← h]
        _ = a - c := by abel
  have cancel : ∀ x y : Matrix n n 𝕜, (2 : 𝕜) • x = (2 : 𝕜) • y → x = y := by
    intro x y hxy
    have := congrArg (fun z => (2 : 𝕜)⁻¹ • z) hxy
    simpa [smul_smul, inv_mul_cancel₀ h2] using this
  have hsum : (2 : 𝕜) • (A * X) + (2 : 𝕜) • (X * B) = C + C ↔ A * X + X * B = C := by
    constructor
    · intro h
      refine cancel _ _ ?_
      calc (2 : 𝕜) • (A * X + X * B) = (2 : 𝕜) • (A * X) + (2 : 𝕜) • (X * B) :=
            smul_add (2 : 𝕜) (A * X) (X * B)
        _ = C + C := h
        _ = (2 : 𝕜) • C := (two_smul (R := 𝕜) (x := C)).symm
    · intro h
      rw [← smul_add, h, two_smul]
  constructor
  · rintro ⟨-, h, -, -⟩
    exact hsum.mp ((key _ _ _).mp h)
  · intro h
    exact ⟨rfl, (key _ _ _).mpr (hsum.mpr h), rfl, rfl⟩

/-- **Theorem 3.3, algebraic core.**  Under the Sylvester equation `A X + X B = C`, the signed
block matrix `S = !![I, 2X; 0, -I]` satisfies `S * S = 1`, commutes with `M = !![A, C; 0, -B]`,
and has blocks `S₁₁ = I`, `S₁₂ = 2X`, `S₂₁ = 0`, `S₂₂ = -I`.  These are the three properties of
`sign M` that the source proof transfers from the holomorphic functional calculus to the
augmented matrix, with the `(1,2)` block carrying twice the Sylvester solution. -/
theorem higham_sign_identity (A C B X : Matrix n n 𝕜) (h2 : (2 : 𝕜) ≠ 0)
    (hX : A * X + X * B = C) :
    signEmbedding X * signEmbedding X = 1 ∧
      signEmbedding X * augmented A C B = augmented A C B * signEmbedding X ∧
      toBlocks₁₁ (signEmbedding X) = 1 ∧ toBlocks₁₂ (signEmbedding X) = (2 : 𝕜) • X ∧
      toBlocks₂₁ (signEmbedding X) = 0 ∧ toBlocks₂₂ (signEmbedding X) = -1 := by
  refine ⟨signEmbedding_mul_self X, (signEmbedding_commute_iff A C B X h2).mpr hX, ?_, ?_, ?_, ?_⟩
  · simp [signEmbedding]
  · simp [signEmbedding]
  · simp [signEmbedding]
  · simp [signEmbedding]

end Qatlib.Papers.SignEmbed26.SignCore
