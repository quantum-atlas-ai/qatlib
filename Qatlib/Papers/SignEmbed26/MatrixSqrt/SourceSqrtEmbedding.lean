/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul

set_option backward.isDefEq.respectTransparency false

/-!
# The principal square-root sign embedding

Source: Y. Wang and J.-P. Liu, *Sign Embedding Quantum Algorithms for Matrix Equations and
Matrix Functions*, arXiv:2604.25333v2, Theorem 8.2 (Section 8.1).

For an invertible matrix `A` whose principal square root exists (`spec A ∩ (-∞, 0] = ∅`), the
source defines the augmented matrix `K(A) = !![0, A; I, 0]` and proves

`K(A)^2 = diag(A, A)`,  `spec(K(A)) ∩ iℝ = ∅`,  `sign(K(A)) = !![0, A^{1/2}; A^{-1/2}, 0]`.

The proof is the computation `sign(M) = M (M^2)^{-1/2}` of Remark 3.2 applied to `M = K(A)`:
with `(K(A)^2)^{-1/2} = diag(A^{-1/2}, A^{-1/2})` one has

`sign(K(A)) = !![0, A; I, 0] diag(A^{-1/2}, A^{-1/2}) = !![0, A A^{-1/2}; A^{-1/2}, 0]`,

and `A A^{-1/2} = A^{1/2}`.

This module formalizes that computation for an abstract square root `R` of `A` (`R * R = A`)
with two-sided inverse `Rinv`: `K(A)^2 = diag(A, A)`, the candidate `!![0, R; Rinv, 0]` is an
involution commuting with `K(A)`, it factors as `K(A) * diag(Rinv, Rinv)` exactly as in the
source, and its blocks are `R` and `Rinv`.  The spectral statement `spec(K(A)) ∩ iℝ = ∅` and the
identification of `!![0, R; Rinv, 0]` with the matrix sign are *not* formalized here; they rely on
the spectral mapping theorem for the sign and on the principal branch of the square root.
-/

namespace Qatlib.Papers.SignEmbed26.MatrixSqrt

open Matrix

set_option autoImplicit false

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The augmented matrix `K(A) = !![0, A; I, 0]` of the square-root sign embedding
(source equation (8.6)). -/
def sqrtAugmented (A : Matrix n n 𝕜) : Matrix (n ⊕ n) (n ⊕ n) 𝕜 :=
  fromBlocks 0 A 1 0

/-- The candidate signed block matrix `!![0, R; Rinv, 0]` carrying the square root `R` and its
inverse (source equation (8.7), with `R = A^{1/2}` and `Rinv = A^{-1/2}`). -/
def sqrtSignEmbedding (R Rinv : Matrix n n 𝕜) : Matrix (n ⊕ n) (n ⊕ n) 𝕜 :=
  fromBlocks 0 R Rinv 0

/-- `K(A)^2 = diag(A, A)`: the first line of the proof of Theorem 8.2. -/
theorem sqrtAugmented_mul_self (A : Matrix n n 𝕜) :
    sqrtAugmented A * sqrtAugmented A = fromBlocks A 0 0 A := by
  rw [sqrtAugmented, fromBlocks_multiply]
  simp

/-- `A A^{-1/2} = A^{1/2}`: the last step of the source computation, using `A = R^2` and
`R R^{-1} = I`. -/
theorem mul_inv_eq_of_sq (A R Rinv : Matrix n n 𝕜) (hR : R * R = A)
    (hright : R * Rinv = 1) : A * Rinv = R := by
  rw [← hR, Matrix.mul_assoc, hright, Matrix.mul_one]

/-- The inverse-sided version: `A^{-1/2} A = A^{1/2}`. -/
theorem inv_mul_eq_of_sq (A R Rinv : Matrix n n 𝕜) (hR : R * R = A)
    (hleft : Rinv * R = 1) : Rinv * A = R := by
  rw [← hR, ← Matrix.mul_assoc, hleft, Matrix.one_mul]

/-- **Theorem 8.2, factoring step.**  With `R R^{-1} = I` and `R^2 = A`, the candidate signed
block matrix factors as `sign(K(A)) = K(A) diag(A^{-1/2}, A^{-1/2})`, the identity displayed in
the source proof. -/
theorem sqrtSignEmbedding_factor (A R Rinv : Matrix n n 𝕜) (hR : R * R = A)
    (hright : R * Rinv = 1) :
    sqrtSignEmbedding R Rinv = sqrtAugmented A * fromBlocks Rinv 0 0 Rinv := by
  rw [sqrtSignEmbedding, sqrtAugmented, fromBlocks_multiply, mul_inv_eq_of_sq A R Rinv hR hright]
  simp

/-- **Theorem 8.2, involution.**  The candidate signed block matrix `!![0, R; Rinv, 0]` squares to
the identity, as the matrix sign must (Remark 3.2). -/
theorem sqrtSignEmbedding_mul_self (R Rinv : Matrix n n 𝕜) (hleft : Rinv * R = 1)
    (hright : R * Rinv = 1) :
    sqrtSignEmbedding R Rinv * sqrtSignEmbedding R Rinv = 1 := by
  rw [sqrtSignEmbedding, fromBlocks_multiply]
  rw [show (1 : Matrix (n ⊕ n) (n ⊕ n) 𝕜) = fromBlocks 1 0 0 1 from fromBlocks_one.symm]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [hleft, hright]

/-- **Theorem 8.2, commutation.**  The candidate signed block matrix commutes with `K(A)`, so it
is a sign of `K(A)` at the level of the algebraic characterization used in Section 3. -/
theorem sqrtSignEmbedding_commute (A R Rinv : Matrix n n 𝕜) (hR : R * R = A)
    (hleft : Rinv * R = 1) (hright : R * Rinv = 1) :
    sqrtSignEmbedding R Rinv * sqrtAugmented A = sqrtAugmented A * sqrtSignEmbedding R Rinv := by
  rw [sqrtSignEmbedding, sqrtAugmented, fromBlocks_multiply, fromBlocks_multiply,
    mul_inv_eq_of_sq A R Rinv hR hright, inv_mul_eq_of_sq A R Rinv hR hleft]
  simp

omit [Fintype n] [DecidableEq n] in
/-- **Theorem 8.2, block content.**  The `(1,2)` block of the signed matrix is the square root
`A^{1/2}` and the `(2,1)` block is the inverse square root `A^{-1/2}`. -/
theorem sqrtSignEmbedding_blocks (R Rinv : Matrix n n 𝕜) :
    toBlocks₁₁ (sqrtSignEmbedding R Rinv) = 0 ∧ toBlocks₁₂ (sqrtSignEmbedding R Rinv) = R ∧
      toBlocks₂₁ (sqrtSignEmbedding R Rinv) = Rinv ∧ toBlocks₂₂ (sqrtSignEmbedding R Rinv) = 0 := by
  simp [sqrtSignEmbedding]

/-- **Theorem 8.2, algebraic core.**  Combining the four statements: for a square root `R` of `A`
with two-sided inverse `Rinv`, the matrix `K(A)` squares to `diag(A, A)` and the signed block
matrix `!![0, R; Rinv, 0]` is an involution commuting with `K(A)` whose `(1,2)` and `(2,1)`
blocks are `R` and `Rinv`.  This is the content of `sign(K(A)) = !![0, A^{1/2}; A^{-1/2}, 0]`
once `sign` is identified with the signed block matrix (Remark 3.2). -/
theorem principalSqrt_signEmbedding (A R Rinv : Matrix n n 𝕜) (hR : R * R = A)
    (hleft : Rinv * R = 1) (hright : R * Rinv = 1) :
    sqrtAugmented A * sqrtAugmented A = fromBlocks A 0 0 A ∧
      sqrtSignEmbedding R Rinv * sqrtSignEmbedding R Rinv = 1 ∧
      sqrtSignEmbedding R Rinv * sqrtAugmented A = sqrtAugmented A * sqrtSignEmbedding R Rinv ∧
      sqrtSignEmbedding R Rinv = sqrtAugmented A * fromBlocks Rinv 0 0 Rinv ∧
      toBlocks₁₂ (sqrtSignEmbedding R Rinv) = R ∧
      toBlocks₂₁ (sqrtSignEmbedding R Rinv) = Rinv :=
  ⟨sqrtAugmented_mul_self A, sqrtSignEmbedding_mul_self R Rinv hleft hright,
    sqrtSignEmbedding_commute A R Rinv hR hleft hright,
    sqrtSignEmbedding_factor A R Rinv hR hright, by simp [sqrtSignEmbedding],
    by simp [sqrtSignEmbedding]⟩

end Qatlib.Papers.SignEmbed26.MatrixSqrt
