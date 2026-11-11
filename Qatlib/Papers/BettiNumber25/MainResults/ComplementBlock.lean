/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Block

set_option backward.isDefEq.respectTransparency false

/-! Complement block encoding for
"Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes" (arXiv:2408.16934v3, 2025).

Theorem 6.1 of the paper: given a circuit `U_{P_Γ}` block-encoding the
projector `P_Γ` onto the simplex family `Γ`, the circuit applying
`U_{P_Γ}`, a multi-controlled `X` on the ancilla, and `U_{P_Γ}†`
block-encodes the complementary projector `I − P_Γ`.

The circuit semantics (multi-controlled gates, ancilla workspace) are
abstracted to the block-matrix level: for a projector `P` (`P² = P`,
`P† = P`), the Szegedy walk `Q = [[P, 1−P], [1−P, −P]]` is unitary
with top-left block `P`, and composing with the ancilla flip
`X = [[0,1],[1,0]]` produces a unitary with top-left block `1 − P`,
i.e. a block encoding of `I − P` with normalization `1` and error `0`.

- `flagProj` instantiates the projector diagonally (simplex in `Γ` or
  not), matching the paper's computational-basis action.
- `projWalk_unitary` proves `Q * Q = 1` for any projector.
- `flip_mul_projWalk` and `flip_projWalk_top_left` show the flipped
  product has top-left block `1 − P`.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.BettiNumber25.MainResults.ComplementBlock

open scoped Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The diagonal projector onto the flag set `s` (`s i = true` marks a
simplex in `Γ`): it sends a computational basis state to itself if
flagged, and to `0` otherwise. -/
def flagProj (s : n → Bool) : Matrix n n ℂ :=
  Matrix.diagonal fun i => if s i then (1 : ℂ) else 0

/-- **Projector property of `flagProj`**: `P² = P`. -/
theorem flagProj_idem (s : n → Bool) : flagProj s * flagProj s = flagProj s := by
  rw [flagProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : s i <;> simp [h]

omit [Fintype n] in
/-- **Hermiticity of `flagProj`**: `P† = P`. -/
theorem flagProj_hermitian (s : n → Bool) : (flagProj s)ᴴ = flagProj s := by
  ext i j
  simp only [flagProj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : s j <;> by_cases h2 : i = j <;> simp [h, h2, ne_comm]

/-- The Szegedy walk of an operator `P`: the block matrix
`Q = [[P, 1−P], [1−P, −P]]`, unitary exactly when `P` is a projector. -/
def projWalk (P : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks P (1 - P) (1 - P) (-P)

/-- The ancilla flip `X = [[0,1],[1,0]]` acting on the block index. -/
def ancillaFlip : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 1 1 0

/-- **Theorem 6.1, unitarity core**: for a projector `P` (`P² = P`,
`P† = P`), the Szegedy walk `Q = [[P, 1−P], [1−P, −P]]` is unitary
(`Q * Q = 1`), so it block-encodes `P` in its top-left block with
normalization `1` and error `0`. -/
theorem projWalk_unitary (P : Matrix n n ℂ) (hI : P * P = P) (_hH : Pᴴ = P) :
    projWalk P * projWalk P = 1 := by
  have e1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hI, sub_self]
  have e2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hI, sub_self]
  have e3 : (1 - P) * (1 - P) = 1 - P := by
    calc (1 - P) * (1 - P) = 1 * (1 - P) - P * (1 - P) := by rw [sub_mul]
      _ = 1 * 1 - 1 * P - (P * 1 - P * P) := by rw [mul_sub, mul_sub]
      _ = 1 - P - (P - P * P) := by rw [one_mul, one_mul, mul_one]
      _ = 1 - P - (P - P) := by rw [hI]
      _ = 1 - P := by simp
  have e4 : (1 - P) * -P = 0 := by rw [mul_neg, e2, neg_zero]
  have e5 : -P * (1 - P) = 0 := by rw [neg_mul, e1, neg_zero]
  have e6 : -P * -P = P := by rw [neg_mul_neg, hI]
  rw [projWalk, Matrix.fromBlocks_multiply, e1, e2, e3, e4, e5, e6, hI]
  simp [Matrix.fromBlocks_one]

/-- **Theorem 6.1, complement block**: composing the Szegedy walk with
the ancilla flip yields the block matrix
`[[1−P, −P], [P, 1−P]]` — a unitary whose top-left block is `1 − P`,
i.e. a block encoding of the complementary projector `I − P_Γ`. -/
theorem flip_mul_projWalk (P : Matrix n n ℂ) :
    ancillaFlip * projWalk P = Matrix.fromBlocks (1 - P) (-P) P (1 - P) := by
  rw [ancillaFlip, projWalk, Matrix.fromBlocks_multiply]
  simp

/-- **Theorem 6.1, top-left entry**: the flipped walk has top-left
block `1 − P`, the complementary projector. -/
theorem flip_projWalk_top_left (P : Matrix n n ℂ) (i j : n) :
    ((ancillaFlip * projWalk P : Matrix (n ⊕ n) (n ⊕ n) ℂ)) (Sum.inl i) (Sum.inl j)
      = (1 - P) i j := by
  rw [flip_mul_projWalk]
  simp [Matrix.fromBlocks]

end Qatlib.Papers.BettiNumber25.MainResults.ComplementBlock
