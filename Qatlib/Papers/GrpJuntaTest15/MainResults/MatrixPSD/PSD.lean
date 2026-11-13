/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

set_option backward.isDefEq.respectTransparency false

/-!
# Positive semidefiniteness closure properties (Proposition A.1)

Fixed source: arXiv:1507.03126v1, *Efficient Quantum Algorithms for (Gapped) Group
Testing and Junta Testing*, Appendix A, page 39.

Claim c025 (Proposition A.1): if `A` and `B` are positive semidefinite matrices of
the same size, then so are

(a) the matrix obtained from `A` by simultaneously duplicating one row and the same
    column;
(b) the Hadamard (entry-wise) product `A ∘ B`.

Both are proved from Mathlib: (a) a duplicated matrix is `A.submatrix f f` for the
non-injective index map `f` that hits the duplicated index twice, and positive
semidefiniteness is closed under `submatrix` (`Matrix.PosSemidef.submatrix`);
(b) is the Schur product theorem `Matrix.PosSemidef.hadamard`.  The matrices in the
adversary bound are complex, so the statements are over `ℂ`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix ComplexOrder

namespace Qatlib.Papers.GrpJuntaTest15.MainResults.MatrixPSD

/-- Index map duplicating `k : Fin n`: indices `≤ k` keep their value, indices
`> k` are shifted down by one.  In particular `k.castSucc` and `k.succ` both map
to `k`, so `dupIndex k` duplicates the row/column `k`. -/
def dupIndex {n : ℕ} (k : Fin n) : Fin (n + 1) → Fin n :=
  fun i => if h : i.val ≤ k.val then ⟨i.val, Nat.lt_of_le_of_lt h k.isLt⟩
           else ⟨i.val - 1, by omega⟩

/-- The first copy of the duplicated index `k` is `k.castSucc`. -/
theorem dupIndex_castSucc {n : ℕ} (k : Fin n) : dupIndex k k.castSucc = k := by
  ext
  simp [dupIndex]

/-- The second copy of the duplicated index `k` is `k.succ`. -/
theorem dupIndex_succ {n : ℕ} (k : Fin n) : dupIndex k k.succ = k := by
  ext
  simp [dupIndex]

/-- c025 (a), Proposition A.1 (a) (arXiv:1507.03126v1, p. 39): duplicating one row
and the same column of a positive semidefinite matrix `A` (here the row/column
`k`) yields a positive semidefinite matrix.  This is
`Matrix.PosSemidef.submatrix` applied to the duplicating index map `dupIndex k`. -/
theorem propositionA_1_a_duplicate_row_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (k : Fin n) :
    (A.submatrix (dupIndex k) (dupIndex k)).PosSemidef :=
  hA.submatrix (dupIndex k)

/-- c025 (b), Proposition A.1 (b) (arXiv:1507.03126v1, p. 39): the Hadamard
(entry-wise) product of two positive semidefinite matrices of the same size is
positive semidefinite (Schur product theorem, `Matrix.PosSemidef.hadamard`). -/
theorem propositionA_1_b_hadamard {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊙ B).PosSemidef :=
  hA.hadamard hB

end Qatlib.Papers.GrpJuntaTest15.MainResults.MatrixPSD
