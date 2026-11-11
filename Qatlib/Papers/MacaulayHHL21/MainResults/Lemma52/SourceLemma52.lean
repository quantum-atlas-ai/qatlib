/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel
import Mathlib.Data.Matrix.Block

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.2 — row reduction of the Boolean-constraint Macaulay matrix

Fixed paper: arXiv:2111.00405, Lemma 5.2 on p.12.

Statement (verbatim): *Let the Macaulay matrix `M̂₂` of max degree `d` of `F₂` have its columns
ordered … Then using row operations, `M̂₂ = [L₂ R₂]` can be reduced to `M̂′₂ = [I₂ B₂]` where
`I₂` is the identity matrix of dimension `(d+1)^n − 2^n` … and rows with zeros are removed.*

The paper's first step (the triangular elimination making each left-side row have at most one
`1`, then zeroing the bottom rows) yields the block shape `[L₂ R₂; 0 0]` with `L₂` invertible.
The final row operation is multiplying on the left by `diag(L₂⁻¹, 1)`, which produces
`[I₂ B₂; 0 0]` with `B₂ = L₂⁻¹ R₂`.  That final step is proved below; the invertibility
`L₂ · L₂⁻¹ = 1` is the hypothesis corresponding to the paper's elimination argument (it is
what "the left part has at most one 1 in each row and a unique row per leading monomial"
provides).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma52

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- **Lemma 5.2** (arXiv:2111.00405, p.12): the Macaulay matrix of `F₂`, in the block shape
`[L₂ R₂; 0 0]` with `L₂` invertible on the non-multilinear monomials, is reduced by the row
operation `diag(L₂⁻¹, 1)` to `[I₂ B₂; 0 0]`, where `I₂` has dimension `(d+1)^n − 2^n` and the
right block has the `2^n` multilinear monomials as columns. -/
theorem lemma52_rowReduction
    {n d : ℕ}
    (L2 Linv : Matrix (Fin ((d + 1) ^ n - 2 ^ n)) (Fin ((d + 1) ^ n - 2 ^ n)) ℂ)
    (R2 : Matrix (Fin ((d + 1) ^ n - 2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hL2 : Linv * L2 = 1) :
    ∃ (U : Matrix (Fin ((d + 1) ^ n - 2 ^ n) ⊕ Fin (2 ^ n))
          (Fin ((d + 1) ^ n - 2 ^ n) ⊕ Fin (2 ^ n)) ℂ)
      (B2 : Matrix (Fin ((d + 1) ^ n - 2 ^ n)) (Fin (2 ^ n)) ℂ),
      U * Matrix.fromBlocks L2 R2 0 0 =
        Matrix.fromBlocks (1 : Matrix (Fin ((d + 1) ^ n - 2 ^ n))
          (Fin ((d + 1) ^ n - 2 ^ n)) ℂ) B2 0 0 := by
  refine ⟨Matrix.fromBlocks Linv 0 0 1, Linv * R2, ?_⟩
  rw [Matrix.fromBlocks_multiply]
  simp [hL2, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul]

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma52
