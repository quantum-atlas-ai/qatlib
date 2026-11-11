/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel
import Mathlib.Data.Matrix.Block

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.3 — reduction of the full Macaulay matrix to the Boolean Macaulay matrix

Fixed paper: arXiv:2111.00405, Lemma 5.3 on p.13.

Statement (verbatim): *Let `M̂ = [L₁ R₁; L₂ R₂]` be the Macaulay matrix for `F₁ ∪ F₂` with the
row and column ordering from Lemma 5.2.  Using row operations (and then removing some zero
rows), `M̂` can be reduced to `M̂′ = [0 B̂; I₂ B₂]` where `B̂` is the Boolean Macaulay matrix of
`F₁`, and `I₂, B₂` are as in Lemma 5.2.*

By Lemma 5.2 the `F₂` block is `I₂`, and the row operation `[[1, −L₁], [0, 1]]` zeroes the top
left block: `L₁ − L₁·I₂ = 0`, leaving `[0, R₁ − L₁R₂; I₂, R₂]`.  This final row operation is
proved below; identifying the top right block with the Boolean Macaulay matrix `B̂` of `F₁` is
the polynomial-side content of the paper's proof (rows `(m̂, fᵢ)` and `(ψ(m̂), fᵢ)` coincide
after applying `ψ`), which is not formalised here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma53

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- **Lemma 5.3** (arXiv:2111.00405, p.13): with the `F₂` block already reduced to `I₂`, the
row operation `[[1, −L₁], [0, 1]]` transforms `[L₁ R₁; I₂ R₂]` into `[0 R₁′; I₂ R₂]` with
`R₁′ = R₁ − L₁R₂`. -/
theorem lemma53_rowReduction
    {γ κ : Type*} [Fintype γ] [Fintype κ] [DecidableEq γ] [DecidableEq κ]
    {m : ℕ}
    (L1 : Matrix γ κ ℂ) (R1 : Matrix γ (Fin m) ℂ) (R2 : Matrix κ (Fin m) ℂ) :
    ∃ (U : Matrix (γ ⊕ κ) (γ ⊕ κ) ℂ) (R1' : Matrix γ (Fin m) ℂ),
      U * Matrix.fromBlocks L1 R1 (1 : Matrix κ κ ℂ) R2 =
        Matrix.fromBlocks 0 R1' (1 : Matrix κ κ ℂ) R2 := by
  refine ⟨Matrix.fromBlocks 1 (-L1) 0 1, R1 - L1 * R2, ?_⟩
  rw [Matrix.fromBlocks_multiply]
  simp [sub_eq_add_neg, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul]

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma53
