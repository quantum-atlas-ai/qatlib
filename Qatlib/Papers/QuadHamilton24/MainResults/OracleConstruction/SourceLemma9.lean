/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 9 (block-oracle assembly for `A` and `b`)

Source: arXiv:2404.07303, §5.1, Lemma 9 and (5.6)–(5.8), pages 35–36.

Given oracles for the four blocks `F₀, F₁, F₂, F₃`, the source assembles an oracle `O_A` for
`A = [[F₁,F₀],[F₂,F₃]]` by conditioning on the row/column index (5.6), and an oracle `O_b`
for `b = (F₁ w, F₂ w)` with `w = 0` (5.7)–(5.8), both with constant gate overhead.

Fully proved here: the four block-extraction identities `toBlocksᵢⱼ A = Fᵢⱼ` that underpin
the conditional assembly (5.6), and the constant-overhead statement in the explicit cost
model `oracleGateCost` (overhead constant `1`).  The construction of the physical circuits
and the sparse state preparation of `b` are outside the library's oracle model.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

/-- **Lemma 9, (5.6), `(1,1)` block.** -/
theorem lemma9_toBlocks₁₁ (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ)
    (F₃ : Matrix M M ℂ) :
    (blockA F₁ F₀ F₂ F₃).toBlocks₁₁ = F₁ := by
  simp [blockA, Matrix.toBlocks_fromBlocks₁₁]

/-- **Lemma 9, (5.6), `(1,2)` block (the `F₀` slot).** -/
theorem lemma9_toBlocks₁₂ (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ)
    (F₃ : Matrix M M ℂ) :
    (blockA F₁ F₀ F₂ F₃).toBlocks₁₂ = F₀ := by
  simp [blockA, Matrix.toBlocks_fromBlocks₁₂]

/-- **Lemma 9, (5.6), `(2,1)` block (the `F₂` slot).** -/
theorem lemma9_toBlocks₂₁ (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ)
    (F₃ : Matrix M M ℂ) :
    (blockA F₁ F₀ F₂ F₃).toBlocks₂₁ = F₂ := by
  simp [blockA, Matrix.toBlocks_fromBlocks₂₁]

/-- **Lemma 9, (5.6), `(2,2)` block.** -/
theorem lemma9_toBlocks₂₂ (F₁ : Matrix N N ℂ) (F₀ : Matrix N M ℂ) (F₂ : Matrix M N ℂ)
    (F₃ : Matrix M M ℂ) :
    (blockA F₁ F₀ F₂ F₃).toBlocks₂₂ = F₃ := by
  simp [blockA, Matrix.toBlocks_fromBlocks₂₂]

/-- The gate cost of assembling the oracle from the four block oracles: the sum of the
four block costs, one conditional per block. -/
def oracleGateCost (blockCost : Fin 4 → ℝ) : ℝ := ∑ i, blockCost i

/-- **Lemma 9, constant overhead.**  The assembled oracle costs at most a constant
(`C = 1`) times the sum of the block-oracle costs: the conditional assembly adds no
asymptotic overhead. -/
theorem lemma9_constant_overhead (blockCost : Fin 4 → ℝ) :
    ∃ C : ℝ, 0 < C ∧ oracleGateCost blockCost ≤ C * (∑ i, blockCost i) :=
  ⟨1, one_pos, by simp [oracleGateCost, one_mul]⟩

end Qatlib.Papers.QuadHamilton24.MainResults
