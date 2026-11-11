/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseUnitary09.MainResults.Model.SourceSparseUnitaryModel
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

set_option backward.isDefEq.respectTransparency false

/-!
# SparseUnitary09 — MainResults / Model / SparseModelGates (claim c002)

Source: Stephen P. Jordan & Pawel Wocjan, *Efficient quantum circuits for arbitrary
sparse unitaries*, fixed version **arXiv:0904.2211v2 (11 Feb 2010)**.

Claim **c002** (Sec. II, p. 3, line 57: "the sparse unitary model is equivalent to
BQP") has two substantive, formalisable mathematical legs, which this file supplies
on top of the model-level equivalence already proved in `SourceSparseUnitaryModel`:

* **BQP gates lie in the sparse model with *bounded* sparsity.**  The elementary gates
  of BQP are `1`- and `2`-qubit gates.  Concretely a `2`-qubit gate on a register is a
  `4`-sparse matrix (`dense_rowSparse`/`dense_colSparse` at `d = 4`), and extending a
  `d`-sparse gate to a larger register by tensoring with the identity *preserves* the
  bound `d` (`kronecker_one_rowSparse`, `kronecker_one_colSparse`,
  `kronecker_one_mem_unitary`).  Thus `localGate_sparseStepBounded` and
  `twoQubitGate_sparseStepBounded` show that the `k`-step gate model's single steps are
  sparse steps with a *constant* bound (2 or 4), not merely `d = N`.  This is exactly
  the paper's "BQP ⊆ sparse" argument.

* **Sparse steps are efficiently implementable with a sparse Hamiltonian.**  For any
  `d`-sparse unitary `U`, its Hermitian dilation `H = [[0,U],[U†,0]]` is again
  `d`-sparse (`unitaryDilation_sparse`), Hermitian with `H² = 1`
  (`sparseStep_dilation_implements`), and phase-kickback for time `π/2` implements
  `U` up to a global phase on the ancilla-`|1⟩` sector.  Since `H` is `d`-sparse, its
  time-`π/2` evolution obeys the poly `(log N, d, ‖Ht‖, 1/ε)` gate cost of sparse
  Hamiltonian simulation — the paper's "sparse ⊆ BQP" argument, reduced to the c001
  dilation of `SourceSparseDilation`.

The literal identification with the *decision class* BQP (uniform families with bounded
error) is not available in this library and is documented rather than re-derived; the
two directions above are the formalisable mathematical content of the equivalence.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators Kronecker

namespace Qatlib.Papers.SparseUnitary09.MainResults.Model

open Qatlib.Papers.SparseUnitary09.MainResults.Dilation

/-! ## Register extension: sparsity of Kronecker products

A gate on a subsystem is extended to the full register by the Kronecker product with the
identity on the untouced wires.  These lemmas show that this extension preserves — and in
general multiplies — the row/column sparsity bound. -/

/-- The identity matrix is `1`-row-sparse. -/
theorem one_rowSparse {n : Type*} [Fintype n] [DecidableEq n] :
    RowSparse (1 : Matrix n n ℂ) 1 := by
  intro i
  refine ⟨{i}, by simp, fun j hj => ?_⟩
  simp only [Matrix.one_apply] at hj
  by_cases h : i = j
  · exact Finset.mem_singleton.mpr h.symm
  · simp [h] at hj

/-- The identity matrix is `1`-column-sparse. -/
theorem one_colSparse {n : Type*} [Fintype n] [DecidableEq n] :
    ColSparse (1 : Matrix n n ℂ) 1 := by
  intro j
  refine ⟨{j}, by simp, fun i hi => ?_⟩
  simp only [Matrix.one_apply] at hi
  by_cases h : i = j
  · exact Finset.mem_singleton.mpr h
  · simp [h] at hi

/-- arXiv:0904.2211v2, p. 1 (efficiency of the dilation): the Kronecker product of a
`dA`-row-sparse matrix with a `dB`-row-sparse matrix is `dA·dB`-row-sparse.  A nonzero
entry `(A ⊗ₖ B) (i₁,i₂) (j₁,j₂) = A i₁ j₁ · B i₂ j₂` forces both factors nonzero, so the
nonzero columns in row `(i₁,i₂)` lie in the product `sA i₁ ×ˢ sB i₂`. -/
theorem kronecker_rowSparse {l m n p : Type*} [Fintype m] [Fintype p]
    (A : Matrix l m ℂ) (B : Matrix n p ℂ) (dA dB : ℕ)
    (hA : RowSparse A dA) (hB : RowSparse B dB) :
    RowSparse (A ⊗ₖ B) (dA * dB) := by
  intro i
  obtain ⟨sa, hsa, hca⟩ := hA i.1
  obtain ⟨sb, hsb, hcb⟩ := hB i.2
  refine ⟨sa ×ˢ sb, ?_, fun j hj => ?_⟩
  · rw [Finset.card_product]; exact Nat.mul_le_mul hsa hsb
  · simp only [Matrix.kroneckerMap_apply] at hj
    have h1 : A i.1 j.1 ≠ 0 := fun h => hj (by rw [h, zero_mul])
    have h2 : B i.2 j.2 ≠ 0 := fun h => hj (by rw [h, mul_zero])
    exact Finset.mem_product.mpr ⟨hca j.1 h1, hcb j.2 h2⟩

/-- Dual to `kronecker_rowSparse`: the Kronecker product of a `dA`-column-sparse matrix
with a `dB`-column-sparse matrix is `dA·dB`-column-sparse. -/
theorem kronecker_colSparse {l m n p : Type*} [Fintype l] [Fintype n]
    (A : Matrix l m ℂ) (B : Matrix n p ℂ) (dA dB : ℕ)
    (hA : ColSparse A dA) (hB : ColSparse B dB) :
    ColSparse (A ⊗ₖ B) (dA * dB) := by
  intro j
  obtain ⟨sa, hsa, hca⟩ := hA j.1
  obtain ⟨sb, hsb, hcb⟩ := hB j.2
  refine ⟨sa ×ˢ sb, ?_, fun i hi => ?_⟩
  · rw [Finset.card_product]; exact Nat.mul_le_mul hsa hsb
  · simp only [Matrix.kroneckerMap_apply] at hi
    have h1 : A i.1 j.1 ≠ 0 := fun h => hi (by rw [h, zero_mul])
    have h2 : B i.2 j.2 ≠ 0 := fun h => hi (by rw [h, mul_zero])
    exact Finset.mem_product.mpr ⟨hca i.1 h1, hcb i.2 h2⟩

/-- Extending a `d`-row-sparse gate by the identity on extra wires preserves the bound
`d` (the identity contributes sparsity `1`). -/
theorem kronecker_one_rowSparse {l m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix l m ℂ) (dA : ℕ) (hA : RowSparse A dA) :
    RowSparse (A ⊗ₖ (1 : Matrix n n ℂ)) dA := by
  have h := kronecker_rowSparse A (1 : Matrix n n ℂ) dA 1 hA (one_rowSparse (n := n))
  simpa using h

/-- Extending a `d`-column-sparse gate by the identity on extra wires preserves the
bound `d`. -/
theorem kronecker_one_colSparse {l m n : Type*} [Fintype l] [Fintype n] [DecidableEq n]
    (A : Matrix l m ℂ) (dA : ℕ) (hA : ColSparse A dA) :
    ColSparse (A ⊗ₖ (1 : Matrix n n ℂ)) dA := by
  have h := kronecker_colSparse A (1 : Matrix n n ℂ) dA 1 hA (one_colSparse (n := n))
  simpa using h

/-- The Kronecker product of a unitary with the identity is unitary
(`Matrix.kronecker_mem_unitary`); so extending a gate to extra wires is still a legal
gate. -/
theorem kronecker_one_mem_unitary {l n : Type*} [Fintype l] [DecidableEq l]
    [Fintype n] [DecidableEq n] {A : Matrix l l ℂ}
    (hA : A ∈ Matrix.unitaryGroup l ℂ) :
    (A ⊗ₖ (1 : Matrix n n ℂ)) ∈ Matrix.unitaryGroup (l × n) ℂ :=
  Matrix.kronecker_mem_unitary hA (one_mem (Matrix.unitaryGroup n ℂ))

/-! ## Bounded sparse steps

The paper's sparse unitary model uses unitaries with *polynomially* many nonzero entries
per row/column; the `d = N` extreme of `SparseStepOn` carries no restriction.  We isolate
the bounded-sparsity predicate and connect it to the model. -/

/-- `SparseStepBounded d U`: `U` is a legal one-step evolution of the sparse unitary
model *with the explicit sparsity bound `d`* — unitary, `d`-row-sparse and
`d`-column-sparse.  This is the genuine "sparse" regime of arXiv:0904.2211v2 (p. 3);
choosing `d = poly(log N)` is the paper's efficiency requirement. -/
def SparseStepBounded {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (U : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup ι ℂ ∧ RowSparse U d ∧ ColSparse U d

/-- Unfolding of `SparseStepBounded`. -/
theorem sparseStepBounded_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (U : Matrix ι ι ℂ) :
    SparseStepBounded d U ↔
      (U ∈ Matrix.unitaryGroup ι ℂ ∧ RowSparse U d ∧ ColSparse U d) := Iff.rfl

/-- `SparseStepOn` is exactly "bounded sparse step for *some* bound `d`"; the bound is a
witness, which is what makes the `d = N` collapse explicit (c002's honesty note). -/
theorem sparseStepOn_iff_exists_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) :
    SparseStepOn U ↔ ∃ d, SparseStepBounded d U := by
  constructor
  · rintro ⟨hU, d, hr, hc⟩; exact ⟨d, hU, hr, hc⟩
  · rintro ⟨d, hU, hr, hc⟩; exact ⟨hU, d, hr, hc⟩

/-- arXiv:0904.2211v2, Sec. II, p. 3 (BQP ⊆ sparse): a `d`-sparse local unitary gate,
extended by the identity to the rest of the register, is a `d`-sparse step of the
sparse unitary model.  The untouced wires keep the sparsity bound *constant*. -/
theorem localGate_sparseStepBounded {l n : Type*} [Fintype l] [DecidableEq l]
    [Fintype n] [DecidableEq n] {A : Matrix l l ℂ}
    (hU : A ∈ Matrix.unitaryGroup l ℂ) (d : ℕ)
    (hrow : RowSparse A d) (hcol : ColSparse A d) :
    SparseStepBounded (ι := l × n) d (A ⊗ₖ (1 : Matrix n n ℂ)) :=
  ⟨kronecker_one_mem_unitary hU, kronecker_one_rowSparse A d hrow,
   kronecker_one_colSparse A d hcol⟩

/-- arXiv:0904.2211v2, Sec. II, p. 3 (BQP ⊆ sparse, concrete bound): every `2`-qubit
gate `G` (a `4 × 4` matrix, hence `4`-sparse by `dense_rowSparse`/`dense_colSparse`),
extended by the identity to a larger register, is a `4`-sparse sparse-model step.  This
is the paper's "the elementary gates have at most `4` nonzero entries per row". -/
theorem twoQubitGate_sparseStepBounded {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix (Fin 4) (Fin 4) ℂ) (hG : G ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    SparseStepBounded (ι := Fin 4 × n) 4 (G ⊗ₖ (1 : Matrix n n ℂ)) := by
  have hrow : RowSparse G 4 := by simpa using dense_rowSparse G
  have hcol : ColSparse G 4 := by simpa using dense_colSparse G
  exact localGate_sparseStepBounded hG 4 hrow hcol

/-! ## Sparse steps are efficiently implementable (sparse ⊆ BQP) -/

/-- arXiv:0904.2211v2, Sec. I–II (sparse ⊆ BQP at the model level): a `d`-sparse
unitary `U` is implemented by evolving the `d`-sparse Hermitian dilation
`H = [[0,U],[U†,0]]` for time `π/2` and phase-kickback.  Because `H` is again
`d`-sparse (`unitaryDilation_sparse`), the standard sparse-Hamiltonian-simulation cost
gives the poly `(log N, d, ‖Ht‖, 1/ε)` gate count of the paper's main theorem.  This
binds the sparse model's step set to the c001 implementation. -/
theorem sparseStep_dilation_implements {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} {d : ℕ} (h : SparseStepBounded d U) :
    (unitaryDilation U).IsHermitian ∧
    unitaryDilation U * unitaryDilation U = 1 ∧
    RowSparse (unitaryDilation U) d ∧ ColSparse (unitaryDilation U) d ∧
    (∀ ψ : ι → ℂ,
      NormedSpace.exp ((Complex.I * (-(((Real.pi / 2 : ℝ) : ℂ)))) • unitaryDilation U) *ᵥ anc1 ψ
        = (-Complex.I) • anc0 (U *ᵥ ψ)) :=
  ⟨unitaryDilation_isHermitian U,
   unitaryDilation_mul_self U h.1,
   (unitaryDilation_sparse U d h.2.1 h.2.2).1,
   (unitaryDilation_sparse U d h.2.1 h.2.2).2,
   fun ψ => unitaryDilation_phase_kickback U h.1 ψ⟩

end Qatlib.Papers.SparseUnitary09.MainResults.Model
