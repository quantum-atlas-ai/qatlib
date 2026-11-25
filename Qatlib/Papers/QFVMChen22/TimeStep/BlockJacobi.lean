/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Cell-block Jacobi preconditioning of the implicit system

[ChenXueChenEtAl2022], Appendix F, Eqs. (33)–(39), applies the inverse of each
cell's diagonal block to the system matrix and residual. The preconditioner
preserves the solution and the zero pattern of entire cell blocks. The
component-level pattern inside a nonzero block may change, so stencil access
can reuse a neighbor-cell oracle with all component slots. Computing one
preconditioned entry reads a full diagonal block and a column of the target
block. The read count here precedes inverse arithmetic and the cost of each
coefficient oracle call.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open scoped BigOperators

variable {Cell Component : Type} [Fintype Cell] [DecidableEq Cell]
  [Fintype Component] [DecidableEq Component]

/-- The matrix block with components at the given row and column cells. -/
def cellBlock (A : Matrix (Component × Cell) (Component × Cell) ℝ) (row column : Cell) :
    Matrix Component Component ℝ :=
  Matrix.of fun i j => A (i, row) (j, column)

/-- A diagonal matrix of inverse blocks, with one inverse per cell. -/
def blockJacobi (A : Matrix (Component × Cell) (Component × Cell) ℝ) :
    Matrix (Component × Cell) (Component × Cell) ℝ :=
  Matrix.blockDiagonal fun cell => (cellBlock A cell cell)⁻¹

/-- The diagonal part is a left inverse of the Jacobi preconditioner when all cell
diagonal blocks are nonsingular. -/
theorem cell_diagonal_mul_block_jacobi (A : Matrix (Component × Cell) (Component × Cell) ℝ)
    (hInvertible : ∀ cell, IsUnit (cellBlock A cell cell).det) :
    (Matrix.blockDiagonal fun cell => cellBlock A cell cell) * blockJacobi A = 1 := by
  rw [blockJacobi, ← Matrix.blockDiagonal_mul]
  have hBlocks : (fun cell => cellBlock A cell cell * (cellBlock A cell cell)⁻¹) =
      (1 : Cell → Matrix Component Component ℝ) := by
    funext cell
    exact Matrix.mul_nonsing_inv _ (hInvertible cell)
  rw [hBlocks, Matrix.blockDiagonal_one]

/-- Left preconditioning the matrix and residual leaves the implicit correction unchanged. -/
theorem block_jacobi_system_iff (A : Matrix (Component × Cell) (Component × Cell) ℝ)
    (hInvertible : ∀ cell, IsUnit (cellBlock A cell cell).det)
    (correction residual : Component × Cell → ℝ) :
    (blockJacobi A * A) *ᵥ correction = blockJacobi A *ᵥ residual ↔ A *ᵥ correction = residual := by
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have hApply := congrArg (fun x => (Matrix.blockDiagonal fun cell => cellBlock A cell cell) *ᵥ x) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, cell_diagonal_mul_block_jacobi A hInvertible,
      Matrix.one_mul, Matrix.one_mulVec] using hApply
  · intro h
    rw [h]

/-- A block of the preconditioned matrix is a local inverse times the corresponding
original block. The summation for an entry ranges only over components of the row cell. -/
theorem cell_block_block_jacobi_mul (A : Matrix (Component × Cell) (Component × Cell) ℝ) (row column : Cell) :
    cellBlock (blockJacobi A * A) row column = (cellBlock A row row)⁻¹ * cellBlock A row column := by
  ext i j
  simp only [cellBlock, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, blockJacobi,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul]
  simp

/-- Multiplying the residual by the preconditioner uses only the residual at the same cell. -/
theorem block_jacobi_residual_apply (A : Matrix (Component × Cell) (Component × Cell) ℝ)
    (residual : Component × Cell → ℝ) (cell : Cell) (i : Component) :
    (blockJacobi A *ᵥ residual) (i, cell) =
      ∑ j, (cellBlock A cell cell)⁻¹ i j * residual (j, cell) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockJacobi,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul]
  simp

/-- Entire zero cell blocks are preserved in both directions. This validates retaining
the same block-level structural sparsity for the neighbor-cell oracle. -/
theorem block_jacobi_cell_block_eq_zero_iff (A : Matrix (Component × Cell) (Component × Cell) ℝ)
    (row column : Cell) (hInvertible : IsUnit (cellBlock A row row).det) :
    cellBlock (blockJacobi A * A) row column = 0 ↔ cellBlock A row column = 0 := by
  rw [cell_block_block_jacobi_mul]
  constructor
  · intro h
    calc
      cellBlock A row column = cellBlock A row row * ((cellBlock A row row)⁻¹ * cellBlock A row column) :=
        (Matrix.mul_nonsing_inv_cancel_left _ _ hInvertible).symm
      _ = 0 := by rw [h, Matrix.mul_zero]
  · intro h
    rw [h, Matrix.mul_zero]

/-- Additional tables are unnecessary for the input reads of one Jacobi entry. The first
part of the index reads the diagonal block, and the second reads the requested column. -/
def jacobiEntryReadAddress (row column : Cell) (j : Component) :
    (Component × Component) ⊕ Component → (Component × Cell) × (Component × Cell) :=
  Sum.elim (fun p => ((p.1, row), (p.2, row))) (fun k => ((k, row), (j, column)))

/-- Recover an entry from the coefficient reads by inverting the diagonal block and
contracting a row of its inverse with the requested column. -/
def jacobiEntryFromReads (coeff : (Component × Component) ⊕ Component → ℝ) (i : Component) : ℝ :=
  let D : Matrix Component Component ℝ := Matrix.of fun k l => coeff (.inl (k, l))
  ∑ k, D⁻¹ i k * coeff (.inr k)

/-- The diagonal-block and column read plan returns the preconditioned coefficient. -/
theorem jacobi_entry_from_reads (A : Matrix (Component × Cell) (Component × Cell) ℝ)
    (row column : Cell) (i j : Component) :
    jacobiEntryFromReads (fun p => A (jacobiEntryReadAddress row column j p).1
      (jacobiEntryReadAddress row column j p).2) i = (blockJacobi A * A) (i, row) (j, column) := by
  exact (congrArg (fun B : Matrix Component Component ℝ => B i j)
    (cell_block_block_jacobi_mul A row column)).symm

/-- The read plan has one coefficient read per diagonal-block entry and one per component
of the target column, without any dependence on the number of cells. -/
theorem jacobi_entry_read_count (C : Type) [Fintype C] :
    Fintype.card ((C × C) ⊕ C) = Fintype.card C ^ 2 + Fintype.card C := by
  simp [pow_two]

end Qatlib.Papers.QFVMChen22.TimeStep
