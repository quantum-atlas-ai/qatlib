/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.SparseCorrection
public import Qatlib.Concepts.QRAM.SignedReadout.Tomography

@[expose] public section

/-!
# Stencil oracles for an implicit linearized step

[ChenXueChenEtAl2022], Section 3.2 and Equations (4)–(8), derive a sparse
linear system at the current physical snapshot. The coefficient callback
is given the physical variables in the row stencil, together with the
coefficient slot. Contributions with the same column address add. The
resulting matrix acts exactly as the corresponding stencil sum.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Papers.QFVMChen22.QramStorage
open Matrix
open scoped BigOperators

variable {depth : ℕ}

/-- The coefficients for the current linearized row, computed from its variable neighborhood. -/
def rowCoefficient (geometry : Geometry depth)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (snapshot : Snapshot depth) (row : Address depth) (slot : Fin geometry.stencilSize) : ℝ :=
  linearize row (fun k => snapshot.physical (geometry.neighbor row k)) slot

/-- Assemble a matrix from the slot coefficients and the geometry's column indices. -/
def stencilMatrix (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) :
    Matrix (Address depth) (Address depth) ℝ :=
  Matrix.of fun row column =>
    ∑ slot, if geometry.neighbor row slot = column then coefficients row slot else 0

/-- The assembled matrix has a zero entry outside the row's storage stencil. -/
theorem stencil_matrix_eq_zero_of_absent_column (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (row column : Address depth) (h : ∀ slot, geometry.neighbor row slot ≠ column) :
    stencilMatrix geometry coefficients row column = 0 := by
  simp [stencilMatrix, h]

/-- Applying the assembled matrix is the sum of coefficient–variable products in the row stencil. -/
theorem stencil_matrix_mulVec (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (vector : Address depth → ℝ) (row : Address depth) :
    (stencilMatrix geometry coefficients *ᵥ vector) row =
      ∑ slot, coefficients row slot * vector (geometry.neighbor row slot) := by
  simp only [stencilMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Finite word oracle for a linearization coefficient, with geometry and variables fixed. -/
noncomputable def coefficientQuery {width : ℕ} (geometry : Geometry depth)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (snapshot : Snapshot depth) (encode : ℝ → BitVec width) :
    Matrix ((Address depth × Fin geometry.stencilSize) × BitVec width)
      ((Address depth × Fin geometry.stencilSize) × BitVec width) ℂ :=
  Qatlib.Concepts.QRAM.WordAccess.query
    (fun address => encode (rowCoefficient geometry linearize snapshot address.1 address.2))

/-- Coherent coefficient access addressed directly by row and column. -/
noncomputable def matrixEntryQuery {width : ℕ} (geometry : Geometry depth)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (snapshot : Snapshot depth) (encode : ℝ → BitVec width) :
    Matrix ((Address depth × Address depth) × BitVec width)
      ((Address depth × Address depth) × BitVec width) ℂ :=
  let matrix := stencilMatrix geometry (rowCoefficient geometry linearize snapshot)
  Qatlib.Concepts.QRAM.WordAccess.query (fun address => encode (matrix address.1 address.2))

/-- The measured sparse correction and the separately estimated solution norm. -/
structure Readout (depth : ℕ) where
  /-- Estimated norm used to recover the scale of the classical solution. -/
  solutionNorm : ℝ
  /-- Addressed estimates of normalized solution entries. -/
  estimates : List (Address depth × ℝ)

/-- Recover the sparse writeback input from the two tomography measurement batches. -/
noncomputable def Readout.ofTomography (solutionNorm : ℝ) (basis : List (Address depth))
    (interference : List (Bool × Address depth)) : Readout depth :=
  ⟨solutionNorm, Qatlib.Concepts.QRAM.SignedReadout.signedEstimates basis interference⟩

/-- One implicit step with a solver-readout procedure over the current linear system and QRAM. -/
noncomputable def timeStep (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (solveAndRead : Matrix (Address depth) (Address depth) ℝ → Tree ℝ depth → Readout depth)
    (snapshot : Snapshot depth) : Snapshot depth :=
  let matrix := stencilMatrix geometry (rowCoefficient geometry linearize snapshot)
  let result := solveAndRead matrix snapshot.residual
  applyCorrection geometry localRhs result.solutionNorm result.estimates snapshot

/-- Whatever admissible correction the readout supplies, the implicit step restores the residual
cache invariant for the next call. -/
theorem consistent_time_step (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ)
    (linearize : Address depth → (Fin geometry.stencilSize → ℝ) → Fin geometry.stencilSize → ℝ)
    (solveAndRead : Matrix (Address depth) (Address depth) ℝ → Tree ℝ depth → Readout depth)
    (snapshot : Snapshot depth) (h : Consistent geometry localRhs snapshot) :
    Consistent geometry localRhs (timeStep geometry localRhs linearize solveAndRead snapshot) :=
  consistent_apply_correction _ _ _ _ _ h

/-- Advance until the squared residual threshold or the permitted number of steps is reached. -/
noncomputable def solveSteady (toleranceSq : ℝ) (step : Snapshot depth → Snapshot depth) :
    ℕ → Snapshot depth → Snapshot depth
  | 0, snapshot => snapshot
  | remaining + 1, snapshot =>
      if mass snapshot.residual ≤ toleranceSq then snapshot
      else solveSteady toleranceSq step remaining (step snapshot)

/-- Every completed steady solve preserves consistency when its step preserves consistency. -/
theorem consistent_solve_steady (geometry : Geometry depth)
    (localRhs : Address depth → (Fin geometry.stencilSize → ℝ) → ℝ) (toleranceSq : ℝ)
    (step : Snapshot depth → Snapshot depth)
    (hStep : ∀ snapshot, Consistent geometry localRhs snapshot →
      Consistent geometry localRhs (step snapshot))
    (remaining : ℕ) (snapshot : Snapshot depth) (h : Consistent geometry localRhs snapshot) :
    Consistent geometry localRhs (solveSteady toleranceSq step remaining snapshot) := by
  induction remaining generalizing snapshot with
  | zero => exact h
  | succ remaining ih =>
      unfold solveSteady
      split
      · exact h
      · exact ih _ (hStep _ h)

end Qatlib.Papers.QFVMChen22.TimeStep
