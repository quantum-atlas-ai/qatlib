/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian.Basic
import Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence.SqrtGateOperator

/-!
# Hamiltonian decomposition into individual rows

This module defines `rowPiece` by retaining a single row of a Hamiltonian matrix and proves the
reconstruction identity `sum_rowPiece`. Each row piece is obtained by a diagonal coordinate
projection; `norm_rowPiece_le` and `rowSparse_rowPiece` show that this operation preserves the
relevant norm and sparsity bounds. The mathematical context is [AharonovTaShma2007].

## Main statements

* `sum_rowPiece`: Summing all individual row pieces reconstructs the original Hamiltonian
  matrix.
* `norm_rowPiece_le`: Retaining a single row does not increase the Euclidean operator norm of a
  Hamiltonian matrix.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian

open Qatlib.Papers.AdiabStateGen03.MainResults
open Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence

variable {n : ℕ}

/-- The matrix retaining row `i` of `H` and setting every other row to zero. -/
def rowPiece (H : Ham n) (i : Dim n) : Ham n :=
  fun i' j => if i' = i then H i j else 0

/-- The retained row of `rowPiece H i` agrees entrywise with row `i` of `H`. -/
@[simp] theorem rowPiece_apply_self (H : Ham n) (i j : Dim n) :
    rowPiece H i i j = H i j := by
  simp [rowPiece]

/-- Every row of `rowPiece H i` other than row `i` is zero. -/
theorem rowPiece_apply_of_ne (H : Ham n) {i i' : Dim n} (h : i' ≠ i) (j : Dim n) :
    rowPiece H i i' j = 0 := by
  simp [rowPiece, h]

/-- Summing all individual row pieces reconstructs the original Hamiltonian matrix
[AharonovTaShma2007]. -/
theorem sum_rowPiece (H : Ham n) : ∑ i, rowPiece H i = H := by
  ext i j
  simp only [Matrix.sum_apply, rowPiece]
  rw [Finset.sum_ite_eq]
  simp

/-- A row piece equals the product of the diagonal projection onto its row index with the
original matrix. -/
theorem rowPiece_eq_diagonal_mul (H : Ham n) (i : Dim n) :
    rowPiece H i = diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0) * H := by
  ext i' j
  rw [Matrix.diagonal_mul]
  by_cases h : i' = i <;> simp [rowPiece, h]

/-- The diagonal coordinate projection onto index `i` is Hermitian. -/
theorem indicator_isHermitian (i : Dim n) :
    IsHermitian (diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0)) := by
  unfold IsHermitian
  rw [Matrix.diagonal_conjTranspose]
  ext i' j
  by_cases h : i' = i <;> by_cases h' : j = i <;> simp [h, h', Matrix.diagonal]

/-- The diagonal coordinate projection onto index `i` is idempotent. -/
theorem indicator_idem (i : Dim n) :
    diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0) *
      diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0)
    = diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i' j
  by_cases h : i' = i <;> by_cases h' : i' = j <;> simp [Matrix.diagonal, h, h']

/-- Retaining a single row does not increase the Euclidean operator norm of a Hamiltonian matrix
[AharonovTaShma2007]. -/
theorem norm_rowPiece_le (H : Ham n) (i : Dim n) : ‖rowPiece H i‖ ≤ ‖H‖ := by
  rw [rowPiece_eq_diagonal_mul]
  have hnorm : ‖diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0)‖ ≤ 1 := by
    have h := projection_norm_le_one
      (diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0))
      (indicator_isHermitian i) (indicator_idem i)
    simpa [norm_toOp] using h
  calc ‖diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0) * H‖
      ≤ ‖diagonal (fun i' : Dim n => if i' = i then (1 : ℂ) else 0)‖ * ‖H‖ :=
        norm_mul_le _ _
    _ ≤ 1 * ‖H‖ := by gcongr
    _ = ‖H‖ := one_mul _

/-- Retaining a single row preserves a given bound on row sparsity [AharonovTaShma2007]. -/
theorem rowSparse_rowPiece {D : ℕ} {H : Ham n} (h : RowSparse H D) (i : Dim n) :
    RowSparse (rowPiece H i) D := by
  intro i'
  by_cases hi : i' = i
  · subst hi
    have hset : (Finset.univ.filter (fun j : Dim n => rowPiece H i' i' j ≠ 0))
        = (Finset.univ.filter (fun j : Dim n => H i' j ≠ 0)) := by
      refine Finset.filter_congr ?_
      intro j _
      simp [rowPiece_apply_self]
    rw [hset]
    exact h i'
  · have hset : (Finset.univ.filter (fun j : Dim n => rowPiece H i i' j ≠ 0)) = ∅ := by
      refine Finset.filter_false_of_mem ?_
      intro j _
      simp [rowPiece, hi]
    rw [hset]
    simp

end Qatlib.Papers.AdiabStateGen03.MainResults.SparseHamiltonian
