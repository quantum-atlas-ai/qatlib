/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.Preparation
public import Qatlib.Concepts.QRAM.WordAccess.Lookup

@[expose] public section

/-!
# Dynamic QRAM data for recommendation

In [KerenidisPrakash2017], Theorem 5.1 and Appendix A, the binary tree of row
norms joins the per-row binary trees of entries. The row bits select a subtree,
and the column bits select the entry within that subtree. An overwrite repairs
both levels of cached masses in one traversal. The number of written cells
counts tree nodes and leaves, with exact real data and arithmetic.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QRecommender16.QramMatrix

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Matrix
open scoped BigOperators

variable {rows columns : ℕ}

/-- One tree packs the row-norm index above the signed entry trees. -/
abbrev MatrixStorage (rows columns : ℕ) := Tree ℝ (columns + rows)

/-- The row selected by a prefix, whose root mass is the squared row norm. -/
def rowTree (storage : MatrixStorage rows columns) (row : Address rows) : Tree ℝ columns :=
  subtree rows storage row

/-- Read an entry by its row and column addresses. -/
def entry (storage : MatrixStorage rows columns) (row : Address rows) (column : Address columns) :
    ℝ := read (rowTree storage row) column

/-- Overwrite an entry and refresh the per-row and top-level caches together. -/
def writeEntry (storage : MatrixStorage rows columns) (row : Address rows)
    (column : Address columns) (value : ℝ) : MatrixStorage rows columns :=
  write storage (joinAddress rows row column) value

/-- An overwrite preserves the QRAM representation invariant. -/
theorem valid_write_entry (storage : MatrixStorage rows columns) (h : Valid storage)
    (row : Address rows) (column : Address columns) (value : ℝ) :
    Valid (writeEntry storage row column value) :=
  valid_write _ _ _ h

/-- Only the selected pair of row and column changes after an overwrite. -/
theorem entry_after_write (storage : MatrixStorage rows columns)
    (selectedRow row : Address rows) (selectedColumn column : Address columns) (value : ℝ) :
    entry (writeEntry storage selectedRow selectedColumn value) row column =
      if row = selectedRow ∧ column = selectedColumn then value else entry storage row column := by
  simp only [entry, rowTree, read_subtree, writeEntry, read_write, join_address_eq_iff]

/-- One overwrite stores one cell for each row-address bit and column-address bit, plus the leaf. -/
theorem entry_write_cells (storage : MatrixStorage rows columns) (row : Address rows)
    (column : Address columns) (value : ℝ) :
    (writeWithCount storage (joinAddress rows row column) value).2 = columns + rows + 1 :=
  write_cell_count _ _ _

/-- The squared norm of an individual row is the cached mass of its subtree. -/
theorem row_mass_eq (storage : MatrixStorage rows columns) (h : Valid storage) (row : Address rows) :
    mass (rowTree storage row) = ∑ column : Address columns, entry storage row column ^ 2 :=
  mass_eq_sum _ (valid_subtree rows storage row h)

/-- The total cached mass is the squared Frobenius norm of the addressed matrix. -/
theorem matrix_mass_eq (storage : MatrixStorage rows columns) (h : Valid storage) :
    mass storage = ∑ row : Address rows, ∑ column : Address columns, entry storage row column ^ 2 := by
  rw [mass_eq_sum_subtrees rows storage h]
  exact Finset.sum_congr rfl (fun row _ => row_mass_eq storage h row)

/-- The state prepared at a row prefix has the amplitudes of that row divided by its norm. -/
theorem row_preparation (storage : MatrixStorage rows columns) (h : Valid storage)
    (row : Address rows) (column : Address columns) :
    pathAmplitude (rowTree storage row) column =
      entry storage row column / Real.sqrt (∑ j : Address columns, entry storage row j ^ 2) := by
  have hRow : Valid (rowTree storage row) := valid_subtree rows storage row h
  rw [path_amplitude_eq _ hRow, row_mass_eq storage h row]
  rfl

/-- The top-level preparation places the selected row norm over the whole matrix norm. -/
theorem row_norm_preparation (storage : MatrixStorage rows columns) (h : Valid storage)
    (hPos : 0 < mass storage) (row : Address rows) :
    prefixAmplitude rows storage row =
      Real.sqrt (∑ column : Address columns, entry storage row column ^ 2) /
        Real.sqrt (mass storage) := by
  rw [prefix_amplitude_eq rows storage h hPos, ← row_mass_eq storage h row]
  rfl

/-- Coherent word access to row and column addresses under a chosen finite encoding. -/
noncomputable def entryQuery {width : ℕ} (encode : ℝ → BitVec width)
    (storage : MatrixStorage rows columns) :
    Matrix ((Address rows × Address columns) × BitVec width)
      ((Address rows × Address columns) × BitVec width) ℂ :=
  Qatlib.Concepts.QRAM.WordAccess.query fun indices => encode (entry storage indices.1 indices.2)

end Qatlib.Papers.QRecommender16.QramMatrix
