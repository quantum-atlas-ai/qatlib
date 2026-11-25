/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.ChebyshevSolve
public import Qatlib.Concepts.QsvtCore.PhaseExistence.SparseAccessConstruction
public import Mathlib.Data.List.Dedup

@[expose] public section

/-!
# Sparse matrix access for the implicit stencil

[ChenXueChenEtAl2022], Section 3.2 and Appendix C, supply position and
entry access to the linear solver. The row slots and the reverse
incidence lists of the current stencil determine its nonzero supports.
Duplicate locations are coalesced after their coefficients have been
summed, and exact zero entries are removed. The padded position maps and
scaled entries give a sparse block encoding. A Hermitian lift makes this
encoding an involution for the Chebyshev walk, including for a nonsymmetric
stencil. The construction is at exact matrix and arithmetic semantics.
Finite-precision support extraction and gate costs require further analysis.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (signal)
open Qatlib.Foundations.MatrixAlgebra.HermitianLift
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped Classical

variable {depth : ℕ}

/-- Scale the current stencil entries to amplitudes for the sparse value oracle. -/
def scaledStencilEntry (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (row column : Address depth) : ℂ :=
  (stencilMatrix geometry coefficients row column / entryScale : ℝ)

/-- List each nonzero column of a row once, using only its neighbor list for candidates. -/
def stencilRowSupport (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale : ℝ) (row : Address depth) : List (Address depth) := by
  classical
  exact (List.ofFn (geometry.neighbor row)).dedup.filter fun column =>
    decide (scaledStencilEntry geometry coefficients entryScale row column ≠ 0)

/-- List each nonzero row of a column once, using the geometry's reverse incidence list. -/
def stencilColumnSupport (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale : ℝ) (column : Address depth) : List (Address depth) := by
  classical
  exact (geometry.affected column).dedup.filter fun row =>
    decide (scaledStencilEntry geometry coefficients entryScale row column ≠ 0)

/-- A nonzero scaled coefficient witnesses that some geometric neighbor slot names its column. -/
private theorem neighbor_of_entry_ne_zero (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (row column : Address depth)
    (h : scaledStencilEntry geometry coefficients entryScale row column ≠ 0) :
    ∃ slot, geometry.neighbor row slot = column := by
  by_contra hAbsent
  push Not at hAbsent
  exact h (by simp [scaledStencilEntry, stencil_matrix_eq_zero_of_absent_column _ _ _ _ hAbsent])

/-- The row support is exactly the nonzero support of the scaled stencil. -/
theorem mem_stencil_row_support_iff (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale : ℝ) (row column : Address depth) :
    column ∈ stencilRowSupport geometry coefficients entryScale row ↔
      scaledStencilEntry geometry coefficients entryScale row column ≠ 0 := by
  classical
  simp only [stencilRowSupport, List.mem_filter, List.mem_dedup, List.mem_ofFn, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨neighbor_of_entry_ne_zero _ _ _ _ _ h, h⟩⟩

/-- The column support is exactly the nonzero support of the scaled stencil. -/
theorem mem_stencil_column_support_iff (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale : ℝ) (row column : Address depth) :
    row ∈ stencilColumnSupport geometry coefficients entryScale column ↔
      scaledStencilEntry geometry coefficients entryScale row column ≠ 0 := by
  classical
  simp only [stencilColumnSupport, List.mem_filter, List.mem_dedup, geometry.mem_affected,
    decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨neighbor_of_entry_ne_zero _ _ _ _ _ h, h⟩⟩

/-- Return the address at the slot or use that slot's own padding label. -/
def paddedSlot {A : Type*} {slots : ℕ} (addresses : List A) (slot : Fin slots) :
    A ⊕ Fin slots :=
  if h : (slot : ℕ) < addresses.length then Sum.inl (getElem addresses slot.val h) else Sum.inr slot

/-- Padded lookup is injective when the occupied list has distinct entries. -/
private theorem padded_slot_injective {A : Type*} {slots : ℕ} (addresses : List A)
    (hNodup : addresses.Nodup) : Function.Injective (paddedSlot (slots := slots) addresses) := by
  intro i j hEqual
  by_cases hi : i.val < addresses.length <;> by_cases hj : j.val < addresses.length
  · simp only [paddedSlot, dite_eq_left hi, dite_eq_left hj, Sum.inl.injEq] at hEqual
    exact Fin.ext (hNodup.eq_of_getElem_eq hi hj hEqual)
  · simp [paddedSlot, hi, hj] at hEqual
  · simp [paddedSlot, hi, hj] at hEqual
  · simpa [paddedSlot, hi, hj] using hEqual

/-- A lookup returning an occupied address witnesses list membership. -/
private theorem mem_of_padded_slot {A : Type*} {slots : ℕ} {addresses : List A} {slot : Fin slots}
    {a : A} (h : paddedSlot addresses slot = Sum.inl a) : a ∈ addresses := by
  by_cases hi : slot.val < addresses.length
  · simp only [paddedSlot, dite_eq_left hi, Sum.inl.injEq] at h
    exact List.mem_iff_getElem.mpr ⟨slot.val, hi, h⟩
  · simp [paddedSlot, hi] at h

/-- Every address in a list of bounded length is returned by some slot. -/
private theorem exists_padded_slot {A : Type*} {slots : ℕ} {addresses : List A} {a : A}
    (hLength : addresses.length ≤ slots) (h : a ∈ addresses) :
    ∃ slot : Fin slots, paddedSlot addresses slot = Sum.inl a := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  exact ⟨⟨i, hi.trans_le hLength⟩, by simp [paddedSlot, hi, he]⟩

/-- An unoccupied lookup uses the slot's own label, so padding fixes that label. -/
private theorem padded_slot_index {A : Type*} {slots : ℕ} {addresses : List A}
    {i j : Fin slots} (h : paddedSlot addresses i = Sum.inr j) : i = j := by
  by_cases hi : i.val < addresses.length
  · simp [paddedSlot, hi] at h
  · simpa [paddedSlot, hi] using h

/-- The stencil's position and value data, with the row budget fixed by the geometry
and a separately chosen column budget. -/
def stencilSparseAccess (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale : ℝ) (columnSlots : ℕ) :
    SparseAccess (Address depth) (Address depth) geometry.stencilSize columnSlots where
  rowPos row := paddedSlot (stencilRowSupport geometry coefficients entryScale row)
  colPos slot column := paddedSlot (stencilColumnSupport geometry coefficients entryScale column) slot
  entry := scaledStencilEntry geometry coefficients entryScale

/-- Position maps enumerate exactly the nonzeros, and the scaled values are valid amplitudes
when the entry scale bounds all assembled stencil coefficients. A bound on the distinct rows
in each reverse incidence list also bounds the corresponding nonzero column support. -/
theorem stencil_sparse_access_legal (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ)
    (entryScale : ℝ) (columnSlots : ℕ)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots) :
    SparseAccessLegal (stencilSparseAccess geometry coefficients entryScale columnSlots) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row
    exact padded_slot_injective _ ((List.nodup_dedup _).filter _)
  · intro column
    exact padded_slot_injective _ ((List.nodup_dedup _).filter _)
  · intro row slot column h
    exact (mem_stencil_row_support_iff _ _ _ _ _).mp (mem_of_padded_slot h)
  · intro row column h
    apply exists_padded_slot _ ((mem_stencil_row_support_iff _ _ _ _ _).mpr h)
    exact (List.length_filter_le _ _).trans
      ((List.dedup_sublist _).length_le.trans_eq List.length_ofFn)
  · intro column slot row h
    exact (mem_stencil_column_support_iff _ _ _ _ _).mp (mem_of_padded_slot h)
  · intro column row h
    exact exists_padded_slot ((List.length_filter_le _ _).trans (hColumns column))
      ((mem_stencil_column_support_iff _ _ _ _ _).mpr h)
  · intro row column
    change ‖scaledStencilEntry geometry coefficients entryScale row column‖ ≤ 1
    rw [scaledStencilEntry, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hScale]
    exact (div_le_one hScale).mpr (hEntry row column)
  · intro row i j h
    have he : i = j := padded_slot_index h
    subst j
    exact h
  · intro column i j h
    have he : i = j := padded_slot_index h
    subst j
    exact h

/-- The Hermitian-walk workspace adds one qubit to the padded position and value registers. -/
abbrev StencilWorkspace (depth rowSlots columnSlots : ℕ) :=
  Fin 2 × SparseWorkspace (Address depth) (Address depth) rowSlots columnSlots

/-- The workspace identity uses the same product equality decision as the qubit-indexed lift. -/
instance stencilWorkspaceDecidableEq (depth rowSlots columnSlots : ℕ) :
    DecidableEq (StencilWorkspace depth rowSlots columnSlots) :=
  @instDecidableEqProd (Fin 2) (SparseWorkspace (Address depth) (Address depth) rowSlots columnSlots)
    inferInstance inferInstance

/-- The solver frame uses the row register on the left and the column register on the right,
with their respective clean scratch slots. -/
def stencilWalkFrame (depth : ℕ) {rowSlots columnSlots : ℕ}
    (rowScratch : Fin rowSlots) (columnScratch : Fin columnSlots) :
    Matrix (StencilWorkspace depth rowSlots columnSlots) (Address depth ⊕ Address depth) ℂ :=
  nativeEmbedding (leftFrame (Sum.inr rowScratch)) (rightFrame (Sum.inr columnScratch))

/-- The Hermitian involution obtained by controlling the sparse operator and its adjoint
on the extra qubit and swapping. -/
def stencilWalkInvolution (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    {columnSlots : ℕ} (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots) :
    Matrix (StencilWorkspace depth geometry.stencilSize columnSlots)
      (StencilWorkspace depth geometry.stencilSize columnSlots) ℂ :=
  native (sparseOperator (stencilSparseAccess geometry coefficients entryScale columnSlots)
    (Sum.inr rowScratch) (Sum.inr columnScratch))

/-- The derived frame and involution satisfy the hypotheses of the qubitized Chebyshev walk.
The signal is the normalized Hermitian lift of the assembled stencil. -/
theorem stencil_walk_encoding (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    {columnSlots : ℕ} (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    Cᴴ * C = 1 ∧ Uᴴ = U ∧ U * U = 1 ∧
      signal C U = stencilSignal geometry coefficients (entryScale * sparseAlpha geometry.stencilSize columnSlots) := by
  let data := stencilSparseAccess geometry coefficients entryScale columnSlots
  let V := sparseOperator data (.inr rowScratch) (.inr columnScratch)
  let E := leftFrame (I := Address depth) (O := Address depth) (sc := columnSlots) (.inr rowScratch)
  let F := rightFrame (I := Address depth) (O := Address depth) (sr := geometry.stencilSize) (.inr columnScratch)
  have hData := stencil_sparse_access_legal geometry coefficients entryScale columnSlots hScale hEntry hColumns
  have hV := sparseProjectedUnitaryEncoding data hData (.inr rowScratch) (.inr columnScratch)
    (Nat.zero_lt_of_lt rowScratch.isLt) (Nat.zero_lt_of_lt columnScratch.isLt)
  refine ⟨nativeEmbedding_gram E F hV.left_isometry hV.right_isometry, native_adjoint V,
    native_squared V (Matrix.mem_unitaryGroup_iff'.mp hV.unitary)
      (Matrix.mem_unitaryGroup_iff.mp hV.unitary), ?_⟩
  change (nativeEmbedding E F)ᴴ * native V * nativeEmbedding E F = _
  rw [native_compression]
  have hCompress : Eᴴ * V * F = data.encoded := hV.encoded
  rw [hCompress, stencilSignal]
  congr 1
  ext row column
  change ((stencilMatrix geometry coefficients row column / entryScale : ℝ) : ℂ) /
      sparseAlphaComplex geometry.stencilSize columnSlots =
    (((entryScale * sparseAlpha geometry.stencilSize columnSlots)⁻¹ *
      stencilMatrix geometry coefficients row column : ℝ) : ℂ)
  rw [sparseAlphaComplex_eq, ← Complex.ofReal_div, div_div, div_eq_mul_inv, mul_comm]

end Qatlib.Papers.QFVMChen22.TimeStep
