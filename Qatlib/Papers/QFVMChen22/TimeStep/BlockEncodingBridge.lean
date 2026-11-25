/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.ReciprocalReadout

@[expose] public section

/-!
# Block-encoded inputs for an implicit stencil solve

The QRAM access model of [ChenXueChenEtAl2022], Section 3.2, supplies
both a normalized stencil and a signed residual preparation. The sparse
unitary has distinct input and output frames. Its Hermitian lift gives
a common frame, as required by solvers using a single clean block. The
scale is determined by the entry bound and the two slot counts. These
identities concern the exact input semantics of one implicit step.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding (BlockEncoding)
open Qatlib.Concepts.Execution.WorkspaceCP (ProjectedUnitaryEncoding)
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Foundations.PureStateMath (ApplyGate Ket ZeroStr)
open Qatlib.Concepts.QRAM.AmplitudeAccess
  (signedTreePreparation signed_tree_preparation_entries signed_tree_preparation_unitary)
open Qatlib.Foundations.QramData.SquaredNormTree (Address Tree Valid mass read)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped Classical Matrix.Norms.L2Operator

variable {depth columnSlots : ℕ}

/-- The row and column frames of the sparse QRAM unitary encode the original
stencil with the exact matrix normalization. -/
theorem stencil_block_encoding (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots) :
    let data := stencilSparseAccess geometry coefficients entryScale columnSlots
    BlockEncoding ((stencilMatrix geometry coefficients).map Complex.ofRealHom)
      (sparseOperator data (.inr rowScratch) (.inr columnScratch))
      (leftFrame (.inr rowScratch)) (rightFrame (.inr columnScratch))
      (entryScale * sparseAlpha geometry.stencilSize columnSlots) 0 := by
  intro data
  have hRows := Nat.zero_lt_of_lt rowScratch.isLt
  have hCols := Nat.zero_lt_of_lt columnScratch.isLt
  have hα := sparseAlpha_pos hRows hCols
  have hData := stencil_sparse_access_legal geometry coefficients entryScale columnSlots hScale hEntry hColumns
  have h := sparseProjectedUnitaryEncoding data hData (.inr rowScratch) (.inr columnScratch) hRows hCols
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, mul_pos hScale hα, le_rfl, ?_⟩
  rw [h.encoded]
  suffices he : (stencilMatrix geometry coefficients).map Complex.ofRealHom =
      (entryScale * sparseAlpha geometry.stencilSize columnSlots) • data.encoded by
    rw [← he, sub_self, norm_zero]
  ext row column
  let entry : ℝ := stencilMatrix geometry coefficients row column
  change (entry : ℂ) =
    (entryScale * sparseAlpha geometry.stencilSize columnSlots) •
      (((entry / entryScale : ℝ) : ℂ) /
        sparseAlphaComplex geometry.stencilSize columnSlots)
  rw [sparseAlphaComplex_eq, ← Complex.ofReal_div, RCLike.real_smul_eq_coe_smul (K := ℂ),
    smul_eq_mul]
  have hEntryScale : entry = (entryScale * sparseAlpha geometry.stencilSize columnSlots) *
      (entry / entryScale / sparseAlpha geometry.stencilSize columnSlots) := by
    field_simp [hScale.ne', hα.ne']
  exact (congrArg Complex.ofReal hEntryScale).trans (Complex.ofReal_mul _ _)

/-- The Hermitian lift of the QRAM stencil has a common clean frame, and
the lifted tree preparation supplies the signed residual in its left block. -/
theorem stencil_common_frame_input (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (residual : Tree ℝ depth) (hValid : Valid residual) (hMass : 0 < mass residual)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots) :
    let C := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let scale := entryScale * sparseAlpha geometry.stencilSize columnSlots
    ProjectedUnitaryEncoding (stencilSignal geometry coefficients scale) U C C ∧
      liftedResidualPreparation residual ∈ Matrix.unitaryGroup (Address depth ⊕ Address depth) ℂ ∧
      ApplyGate (liftedResidualPreparation residual) (Ket (.inl (ZeroStr depth))) = liftedResidual residual := by
  intro C U scale
  obtain ⟨hC, hSelf, hSq, hSignal⟩ :=
    stencil_walk_encoding geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  have hUnitary : U ∈ Matrix.unitaryGroup _ ℂ := Matrix.mem_unitaryGroup_iff'.2 (by
    change Uᴴ * U = 1
    rw [show Uᴴ = U from hSelf]
    exact hSq)
  exact ⟨⟨hUnitary, hC, hC, hSignal⟩, lifted_residual_preparation_unitary residual hValid,
    lifted_residual_preparation_apply residual hValid hMass⟩

/-- The original, unlifted right-hand side is prepared by the signed
sum-tree circuit on the physical address register. -/
theorem stencil_residual_input (residual : Tree ℝ depth) (hValid : Valid residual)
    (hMass : 0 < mass residual) :
    signedTreePreparation residual ∈ Matrix.unitaryGroup (Address depth) ℂ ∧
      ApplyGate (signedTreePreparation residual) (Ket (ZeroStr depth)) =
        fun i => ((read residual i / Real.sqrt (mass residual) : ℝ) : ℂ) :=
  ⟨signed_tree_preparation_unitary residual hValid,
    funext (signed_tree_preparation_entries residual hValid hMass)⟩

end Qatlib.Papers.QFVMChen22.TimeStep
