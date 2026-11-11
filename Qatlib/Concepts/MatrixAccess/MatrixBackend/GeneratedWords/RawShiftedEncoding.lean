/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.ContourAdapters
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.ShiftedCoefficientLaws
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.RawShiftedBody
import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Mathlib.Data.Matrix.Block
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.ShiftCoefficients
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-!
# Original common-frame access constructs the literal joint shifted encoding

The known coefficient preparation and phase gates are checked separately.
The actual common frame is lifted and relabeled, rather than replaced by an
assumed aligned frame.  Its corner is the normalized shift of the original
matrix, and the literal program pays its controlled-oracle query and macros.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords


open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Construction for shift Label Lift in the raw shifted encoding model. -/
private def shiftLabelLift {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) : Matrix (L × M) (L × N) ℂ :=
  (Matrix.blockDiagonal V).submatrix (Equiv.prodComm L M) (Equiv.prodComm L N)

/-- The finite construction in `RawShiftedEncoding` satisfies `shift_label_lift_adjoint` under the displayed hypotheses. -/
private theorem shift_label_lift_adjoint {M N L : Type} [DecidableEq L]
    (V : L → Matrix M N ℂ) :
    (shiftLabelLift V)ᴴ = shiftLabelLift (fun j => (V j)ᴴ) := by
  simp only [shiftLabelLift, Matrix.conjTranspose_submatrix, Matrix.blockDiagonal_conjTranspose]

/-- The finite construction in `RawShiftedEncoding` satisfies `shift_label_lift_mul` under the displayed hypotheses. -/
private theorem shift_label_lift_mul {M N P L : Type}
    [Fintype N] [Fintype L] [DecidableEq L]
    (V : L → Matrix M N ℂ) (W : L → Matrix N P ℂ) :
    shiftLabelLift (fun j => V j * W j) = shiftLabelLift V * shiftLabelLift W := by
  unfold shiftLabelLift
  rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]

/-- The finite construction in `RawShiftedEncoding` satisfies `shift_label_lift_one` under the displayed hypotheses. -/
private theorem shift_label_lift_one {I L : Type} [DecidableEq I] [DecidableEq L] :
    shiftLabelLift (fun _ : L => (1 : Matrix I I ℂ)) = 1 := by
  change (Matrix.blockDiagonal (1 : L → Matrix I I ℂ)).submatrix
    (Equiv.prodComm L I) (Equiv.prodComm L I) = 1
  rw [Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]

/-- The finite construction in `RawShiftedEncoding` satisfies `shift_label_lift_eq_select` under the displayed hypotheses. -/
private theorem shift_label_lift_eq_select {H L : Type} [DecidableEq L]
    (V : L → Matrix H H ℂ) : shiftLabelLift V = select V := by
  rfl

/-- The finite construction in `RawShiftedEncoding` satisfies `shifted_logical_frame_eq_lift` under the displayed hypotheses. -/
private theorem shifted_logical_frame_eq_lift
    {H I L : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (F : Matrix H I ℂ) :
    shiftedLogicalFrame (L := L) F = shiftLabelLift (fun _ : L => tagFrame shiftSeed F) := by
  ext ⟨j, s, x⟩ ⟨k, i⟩
  by_cases hj : j = k <;> by_cases hs : s = shiftSeed <;>
    simp [shiftedLogicalFrame, shiftLabelLift, Matrix.blockDiagonal, tagFrame, hj, hs]

/-- The literal logical frame remains an isometry on all label sectors. -/
theorem shiftedLogicalFrame_isometry
    {H I L : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (shiftedLogicalFrame (L := L) F) := by
  rw [shifted_logical_frame_eq_lift]
  change (shiftLabelLift (fun _ : L => tagFrame shiftSeed F))ᴴ *
    shiftLabelLift (fun _ : L => tagFrame shiftSeed F) = 1
  rw [shift_label_lift_adjoint, ← shift_label_lift_mul]
  have htag : (tagFrame shiftSeed F)ᴴ * tagFrame shiftSeed F = 1 :=
    tagFrame_isIsometry shiftSeed F hF
  simpa only [htag] using (shift_label_lift_one (I := I) (L := L))

/-- Compression by the literal logical frame is exactly compression in each
label sector by the actual tagged common frame. -/
theorem shiftedLogicalFrame_compress_select
    {H I L : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (F : Matrix H I ℂ)
    (V : L → Matrix (ShiftSlot × H) (ShiftSlot × H) ℂ) :
    compress (shiftedLogicalFrame F) (select V) (shiftedLogicalFrame F) =
      select (fun j => compress (tagFrame shiftSeed F) (V j) (tagFrame shiftSeed F)) := by
  simp only [compress, shifted_logical_frame_eq_lift, ← shift_label_lift_eq_select,
    shift_label_lift_adjoint, ← shift_label_lift_mul]

/-- Relabeling the actual frame preserves its Gram matrix and its isometry. -/
theorem rawShiftedFrame_isometry
    {H I L : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (rawShiftedFrame (L := L) F) := by
  have hgram := shiftedLogicalFrame_isometry (L := L) F hF
  unfold Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry at hgram ⊢
  change ((shiftedLogicalFrame F).submatrix (shiftWireEquiv L H).symm id)ᴴ *
    (shiftedLogicalFrame F).submatrix (shiftWireEquiv L H).symm id = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hgram]
  rfl

/-- The raw wire transport preserves the literal frame compression exactly;
no norm reindexing assumption is needed. -/
theorem rawShiftedFrame_compress_relabel
    {H I L : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (F : Matrix H I ℂ)
    (V : Matrix (ShiftedLogicalSpace L H) (ShiftedLogicalSpace L H) ℂ) :
    compress (rawShiftedFrame F) (relabelGate (shiftWireEquiv L H) V) (rawShiftedFrame F) =
      compress (shiftedLogicalFrame F) V (shiftedLogicalFrame F) := by
  simp only [compress, rawShiftedFrame, relabelGate, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rfl

/-- Every fixed preparation and coefficient-phase gate in the literal word
is unitary.  The unknown data oracle is absent from these gate parameters. -/
theorem raw_shifted_word_wellFormed
    (H L : Type) [Fintype H] [DecidableEq H] [Fintype L] [DecidableEq L]
    (α B₀ : ℝ) (z : L → ℂ) (hα : 0 ≤ α) (hB : 0 < B₀)
    (hbound : ∀ j, α + ‖z j‖ ≤ B₀) :
    WellFormedAdjointCircuit (rawShiftedWord (H := H) α B₀ z) := by
  have hmass (j : L) : 0 < coefficientMass (shiftCoefficient (z j) α B₀) := by
    rw [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.Shifts.shift_coefficient_mass (z j) α B₀ hα (hbound j)]
    exact hB
  have hprepare : shiftedPrepare (H := H) α B₀ z ∈
      Matrix.unitaryGroup (ShiftedLogicalSpace L H) ℂ := by
    unfold shiftedPrepare
    apply select_unitary
    intro j
    exact prepareRegister_unitary
      (coefficientPrepare_unitary (shiftCoefficient (z j) α B₀) shiftSeed (hmass j))
  have hphase : shiftedPhase (H := H) α B₀ z ∈
      Matrix.unitaryGroup (ShiftedLogicalSpace L H) ℂ := by
    unfold shiftedPhase
    apply select_unitary
    intro j
    apply select_unitary
    intro s
    exact phaseAbsorbed_unitary (shiftCoefficient (z j) α B₀)
      (fun _ : ShiftSlot => (1 : Matrix H H ℂ))
      (fun _ => (Matrix.unitaryGroup H ℂ).one_mem) s
  have hrawprepare : rawShiftedPrepare (H := H) α B₀ z ∈
      Matrix.unitaryGroup (ShiftedRawSpace L H) ℂ :=
    relabelGate_mem_unitary hprepare (shiftWireEquiv L H)
  have hrawphase : rawShiftedPhase (H := H) α B₀ z ∈
      Matrix.unitaryGroup (ShiftedRawSpace L H) ℂ :=
    relabelGate_mem_unitary hphase (shiftWireEquiv L H)
  simp only [rawShiftedWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
  exact ⟨adjoint_unitary hrawprepare, hrawphase, hrawprepare⟩

/-- G24: the original exact common-frame block encoding constructs the actual
normalized joint shifted encoding with the literal paid program and frames. -/
theorem raw_shifted_encoding
    (H I L : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (α B₀ : ℝ) (z : L → ℂ)
    (hbe : BlockEncoding A U F F α 0) (hB : 0 < B₀)
    (hbound : ∀ j, α + ‖z j‖ ≤ B₀) :
    WellFormedAdjointCircuit (rawShiftedWord (H := H) α B₀ z) ∧
    ProjectedUnitaryEncoding (jointNormalizedShift A z B₀)
      (evaluate (rawShiftedQuery U) (rawShiftedWord α B₀ z))
      (rawShiftedFrame F) (rawShiftedFrame F) ∧
    adjointQueryCount (rawShiftedWord (H := H) α B₀ z) = 1 ∧
    adjointGateCount (rawShiftedWord (H := H) α B₀ z) = 3 := by
  have hα : 0 ≤ α := hbe.normalization_pos.le
  have hFgram : Fᴴ * F = 1 := hbe.left_isometry
  have hAreal : A = α • compress F U F := by
    exact sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm hbe.error_le (norm_nonneg _)))
  have hA : A = (α : ℂ) • compress F U F := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at hAreal
    exact hAreal
  have hpoint (j : L) :
      compress (tagFrame shiftSeed F)
        (coefficientLCUUnitary (shiftCoefficient (z j) α B₀) (shiftSlotMatrix U) shiftSeed)
        (tagFrame shiftSeed F) = ((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j) := by
    rw [compress_tagFrame, shifted_lcu_compress H (z j) α B₀ U hα hB (hbound j)]
    change compress F (((B₀⁻¹ : ℝ) : ℂ) •
      ((z j) • (1 : Matrix H H ℂ) - (α : ℂ) • U)) F =
        ((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j)
    rw [compress_smul]
    apply congrArg (fun V : Matrix I I ℂ => ((B₀⁻¹ : ℝ) : ℂ) • V)
    simp only [compress, matrixShift, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
    rw [hFgram]
    change z j • 1 - (α : ℂ) • compress F U F = z j • 1 - A
    rw [← hA]
  have hlogical :
      compress (shiftedLogicalFrame F)
        (select (fun j => coefficientLCUUnitary (shiftCoefficient (z j) α B₀)
          (shiftSlotMatrix U) shiftSeed)) (shiftedLogicalFrame F) =
        jointNormalizedShift A z B₀ := by
    rw [shiftedLogicalFrame_compress_select]
    rw [normalized_shift_as_select]
    apply congrArg (fun V : L → Matrix I I ℂ => select V)
    funext j
    exact hpoint j
  have hrawcorner : compress (rawShiftedFrame F) (rawShiftedBody α B₀ z U)
      (rawShiftedFrame F) = jointNormalizedShift A z B₀ := by
    rw [rawShiftedBody, rawShiftedFrame_compress_relabel]
    exact hlogical
  have hframe := rawShiftedFrame_isometry (L := L) F hbe.left_isometry
  have hword := raw_shifted_word_wellFormed H L α B₀ z hα hB hbound
  have hquery : rawShiftedQuery (L := L) U ∈ Matrix.unitaryGroup (ShiftedRawSpace L H) ℂ := by
    unfold rawShiftedQuery parallelOracle
    exact select_unitary _ (fun _ => controlOracle_unitary hbe.unitary)
  obtain ⟨_hqueryeq, heval, hqueries, hgates, _hadjoint, _hadjointqueries, _hadjointgates⟩ :=
    raw_shifted_body_law H L α B₀ z U
  refine ⟨hword, ⟨hword.evaluate_unitary hquery, hframe, hframe, ?_⟩, hqueries, hgates⟩
  rw [heval]
  exact hrawcorner

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
