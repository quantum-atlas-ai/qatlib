/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanBlockLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Actual preparation columns and arbitrary phase tables on a diagonal clean
block. The source word need not be a whole-space SELECT. Preparation and phase
are explicit known matrix macros; finite gate refinement is separate. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open scoped BigOperators Kronecker
open scoped Matrix.Norms.L2Operator

local notation:70 A " ⬝ₘ " B =>
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

omit [Fintype H] [DecidableEq H] in
/-- The finite construction in `NativeColumnWeightedWord` satisfies `label_frame_fiber` under the displayed hypotheses. -/
private theorem label_frame_fiber (F : Matrix H I ℂ) (j₀ : J) :
    tagFrame j₀ F =
      ((1 : Matrix J J ℂ) ⊗ₖ F) * encodingFiber (I := I) j₀ := by
  classical
  ext ⟨j,h⟩ i
  rw [Matrix.mul_apply, Finset.sum_eq_single (j₀,i)]
  · simp [tagFrame, encodingFiber_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro x _ hx
    simp [encodingFiber_apply, hx]
  · simp

/-- The finite construction in `NativeColumnWeightedWord` satisfies `label_prepare_intertwine` under the displayed hypotheses. -/
private theorem label_prepare_intertwine (F : Matrix H I ℂ) (P : Matrix J J ℂ) :
    prepareRegister (I := H) P * ((1 : Matrix J J ℂ) ⊗ₖ F) =
      ((1 : Matrix J J ℂ) ⊗ₖ F) * prepareRegister (I := I) P := by
  simp only [prepareRegister, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- Exact Born/phase coefficients from the supplied preparation matrix, with
no canonical coefficient mass or full-unitary comparison. -/
theorem column_phase_clean_compress
    (F : Matrix H I ℂ) (W : Matrix (J × H) (J × H) ℂ)
    (Y : J → Matrix I I ℂ) (Q : Matrix J J ℂ) (φ : J → ℂ) (j₀ : J)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ F) W
      ((1 : Matrix J J ℂ) ⊗ₖ F) = select Y) :
    compress (tagFrame j₀ F)
      ((prepareRegister (I := H) Q)ᴴ *
        prepareRegister (I := H) (Matrix.diagonal φ) *
        W * prepareRegister (I := H) Q)
      (tagFrame j₀ F) =
      ∑ j, (star (Q j j₀) * Q j j₀ * φ j) • Y j := by
  let E : Matrix (J × H) (J × I) ℂ := (1 : Matrix J J ℂ) ⊗ₖ F
  let D : Matrix J J ℂ := Matrix.diagonal φ
  have hQ : prepareRegister (I := H) Q * E = E * prepareRegister (I := I) Q :=
    label_prepare_intertwine F Q
  have hQa : Eᴴ * (prepareRegister (I := H) Q)ᴴ =
      (prepareRegister (I := I) Q)ᴴ * Eᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hQ
  have hD' : Eᴴ * prepareRegister (I := H) D =
      prepareRegister (I := I) D * Eᴴ := by
    have h := congrArg Matrix.conjTranspose (label_prepare_intertwine F Dᴴ)
    simpa only [E, Matrix.conjTranspose_mul, prepareRegister,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using h
  have hsandwich :
      Eᴴ * ((prepareRegister (I := H) Q)ᴴ * prepareRegister (I := H) D *
        W * prepareRegister (I := H) Q) * E =
      (prepareRegister (I := I) Q)ᴴ * prepareRegister (I := I) D *
        (Eᴴ * W * E) * prepareRegister (I := I) Q := by
    calc
      _ = (Eᴴ * (prepareRegister (I := H) Q)ᴴ) *
          prepareRegister (I := H) D * W * (prepareRegister (I := H) Q * E) := by
            simp only [Matrix.mul_assoc]
      _ = ((prepareRegister (I := I) Q)ᴴ * Eᴴ) *
          prepareRegister (I := H) D * W * (E * prepareRegister (I := I) Q) := by rw [hQa, hQ]
      _ = (prepareRegister (I := I) Q)ᴴ *
          (Eᴴ * prepareRegister (I := H) D) * W * E * prepareRegister (I := I) Q := by
            simp only [Matrix.mul_assoc]
      _ = (prepareRegister (I := I) Q)ᴴ *
          (prepareRegister (I := I) D * Eᴴ) * W * E * prepareRegister (I := I) Q := by rw [hD']
      _ = _ := by simp only [Matrix.mul_assoc]
  have hselect : prepareRegister (I := I) D * select Y =
      select (fun j => φ j • Y j) := by
    ext ⟨j,i⟩ ⟨k,l⟩
    by_cases hj : j = k
    · subst k
      simp [D, prepareRegister, select, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
    · simp [D, prepareRegister, select, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, hj]
  change Eᴴ * W * E = select Y at hblock
  calc
    _ = compress (encodingFiber (I := I) j₀)
          (Eᴴ * ((prepareRegister (I := H) Q)ᴴ * prepareRegister (I := H) D *
            W * prepareRegister (I := H) Q) * E)
          (encodingFiber (I := I) j₀) := by
      rw [label_frame_fiber]
      simp only [compress, Matrix.conjTranspose_mul]
      simp only [E, D, Matrix.mul_assoc]
    _ = compress (encodingFiber (I := I) j₀)
          ((prepareRegister (I := I) Q)ᴴ * select (fun j => φ j • Y j) *
            prepareRegister (I := I) Q) (encodingFiber (I := I) j₀) := by
      rw [hsandwich, hblock]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (prepareRegister (I := I) D) (select Y), hselect]
    _ = _ := by
      have hf : prepareLift (I := I) (Qatlib.Foundations.PureStateMath.Ket j₀) =
          encodingFiber (I := I) j₀ := by
        have ht := tagFrame_eq j₀ (1 : Matrix I I ℂ)
        simpa only [tagFrame_one, Matrix.mul_one] using ht.symm
      rw [← hf]
      have hcol : Q *ᵥ Qatlib.Foundations.PureStateMath.Ket j₀ = fun j => Q j j₀ := by
        ext j
        simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
      have he : compress (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀))
          ((prepareRegister (I := I) Q)ᴴ * select (fun j => φ j • Y j) *
            prepareRegister (I := I) Q) (prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) =
          compress (prepareRegister (I := I) Q ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀))
            (select (fun j => φ j • Y j))
            (prepareRegister (I := I) Q ⬝ₘ prepareLift (Qatlib.Foundations.PureStateMath.Ket j₀)) := by
        simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [he, prepareRegister_mul_prepareLift, hcol, prepare_select_compress]
      simp only [lcuMatrix, smul_smul]

/-- The emitted PREP column and phase, including zero and slack labels. -/
def columnPhaseCoefficient (Q : Matrix J J ℂ) (φ : J → ℂ) (j₀ j : J) : ℂ :=
  star (Q j j₀) * Q j j₀ * φ j

/-- The same supplied query word, surrounded by its actual preparation,
phase and true adjoint. These three instructions are matrix macros. -/
def columnPhaseWord (Q : Matrix J J ℂ) (φ : J → ℂ)
    (W : List (AdjointStep (J × H))) : List (AdjointStep (J × H)) :=
  [.gate (prepareRegister (I := H) Q)ᴴ,
    .gate (prepareRegister (I := H) (Matrix.diagonal φ))] ++
    W ++ [.gate (prepareRegister (I := H) Q)]

omit [Fintype I] [DecidableEq I] in
/-- The finite construction in `NativeColumnWeightedWord` satisfies `columnPhaseWord_evaluate` under the displayed hypotheses. -/
theorem columnPhaseWord_evaluate (Q : Matrix J J ℂ) (φ : J → ℂ)
    (O : Matrix (J × H) (J × H) ℂ) (W : List (AdjointStep (J × H))) :
    evaluate O (columnPhaseWord Q φ W) =
      (prepareRegister (I := H) Q)ᴴ *
        prepareRegister (I := H) (Matrix.diagonal φ) *
        evaluate O W * prepareRegister (I := H) Q := by
  simp only [columnPhaseWord, evaluate_append, evaluate, instructionMatrix,
    Matrix.mul_one, Matrix.mul_assoc]

omit [Fintype J] [Fintype H] [Fintype I] [DecidableEq I] in
/-- The same emitted instruction list satisfies `columnPhaseWord_counts` with the displayed gate and query accounting. -/
theorem columnPhaseWord_counts (Q : Matrix J J ℂ) (φ : J → ℂ)
    (W : List (AdjointStep (J × H))) :
    adjointQueryCount (columnPhaseWord Q φ W) = adjointQueryCount W ∧
    adjointGateCount (columnPhaseWord Q φ W) = adjointGateCount W + 3 := by
  simp [columnPhaseWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount]

/-- The actual finite word or frame satisfies `column_phase_diagonal_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem column_phase_diagonal_unitary (φ : J → ℂ)
    (hφ : ∀ j, star (φ j) * φ j = 1) :
    Matrix.diagonal φ ∈ Matrix.unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext j k
  by_cases hjk : j = k
  · subst k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal] using hφ j
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, hjk, Ne.symm hjk]

omit [Fintype I] [DecidableEq I] in
/-- The actual finite word or frame satisfies `columnPhaseWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem columnPhaseWord_legal (Q : Matrix J J ℂ) (φ : J → ℂ)
    (W : List (AdjointStep (J × H)))
    (hQ : Q ∈ Matrix.unitaryGroup J ℂ)
    (hφ : ∀ j, star (φ j) * φ j = 1) (hW : WellFormedAdjointCircuit W) :
    WellFormedAdjointCircuit (columnPhaseWord Q φ W) := by
  have hP := prepareRegister_unitary (I := H) hQ
  have hD := prepareRegister_unitary (I := H) (column_phase_diagonal_unitary φ hφ)
  have hleft : WellFormedAdjointCircuit
      [.gate (prepareRegister (I := H) Q)ᴴ,
        .gate (prepareRegister (I := H) (Matrix.diagonal φ))] := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] using And.intro (adjoint_unitary hP) hD
  have hright : WellFormedAdjointCircuit [.gate (prepareRegister (I := H) Q)] := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] using hP
  exact (hleft.append hW).append hright

/-- The exact actual-column block, derived from the source word's clean
relation. No desired weighted-block approximation is an input. -/
theorem column_phase_word_encoding
    (F : Matrix H I ℂ) (O : Matrix (J × H) (J × H) ℂ)
    (W : List (AdjointStep (J × H))) (Y : J → Matrix I I ℂ)
    (Q : Matrix J J ℂ) (φ : J → ℂ) (j₀ : J)
    (hF : IsIsometry F) (hQ : Q ∈ Matrix.unitaryGroup J ℂ)
    (hφ : ∀ j, star (φ j) * φ j = 1)
    (hW : evaluate O W ∈ Matrix.unitaryGroup (J × H) ℂ)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ F) (evaluate O W)
      ((1 : Matrix J J ℂ) ⊗ₖ F) = select Y) :
    ProjectedUnitaryEncoding (∑ j, columnPhaseCoefficient Q φ j₀ j • Y j)
      (evaluate O (columnPhaseWord Q φ W)) (tagFrame j₀ F) (tagFrame j₀ F) := by
  have hP := prepareRegister_unitary (I := H) hQ
  have hD := prepareRegister_unitary (I := H) (column_phase_diagonal_unitary φ hφ)
  refine ⟨?_, tagFrame_isIsometry j₀ F hF, tagFrame_isIsometry j₀ F hF, ?_⟩
  · rw [columnPhaseWord_evaluate]
    exact (unitaryGroup (J × H) ℂ).mul_mem
      ((unitaryGroup (J × H) ℂ).mul_mem
        ((unitaryGroup (J × H) ℂ).mul_mem (adjoint_unitary hP) hD) hW) hP
  · rw [columnPhaseWord_evaluate]
    exact column_phase_clean_compress F (evaluate O W) Y Q φ j₀ hblock

/-- Each clean node block is a contraction even when the full source word
is not a SELECT. This uses an exact coordinate-column specialization. -/
theorem clean_node_norm_le_one
    (F : Matrix H I ℂ) (V : Matrix (J × H) (J × H) ℂ)
    (Y : J → Matrix I I ℂ) (hF : IsIsometry F)
    (hV : V ∈ Matrix.unitaryGroup (J × H) ℂ)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ F) V
      ((1 : Matrix J J ℂ) ⊗ₖ F) = select Y) (j : J) : ‖Y j‖ ≤ 1 := by
  have hc := column_phase_clean_compress F V Y (1 : Matrix J J ℂ) (fun _ => 1) j hblock
  have hid : prepareRegister (I := H) (1 : Matrix J J ℂ) = 1 := by
    simp [prepareRegister]
  have he : compress (tagFrame j F) V (tagFrame j F) = Y j := by
    simpa [hid, Matrix.one_apply] using hc
  rw [← he]
  exact Qatlib.Concepts.BlockEncoding.EncodingCore.l2_norm_compress_le_one (tagFrame_isIsometry j F hF) hV
    (tagFrame_isIsometry j F hF)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
