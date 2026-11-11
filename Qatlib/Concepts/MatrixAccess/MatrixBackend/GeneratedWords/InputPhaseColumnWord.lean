/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeColumnWeightedWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate
/-! Put the coefficient phase before the selector in physical order. The
derived clean block agrees with the older output-phase word, even when the
two full operators differ. No global SELECT or commutation is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Physical order PREP, phase, source word, true PREP adjoint. The source
operator need only have the stated diagonal compression. -/
theorem input_phase_clean_compress
    (F : Matrix H I ℂ) (W : Matrix (J × H) (J × H) ℂ)
    (Y : J → Matrix I I ℂ) (Q : Matrix J J ℂ) (φ : J → ℂ) (j₀ : J)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ F) W
      ((1 : Matrix J J ℂ) ⊗ₖ F) = select Y) :
    compress (tagFrame j₀ F)
      ((prepareRegister (I := H) Q)ᴴ * W *
        prepareRegister (I := H) (Matrix.diagonal φ) * prepareRegister (I := H) Q)
      (tagFrame j₀ F) = ∑ j, columnPhaseCoefficient Q φ j₀ j • Y j := by
  let E : Matrix (J × H) (J × I) ℂ := (1 : Matrix J J ℂ) ⊗ₖ F
  have hba : compress E Wᴴ E = select (fun j => (Y j)ᴴ) := by
    rw [← compress_adjoint, hblock, parallel_select_adjoint]
  have hc := column_phase_clean_compress F Wᴴ (fun j => (Y j)ᴴ) Q (fun j => star (φ j)) j₀ hba
  have ha := congrArg Matrix.conjTranspose hc
  have hD : (prepareRegister (I := H) (Matrix.diagonal (fun j => star (φ j))))ᴴ =
      prepareRegister (I := H) (Matrix.diagonal φ) := by
    have hf : star (fun j => star (φ j)) = φ := by
      funext j
      change star (star (φ j)) = φ j
      exact star_star _
    simp only [prepareRegister, Matrix.conjTranspose_kronecker,
      Matrix.diagonal_conjTranspose, Matrix.conjTranspose_one, hf]
  have hs (j : J) : star (star (Q j j₀)*Q j j₀*star (φ j)) =
      columnPhaseCoefficient Q φ j₀ j := by
    simp only [star_mul, star_star, columnPhaseCoefficient]
    ring
  simpa only [compress_adjoint, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hD, hs, Matrix.mul_assoc] using ha

/-- The actual ordered word: gates are written in evaluate's matrix-product
order, so the last PREP is physically applied first. -/
def inputColumnPhaseWord (Q : Matrix J J ℂ) (φ : J → ℂ)
    (W : List (AdjointStep (J × H))) : List (AdjointStep (J × H)) :=
  [.gate (prepareRegister (I := H) Q)ᴴ] ++ W ++
    [.gate (prepareRegister (I := H) (Matrix.diagonal φ)), .gate (prepareRegister (I := H) Q)]

omit [Fintype I] [DecidableEq I] in
/-- The finite construction in `InputPhaseColumnWord` satisfies `inputColumnPhaseWord_evaluate` under the displayed hypotheses. -/
theorem inputColumnPhaseWord_evaluate (Q : Matrix J J ℂ) (φ : J → ℂ)
    (O : Matrix (J × H) (J × H) ℂ) (W : List (AdjointStep (J × H))) :
    evaluate O (inputColumnPhaseWord Q φ W) = (prepareRegister (I := H) Q)ᴴ * evaluate O W *
      prepareRegister (I := H) (Matrix.diagonal φ) * prepareRegister (I := H) Q := by
  simp only [inputColumnPhaseWord, evaluate_append, evaluate, instructionMatrix,
    Matrix.mul_one, Matrix.mul_assoc]

omit [Fintype J] [Fintype H] [Fintype I] [DecidableEq I] in
/-- The same emitted instruction list satisfies `inputColumnPhaseWord_counts` with the displayed gate and query accounting. -/
theorem inputColumnPhaseWord_counts (Q : Matrix J J ℂ) (φ : J → ℂ)
    (W : List (AdjointStep (J × H))) :
    adjointQueryCount (inputColumnPhaseWord Q φ W) = adjointQueryCount W ∧
    adjointGateCount (inputColumnPhaseWord Q φ W) = adjointGateCount W+3 := by
  simp [inputColumnPhaseWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount]

/-- Equality is asserted only after compression in the original common
frame. Preparation and phase need not be real, Hermitian or unitary here. -/
theorem inputColumnPhaseWord_compress_eq
    (F : Matrix H I ℂ) (O : Matrix (J × H) (J × H) ℂ)
    (W : List (AdjointStep (J × H))) (Y : J → Matrix I I ℂ)
    (Q : Matrix J J ℂ) (φ : J → ℂ) (j₀ : J)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ F) (evaluate O W)
      ((1 : Matrix J J ℂ) ⊗ₖ F) = select Y) :
    compress (tagFrame j₀ F) (evaluate O (inputColumnPhaseWord Q φ W)) (tagFrame j₀ F) =
      compress (tagFrame j₀ F) (evaluate O (columnPhaseWord Q φ W)) (tagFrame j₀ F) := by
  rw [inputColumnPhaseWord_evaluate, columnPhaseWord_evaluate,
    input_phase_clean_compress F (evaluate O W) Y Q φ j₀ hblock,
    column_phase_clean_compress F (evaluate O W) Y Q φ j₀ hblock]
  rfl

/-- The actual finite word or frame satisfies `input_phase_diagonal_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem input_phase_diagonal_unitary (φ : J → ℂ)
    (hφ : ∀ j, star (φ j)*φ j=1) : Matrix.diagonal φ ∈ unitaryGroup J ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext j k
  by_cases hjk : j=k
  · subst k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal] using hφ j
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, hjk, Ne.symm hjk]

omit [Fintype I] [DecidableEq I] in
/-- The actual finite word or frame satisfies `inputColumnPhaseWord_legal` with all displayed legality, input and workspace hypotheses. -/
theorem inputColumnPhaseWord_legal [outer : DecidableEq (J × H)]
    (Q : Matrix J J ℂ) (φ : J → ℂ) (W : List (AdjointStep (J × H)))
    (hQ : Q ∈ unitaryGroup J ℂ) (hφ : ∀ j, star (φ j)*φ j=1)
    (hW : WellFormedAdjointCircuit W) : WellFormedAdjointCircuit (inputColumnPhaseWord Q φ W) := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  have hP := prepareRegister_unitary (I := H) hQ
  have hD := prepareRegister_unitary (I := H) (input_phase_diagonal_unitary φ hφ)
  have hl : WellFormedAdjointCircuit [.gate (prepareRegister (I := H) Q)ᴴ] := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      using adjoint_unitary hP
  have hr : WellFormedAdjointCircuit [.gate (prepareRegister (I := H) (Matrix.diagonal φ)),
      .gate (prepareRegister (I := H) Q)] := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      using And.intro hD hP
  exact (hl.append hW).append hr

omit [Fintype I] [DecidableEq I] in
/-- The actual finite word or frame satisfies `inputColumnPhaseWord_unitary` with all displayed legality, input and workspace hypotheses. -/
theorem inputColumnPhaseWord_unitary [outer : DecidableEq (J × H)]
    (Q : Matrix J J ℂ) (φ : J → ℂ) (O : Matrix (J × H) (J × H) ℂ)
    (W : List (AdjointStep (J × H)))
    (hQ : Q ∈ unitaryGroup J ℂ) (hφ : ∀ j, star (φ j)*φ j=1)
    (hW : evaluate O W ∈ unitaryGroup (J × H) ℂ) :
    evaluate O (inputColumnPhaseWord Q φ W) ∈ unitaryGroup (J × H) ℂ := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  have hP := prepareRegister_unitary (I := H) hQ
  have hD := prepareRegister_unitary (I := H) (input_phase_diagonal_unitary φ hφ)
  rw [inputColumnPhaseWord_evaluate]
  exact (unitaryGroup (J × H) ℂ).mul_mem
    ((unitaryGroup (J × H) ℂ).mul_mem
      ((unitaryGroup (J × H) ℂ).mul_mem (adjoint_unitary hP) hW) hD) hP

/-- Exact block-encoding transport to the actual phase order. The supplied
block encoding is preserved, not weakened by an invented operator distance. -/
theorem inputColumnPhaseWord_transfer [outer : DecidableEq (J × H)]
    (T : Matrix I I ℂ) (F : Matrix H I ℂ) (O : Matrix (J × H) (J × H) ℂ)
    (W : List (AdjointStep (J × H))) (Y : J → Matrix I I ℂ)
    (Q : Matrix J J ℂ) (φ : J → ℂ) (j₀ : J) (β ε : ℝ)
    (hQ : Q ∈ unitaryGroup J ℂ) (hφ : ∀ j, star (φ j)*φ j=1)
    (hW : evaluate O W ∈ unitaryGroup (J × H) ℂ)
    (hblock : compress ((1 : Matrix J J ℂ) ⊗ₖ F) (evaluate O W)
      ((1 : Matrix J J ℂ) ⊗ₖ F) = select Y)
    (hpost : BlockEncoding T (evaluate O (columnPhaseWord Q φ W))
      (tagFrame j₀ F) (tagFrame j₀ F) β ε) :
    BlockEncoding T (evaluate O (inputColumnPhaseWord Q φ W))
      (tagFrame j₀ F) (tagFrame j₀ F) β ε := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  refine ⟨inputColumnPhaseWord_unitary Q φ O W hQ hφ hW,
    hpost.left_isometry, hpost.right_isometry, hpost.normalization_pos, hpost.error_nonneg, ?_⟩
  rw [inputColumnPhaseWord_compress_eq F O W Y Q φ j₀ hblock]
  exact hpost.error_le

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
