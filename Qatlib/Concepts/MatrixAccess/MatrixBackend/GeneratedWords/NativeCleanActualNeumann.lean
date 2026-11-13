/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanBlockLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Actual multi-node Neumann word in the label-external clean frame. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for clean Actual Inner Dec Eq in the native clean actual neumann model. -/
local instance cleanActualInnerDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _
/-- Typeclass instance for clean Actual Outer Dec Eq in the native clean actual neumann model. -/
local instance cleanActualOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- The actual relabeled shared-query word has the per-label Neumann blocks
in its common clean frame. This does not assert whole-space SELECT semantics. -/
theorem nativeMultiNodeRelabeled_clean_block (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    compress ((1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F))
      (evaluate (parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)))
        (nativeMultiNodeRelabeledWord b hb F ps p slack))
      ((1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)) =
      select (fun j => ((b : ℂ)⁻¹) • Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
        (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
          (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b) := by
  let e := nativeMultiNodeLabelEquiv (J := J) (H := H) b
  let L := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeMultiNodeFrame (J := J) F)
  let V := evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (parallelOracle (J := J) (nativeDataQuery U)))
    (nativeMultiNodeNeumannWord b hb F ps p slack)
  have hr : compress (Matrix.reindex e (Equiv.refl (J × I)) L)
      (relabelGate e V) (Matrix.reindex e (Equiv.refl (J × I)) L) = compress L V L := by
    simp only [compress, relabelGate, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    rfl
  have hf : Matrix.reindex e (Equiv.refl (J × I)) L =
      (1 : Matrix J J ℂ) ⊗ₖ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F) :=
    relabeled_neumann_frame b hb F
  rw [hf] at hr
  rw [nativeMultiNodeRelabeledWord_evaluate]
  exact hr.trans (nativeMultiNodeNeumann_per_label b hb F A U α hbe ps p slack).1.encoded

/- Scope note: this module proves the per-label clean-block identity. The weighted
construction below is a commented specification; its encoding and cost claims
are outside the formalized results of this file.

/-- Insert the same actual relabeled word into the ideal weight PREPARE and
phase macros. The weight macros are not a finite-gate implementation. -/
def nativeWeightedCleanNeumannWord (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (d : J → ℂ) (j₀ : J) :=
  weightedLCUSlotWord d j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)

omit [Fintype J] in
/-- The finite construction in `NativeCleanActualNeumann` satisfies `clean_actual_phase` under the displayed hypotheses. -/
private theorem clean_actual_phase (d : J → ℂ)
    {T : Type} [DecidableEq T] :
    select (phaseAbsorbed d (fun _ => (1 : Matrix T T ℂ))) =
      prepareRegister (I := T) (Matrix.diagonal (fun j => coefficientPhase (d j))) := by
  classical
  ext ⟨j,x⟩ ⟨k,y⟩
  by_cases hj : j = k <;> by_cases hx : x = y <;>
    simp [prepareRegister, Matrix.kroneckerMap_apply, select, phaseAbsorbed,
      Matrix.one_apply, hj, hx]

/-- The actual finite word or frame satisfies `clean_phase_unitary` with all displayed legality, input and workspace hypotheses. -/
private theorem clean_phase_unitary (d : J → ℂ)
    {T : Type} [Fintype T] [DecidableEq T] :
    prepareRegister (I := T) (Matrix.diagonal (fun j => coefficientPhase (d j))) ∈
      unitaryGroup (J × T) ℂ := by
  rw [← clean_actual_phase d]
  exact Qatlib.Concepts.CopyEvolution.Discriminate.select_unitary _
    (phaseAbsorbed_unitary d _ (fun _ => (unitaryGroup T ℂ).one_mem))

/-- The actual shared-oracle word encodes the weighted sum of its per-node
Neumann blocks, without requiring the whole word to be a SELECT. PREPARE and
phase are charged as three ideal macros. -/
theorem nativeWeightedCleanNeumann_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    let L := uniformNeumannFrame b hb (nativeDataFrame F)
    let O := parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U))
    let W := nativeWeightedCleanNeumannWord b hb F ps p slack d j₀
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) •
        (((b : ℂ)⁻¹) • leftDefectNeumann
          (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
            (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b))
      (evaluate O W) (tagFrame j₀ L) (tagFrame j₀ L) ∧
    O ∈ unitaryGroup _ ℂ ∧
    adjointQueryCount W = 2*b-1 ∧
    adjointGateCount W = 2*b+(2*b-1)*3+3 := by
  dsimp only
  let T := NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))
  let L : Matrix T I ℂ := uniformNeumannFrame b hb (nativeDataFrame F)
  let O : Matrix (J × T) (J × T) ℂ :=
    parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U))
  let R : List (AdjointStep (J × T)) := nativeMultiNodeRelabeledWord b hb F ps p slack
  let body := weightedLCUSlotBody d R
  let cs := scaledLCUAdjointWord (H := T) d j₀
  let Q := coefficientPrepare d j₀
  let D := Matrix.diagonal (fun j => coefficientPhase (d j))
  let W := nativeWeightedCleanNeumannWord b hb F ps p slack d j₀
  have hsub := substitute_adjoint_evaluate_cost O body cs
  have hev : evaluate O W =
      (prepareRegister (I := T) Q)ᴴ * prepareRegister (I := T) D *
        evaluate O R * prepareRegister (I := T) Q := by
    change evaluate O (substituteAdjointCircuit body cs) = _
    rw [hsub.1]
    simp only [cs, scaledLCUAdjointWord, evaluate, instructionMatrix, Matrix.mul_one,
      body, weightedLCUSlotBody, clean_actual_phase, Q, D]
    simp only [Matrix.mul_assoc]
  have hblock := nativeMultiNodeRelabeled_clean_block b hb F A U α hbe ps p slack
  change compress ((1 : Matrix J J ℂ) ⊗ₖ L) (evaluate O R)
    ((1 : Matrix J J ℂ) ⊗ₖ L) = _ at hblock
  have hc := clean_block_lcu_compress L (evaluate O R) _ d j₀ hmass hblock
  have hL : IsIsometry L := by
    change IsIsometry (freshNeumannFrame (b-1)
      (encodingFiber (I := Reg 6 × H) (⟨0,hb⟩ : Fin b) * nativeDataFrame F))
    unfold freshNeumannFrame
    exact IsIsometry.mul (encodingFiber_isIsometry _)
      (IsIsometry.mul (encodingFiber_isIsometry _) (nativeDataFrame_isometry F hbe.left_isometry))
  have htag := tagFrame_isIsometry j₀ L hL
  have hP := prepareRegister_unitary (I := T) (coefficientPrepare_unitary d j₀ hmass)
  have hphase : prepareRegister (I := T) D ∈ unitaryGroup (J × T) ℂ := clean_phase_unitary d
  have hraw := (nativeMultiNodeNeumann_per_label b hb F A U α hbe ps p slack).1.unitary
  have hR : evaluate O R ∈ unitaryGroup (J × T) ℂ := by
    change evaluate _ (nativeMultiNodeRelabeledWord b hb F ps p slack) ∈ _
    rw [nativeMultiNodeRelabeledWord_evaluate]
    exact relabelGate_mem_unitary hraw _
  have hW : evaluate O W ∈ unitaryGroup (J × T) ℂ := by
    rw [hev]
    exact (unitaryGroup (J × T) ℂ).mul_mem
      ((unitaryGroup (J × T) ℂ).mul_mem
        ((unitaryGroup (J × T) ℂ).mul_mem (adjoint_unitary hP) hphase) hR) hP
  have hO : O ∈ unitaryGroup (J × T) ℂ := by
    apply Qatlib.Concepts.CopyEvolution.Discriminate.select_unitary
    intro j
    apply tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    apply Qatlib.Concepts.CopyEvolution.Discriminate.select_unitary
    intro k
    exact nativeDataQuery_unitary U hbe.unitary
  refine ⟨⟨hW, htag, htag, ?_⟩, hO, ?_, ?_⟩
  · rw [hev]
    exact hc
  · change adjointQueryCount (substituteAdjointCircuit body cs) = _
    rw [hsub.2.1]
    simp [cs, scaledLCUAdjointWord, adjointQueryCount, body, weightedLCUSlotBody,
      (nativeMultiNodeRelabeledWord_cost b hb F ps p slack U).1]
  · change adjointGateCount (substituteAdjointCircuit body cs) = _
    rw [hsub.2.2.1]
    simp [cs, scaledLCUAdjointWord, adjointQueryCount, adjointGateCount, body,
      weightedLCUSlotBody, (nativeMultiNodeRelabeledWord_cost b hb F ps p slack U).2]
    omega
-/

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
