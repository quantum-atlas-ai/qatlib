/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeCleanNeumannLCU
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.NativeWeightedLCUSlot
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
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Split actual weighted Neumann endpoint. The final combined encoding is an
unverified comment after the proved frame, unitarity and cost results. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix

open scoped BigOperators Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for parts Branch Dec Eq in the native clean neumann parts model. -/
local instance partsBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for parts Outer Dec Eq in the native clean neumann parts model. -/
local instance partsOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _
/-- Typeclass instance for parts Inner Dec Eq in the native clean neumann parts model. -/
local instance partsInnerDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _

/-- Single-node clean frame, unchanged across the node labels. -/
theorem nativeCleanSingleFrame_isometry (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannFrame b hb (nativeDataFrame F)) := by
  change Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame (b-1)
    (encodingFiber (I := Reg 6 × H) (⟨0,hb⟩ : Fin b) * nativeDataFrame F))
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame
  exact Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (encodingFiber_isIsometry _)
    (Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (encodingFiber_isIsometry _) (nativeDataFrame_isometry F hF))

/-- Unitarity of the actual relabeled word, from the original encoding. -/
theorem nativeCleanRelabeledWord_unitary (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) :
    evaluate (parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b (nativeDataQuery U)))
      (nativeMultiNodeRelabeledWord b hb F ps p slack) ∈
        unitaryGroup (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) ℂ := by
  rw [nativeMultiNodeRelabeledWord_evaluate]
  exact relabelGate_mem_unitary
    (nativeMultiNodeNeumann_per_label b hb F A U α hbe ps p slack).1.unitary _

/-- Syntactic weight wrapper cost for any actual query word. -/
private theorem cleanWeightWord_counts {T : Type} [Fintype T] [DecidableEq T]
    (d : J → ℂ) (j₀ : J) (W : List (AdjointStep (J × T))) :
    adjointQueryCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) = adjointQueryCount W ∧
    adjointGateCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) = adjointGateCount W + 3 := by
  let body := Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody d W
  let cs := scaledLCUAdjointWord (H := T) d j₀
  have h := substitute_adjoint_evaluate_cost (1 : Matrix (J × T) (J × T) ℂ) body cs
  constructor
  · change adjointQueryCount (substituteAdjointCircuit body cs) = _
    rw [h.2.1]
    simp [cs, scaledLCUAdjointWord, adjointQueryCount, body, Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]
  · change adjointGateCount (substituteAdjointCircuit body cs) = _
    rw [h.2.2.1]
    simp [cs, scaledLCUAdjointWord, adjointQueryCount, adjointGateCount, body,
      Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody]
    omega

omit [DecidableEq I] in
/-- The actual relabeled Neumann word retains the original query count; the
weighting adds three ideal known macros. -/
theorem nativeCleanNeumannWeight_cost (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (d : J → ℂ) (j₀ : J)
    (U : Matrix H H ℂ) :
    adjointQueryCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀
      (nativeMultiNodeRelabeledWord b hb F ps p slack)) = 2*b-1 ∧
    adjointGateCount (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀
      (nativeMultiNodeRelabeledWord b hb F ps p slack)) = 2*b+(2*b-1)*3+3 := by
  have hc := cleanWeightWord_counts d j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)
  have hr := nativeMultiNodeRelabeledWord_cost b hb F ps p slack U
  exact ⟨hc.1.trans hr.1, hc.2.trans (by rw [hr.2])⟩

/- UNVERIFIED DRAFT: the combined encoding times out during whnf at 400000
heartbeats despite its separate inputs being proved.

/-- The same actual shared query word encodes the ideal weighted sum of
per-node Neumann blocks; no whole-space SELECT is assumed. -/
theorem nativeCleanNeumannWeight_encoding (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (A : Matrix I I ℂ) (U : Matrix H H ℂ) (α : ℝ)
    (hbe : BlockEncoding A U F F α 0)
    (ps : J → Fin 7 → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (p : J → QuantumAlgorithmDev.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    ProjectedUnitaryEncoding
      (∑ j, (d j / (coefficientMass d : ℂ)) •
        (((b : ℂ)⁻¹) • leftDefectNeumann
          (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
            (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b))
      (evaluate (parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U)))
        (weightedLCUSlotWord d j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)))
      (tagFrame j₀ (uniformNeumannFrame b hb (nativeDataFrame F)))
      (tagFrame j₀ (uniformNeumannFrame b hb (nativeDataFrame F))) := by
  let L := uniformNeumannFrame b hb (nativeDataFrame F)
  let O := parallelOracle (J := J) (uniformNeumannOracle b (nativeDataQuery U))
  let W := nativeMultiNodeRelabeledWord b hb F ps p slack
  let Y : J → Matrix I I ℂ := fun j => ((b : ℂ)⁻¹) • leftDefectNeumann
    (identityCoefficient (ps j) (p j) (slack j) • (1 : Matrix I I ℂ) +
      (oracleCoefficient (ps j) (p j) (slack j) / (α : ℂ)) • A) b
  have hf := nativeCleanSingleFrame_isometry b hb F hbe.left_isometry
  have hu := nativeCleanRelabeledWord_unitary b hb F A U α hbe ps p slack
  have hc := nativeMultiNodeRelabeled_clean_block b hb F A U α hbe ps p slack
  exact (clean_word_lcu_encoding_cost L O W Y d j₀ hmass hf hu hc).1
-/

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
