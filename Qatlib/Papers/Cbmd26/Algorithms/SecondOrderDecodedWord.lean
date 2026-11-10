/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CosineSecondOrderConsumer
import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticDecodedWord
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

section Generic
variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
def basisConvertedPreparedWord (D : Matrix W W ℂ) (cs : List (PreparedStep W)) :
    List (PreparedStep W) := [.gate Dᴴ] ++ cs ++ [.gate D]

theorem basisConvertedPreparedWord_evaluate (D O1 O2 : Matrix W W ℂ)
    (cs : List (PreparedStep W)) :
    evaluatePrepared O1 O2 (basisConvertedPreparedWord D cs) =
      Dᴴ * evaluatePrepared O1 O2 cs * D := by
  simp [basisConvertedPreparedWord, evaluatePrepared_append, evaluatePrepared,
    preparedInstruction, Matrix.mul_assoc]

omit [Fintype W] [DecidableEq W] in

theorem basisConvertedPreparedWord_cost (D : Matrix W W ℂ) (cs : List (PreparedStep W)) :
    preparedDataQueries (basisConvertedPreparedWord D cs) = preparedDataQueries cs ∧
    preparedInputQueries (basisConvertedPreparedWord D cs) = preparedInputQueries cs ∧
    preparedFixedGates (basisConvertedPreparedWord D cs) = preparedFixedGates cs + 2 := by
  simp [basisConvertedPreparedWord, Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.data_append, Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.input_append,
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.gates_append, preparedDataQueries, preparedInputQueries, preparedFixedGates,
    Nat.add_assoc]

theorem basisConvertedPreparedWord_valid (D : Matrix W W ℂ)
    (hD : D ∈ Matrix.unitaryGroup W ℂ) (cs : List (PreparedStep W))
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (basisConvertedPreparedWord D cs) := by
  intro c hc
  simp only [basisConvertedPreparedWord, List.mem_append, List.mem_singleton] at hc
  rcases hc with (rfl | hc) | rfl
  · exact adjoint_unitary hD
  · exact hcs c hc
  · exact hD

theorem basisConvertedPreparedWord_blockEncoding (D O1 O2 : Matrix W W ℂ)
    (hD : D ∈ Matrix.unitaryGroup W ℂ) (cs : List (PreparedStep W))
    (A : Matrix I I ℂ) (F : Matrix W I ℂ) (hF : IsIsometry F) (α ε : ℝ)
    (henc : BlockEncoding A (evaluatePrepared O1 O2 cs) (D * F) (D * F) α ε) :
    BlockEncoding A (evaluatePrepared O1 O2 (basisConvertedPreparedWord D cs)) F F α ε := by
  rw [basisConvertedPreparedWord_evaluate]
  refine ⟨(Matrix.unitaryGroup W ℂ).mul_mem
    ((Matrix.unitaryGroup W ℂ).mul_mem (adjoint_unitary hD) henc.unitary) hD,
    hF, hF, henc.normalization_pos, henc.error_nonneg, ?_⟩
  simpa only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc] using! henc.error_le
end Generic

section Actual
variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]
abbrev SecondOrderSpace (J W : Type) := Bool × (PreparedPredicateLabels (Fin 4) J Bool × W)

def secondOrderAveragePrepare : Matrix (SecondOrderSpace J W) (SecondOrderSpace J W) ℂ :=
  parallelOracle (J := Bool)
    ((parallelOracle (J := Fin 4 × J)
      (prepareRegister (I := Bool × W) (complexPrepare realPartAmplitude false))).submatrix
      (preparedPredicateWorkspaceEquiv (Fin 4) J Bool W)
      (preparedPredicateWorkspaceEquiv (Fin 4) J Bool W))

def secondOrderDecodedFrame (j₀ : J) (F : Matrix W I ℂ) :
    Matrix (SecondOrderSpace J W) I ℂ :=
  tagFrame false (reindexFrame (preparedPredicateWorkspaceEquiv (Fin 4) J Bool W)
    (tagFrame (0, j₀) (tagFrame false (tagFrame false F))))

omit [Fintype I] [DecidableEq I] in

theorem secondOrderAveragePrepare_unitary :
    secondOrderAveragePrepare (J := J) (W := W) ∈ Matrix.unitaryGroup (SecondOrderSpace J W) ℂ := by
  apply parallelOracle_unitary
  apply relabelGate_mem_unitary _ (preparedPredicateWorkspaceEquiv (Fin 4) J Bool W).symm
  apply parallelOracle_unitary
  apply prepareRegister_unitary
  apply complexPrepare_unitary
  rw [normalized_iff_inner_self]
  exact realPartAmplitude_normalized

theorem secondOrderDecodedFrame_isIsometry (j₀ : J) (F : Matrix W I ℂ) (hF : IsIsometry F) :
    IsIsometry (secondOrderDecodedFrame j₀ F) := by
  apply tagFrame_isIsometry
  apply reindexFrame_isIsometry
  exact tagFrame_isIsometry _ _ (tagFrame_isIsometry _ _ (tagFrame_isIsometry _ _ hF))

theorem secondOrderAveragePrepare_frame (j₀ : J) (F : Matrix W I ℂ) :
    secondOrderAveragePrepare * secondOrderDecodedFrame j₀ F = secondOrderFrame j₀ F := by
  unfold secondOrderAveragePrepare secondOrderDecodedFrame secondOrderFrame
  rw [parallelOracle_mul_tagFrame]
  congr 1
  unfold reindexFrame
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  rw [parallelOracle_mul_tagFrame, tagFrame_eq false]
  rw [← Matrix.mul_assoc, prepareRegister_mul_prepareLift, complexPrepare_mulVec_ket]
  rfl

def decodedSecondOrderWord (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)) (βL βH : ℝ) (s : J → ℝ) :
    List (PreparedStep (SecondOrderSpace J W)) :=
  basisConvertedPreparedWord secondOrderAveragePrepare (secondOrderWord c j₀ F D base zs βL βH s)

omit [Fintype W] [DecidableEq I] in

theorem decodedSecondOrderWord_cost (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (hlen : ∀ k, (zs k).length = uniformBranchDegree D k) (βL βH : ℝ) (s : J → ℝ) :
    preparedDataQueries (decodedSecondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
    preparedInputQueries (decodedSecondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
    preparedFixedGates (decodedSecondOrderWord c j₀ F D base zs βL βH s) = 80 * D + 35 := by
  have hh := basisConvertedPreparedWord_cost secondOrderAveragePrepare
    (secondOrderWord c j₀ F D base zs βL βH s)
  have hc := secondOrderWord_cost c j₀ F D base zs hlen βL βH s
  exact ⟨hh.1.trans hc.1, hh.2.1.trans hc.2.1, hh.2.2.trans (by rw [hc.2.2])⟩

omit [DecidableEq I] in

theorem decodedSecondOrderWord_valid (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)) (βL βH : ℝ) (s : J → ℝ)
    (hcs : PreparedCircuitValid (secondOrderWord c j₀ F D base zs βL βH s)) :
    PreparedCircuitValid (decodedSecondOrderWord c j₀ F D base zs βL βH s) :=
  basisConvertedPreparedWord_valid _ secondOrderAveragePrepare_unitary _ hcs

theorem decodedSecondOrderWord_blockEncoding (c : J → ℂ) (j₀ : J) (F : Matrix W I ℂ)
    (hF : IsIsometry F) (D : ℕ) (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (βL βH : ℝ) (s : J → ℝ) (O1 O2 : Matrix (SecondOrderSpace J W) (SecondOrderSpace J W) ℂ)
    (A : Matrix I I ℂ) (α ε : ℝ)
    (henc : BlockEncoding A (evaluatePrepared O1 O2 (secondOrderWord c j₀ F D base zs βL βH s))
      (secondOrderFrame j₀ F) (secondOrderFrame j₀ F) α ε) :
    BlockEncoding A (evaluatePrepared O1 O2 (decodedSecondOrderWord c j₀ F D base zs βL βH s))
      (secondOrderDecodedFrame j₀ F) (secondOrderDecodedFrame j₀ F) α ε := by
  apply basisConvertedPreparedWord_blockEncoding _ _ _ secondOrderAveragePrepare_unitary
    _ _ _ (secondOrderDecodedFrame_isIsometry j₀ F hF)
  simpa only [secondOrderAveragePrepare_frame] using! henc
end Actual
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
