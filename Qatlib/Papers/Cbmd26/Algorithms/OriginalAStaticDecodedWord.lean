/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticAmplification

/-!
# Decoding Static Oracle Words

This module implements a change of frame for adjoint oracle words. `basisConvertedWord` adds
fixed gates around a word so that its evaluation is conjugated by a chosen matrix; when that
matrix is unitary, block encodings transfer from the transformed frame to the original frame.

For static original-oracle circuits, `originalStaticAveragePrepare` maps the computationally
tagged `originalStaticDecodedFrame` to `originalStaticFrame`. The resulting
`originalStaticDecodedWord` preserves the original block-encoding normalization and error and
adds exactly two fixed gates without increasing the query count. See [WangEtAl2026].

## Main statements

* `basisConvertedWord_blockEncoding` transports a block encoding through a unitary change of
  frame.

* `originalStaticAveragePrepare_frame` identifies the decoded and averaged frames.
* `originalStaticDecodedWord_cost` and `originalStaticDecodedWord_blockEncoding` give the
  decoded word's cost and encoding guarantee.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

section Generic
variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] [DecidableEq W] [Fintype I] in

/-- Applying a parallel copy of `D` to a frame tagged by `j₀` applies `D` to the underlying
frame while preserving the tag. -/
theorem parallelOracle_mul_tagFrame (D : Matrix W W ℂ) (F : Matrix W I ℂ) (j₀ : J) :
    parallelOracle (J := J) D * tagFrame j₀ F = tagFrame j₀ (D * F) := by
  ext ⟨j,w⟩ i
  by_cases hj : j = j₀
  · subst j
    simp [parallelOracle, select, tagFrame, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [parallelOracle, select, tagFrame, Matrix.mul_apply, Fintype.sum_prod_type, hj]

/-- Surrounds an adjoint oracle word with fixed gates implementing a change of basis by `D`, so
evaluation is conjugated by `D` and its adjoint. -/
def basisConvertedWord (D : Matrix W W ℂ) (cs : List (AdjointStep W)) : List (AdjointStep W) :=
  [.gate Dᴴ] ++ cs ++ [.gate D]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- Evaluating `basisConvertedWord D cs` gives `Dᴴ * evaluate O cs * D`. -/
theorem basisConvertedWord_evaluate (D O : Matrix W W ℂ) (cs : List (AdjointStep W)) :
    evaluate O (basisConvertedWord D cs) = Dᴴ * evaluate O cs * D := by
  simp [basisConvertedWord, evaluate_append, evaluate, instructionMatrix, Matrix.mul_assoc]

omit [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- The basis-converted word has the same oracle query count as the original word and exactly
two additional fixed gates. -/
theorem basisConvertedWord_cost (D : Matrix W W ℂ) (cs : List (AdjointStep W)) :
    adjointQueryCount (basisConvertedWord D cs) = adjointQueryCount cs ∧
    adjointGateCount (basisConvertedWord D cs) = adjointGateCount cs + 2 := by
  simp [basisConvertedWord, adjointQueryCount, adjointGateCount, Nat.add_assoc]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

/-- A unitary change of basis preserves well-formedness of an adjoint oracle word. -/
theorem basisConvertedWord_wellFormed (D : Matrix W W ℂ)
    (hD : D ∈ Matrix.unitaryGroup W ℂ) (cs : List (AdjointStep W))
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (basisConvertedWord D cs) := by
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simpa using! adjoint_unitary hD
    · exact hcs
  · simpa using! hD

omit [Fintype J] [DecidableEq J] in

/-- Transfers a block encoding from the frame `D * F` to `F` by conjugating the evaluated word
with a unitary `D`. The encoded matrix, scale, and error are preserved. -/
theorem basisConvertedWord_blockEncoding (D O : Matrix W W ℂ)
    (hD : D ∈ Matrix.unitaryGroup W ℂ) (cs : List (AdjointStep W))
    (A : Matrix I I ℂ) (F : Matrix W I ℂ) (hF : IsIsometry F) (α ε : ℝ)
    (henc : BlockEncoding A (evaluate O cs) (D * F) (D * F) α ε) :
    BlockEncoding A (evaluate O (basisConvertedWord D cs)) F F α ε := by
  rw [basisConvertedWord_evaluate]
  refine ⟨(Matrix.unitaryGroup W ℂ).mul_mem
    ((Matrix.unitaryGroup W ℂ).mul_mem (adjoint_unitary hD) henc.unitary) hD,
    hF, hF, henc.normalization_pos, henc.error_nonneg, ?_⟩
  simpa only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc] using! henc.error_le
end Generic

section Static
variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]
local instance cbmdOriginalAStaticDecodedWordInstance1 : DecidableEq (OriginalStaticLabels J) :=
  inferInstanceAs (DecidableEq (J × (Fin 4 × (Bool × (Bool × Bool)))))

/-- The static workspace matrix that prepares the response averaging register while acting in
parallel on the clean, sample, and branch labels. -/
def originalStaticAveragePrepare : Matrix (OriginalStaticSpace J W) (OriginalStaticSpace J W) ℂ :=
  parallelOracle (J := Bool)
    ((parallelOracle (J := J) (parallelOracle (J := Fin 4)
      (prepareRegister (I := Bool × (Bool × W)) (complexPrepare realPartAmplitude false)))).submatrix
        (originalStaticWorkspaceEquiv J W) (originalStaticWorkspaceEquiv J W))

/-- Embeds `R` into the static workspace with fixed sample and branch tags and all response and
clean Boolean registers tagged by `false`. -/
def originalStaticDecodedFrame (R : Matrix W I ℂ) (j₀ : J) :
    Matrix (OriginalStaticSpace J W) I ℂ :=
  tagFrame false (reindexFrame (originalStaticWorkspaceEquiv J W)
    (tagFrame j₀ (tagFrame (0 : Fin 4)
      (tagFrame false (tagFrame false (tagFrame false R))))))

omit [Fintype I] [DecidableEq I] in

/-- The static averaging preparation matrix is unitary. -/
theorem originalStaticAveragePrepare_unitary :
    originalStaticAveragePrepare (J := J) (W := W) ∈
      Matrix.unitaryGroup (OriginalStaticSpace J W) ℂ := by
  apply parallelOracle_unitary
  apply relabelGate_mem_unitary _ (originalStaticWorkspaceEquiv J W).symm
  apply parallelOracle_unitary
  apply parallelOracle_unitary
  apply prepareRegister_unitary
  apply complexPrepare_unitary
  rw [normalized_iff_inner_self]
  exact realPartAmplitude_normalized

/-- The decoded static frame is an isometry whenever the underlying system frame `R` is an
isometry. -/
theorem originalStaticDecodedFrame_isIsometry (R : Matrix W I ℂ) (hR : IsIsometry R) (j₀ : J) :
    IsIsometry (originalStaticDecodedFrame R j₀) := by
  apply tagFrame_isIsometry
  apply reindexFrame_isIsometry
  exact tagFrame_isIsometry _ _ (tagFrame_isIsometry _ _
    (tagFrame_isIsometry _ _ (tagFrame_isIsometry _ _ (tagFrame_isIsometry _ _ hR))))

/-- The static averaging preparation maps `originalStaticDecodedFrame` exactly to
`originalStaticFrame`. -/
theorem originalStaticAveragePrepare_frame (R : Matrix W I ℂ) (j₀ : J) :
    originalStaticAveragePrepare * originalStaticDecodedFrame R j₀ = originalStaticFrame R j₀ := by
  unfold originalStaticAveragePrepare originalStaticDecodedFrame originalStaticFrame
  rw [parallelOracle_mul_tagFrame]
  congr 1
  unfold reindexFrame
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  rw [parallelOracle_mul_tagFrame, parallelOracle_mul_tagFrame, tagFrame_eq false]
  rw [← Matrix.mul_assoc, prepareRegister_mul_prepareLift, complexPrepare_mulVec_ket]
  rfl

/-- Converts the static outer oracle word to the decoded frame using
`originalStaticAveragePrepare` as its change of basis. -/
def originalStaticDecodedWord (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (c : J → ℂ) (j₀ : J) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    List (AdjointStep (OriginalStaticSpace J W)) :=
  basisConvertedWord originalStaticAveragePrepare (originalStaticOuterWord R α Λ s c j₀ d base zs)

omit [DecidableEq I] in

/-- The decoded static word uses twice the total phase-list length in oracle queries and
thirteen times that length plus eighteen fixed gates. -/
theorem originalStaticDecodedWord_cost (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (c : J → ℂ) (j₀ : J) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    adjointQueryCount (originalStaticDecodedWord R α Λ s c j₀ d base zs) = 2 * ∑ k, (zs k).length ∧
    adjointGateCount (originalStaticDecodedWord R α Λ s c j₀ d base zs) = 13 * (∑ k, (zs k).length) + 18 := by
  obtain ⟨hq,hg⟩ := originalStaticOuterWord_cost R α Λ s c j₀ d base zs
  obtain ⟨hdq,hdg⟩ := basisConvertedWord_cost originalStaticAveragePrepare
    (originalStaticOuterWord R α Λ s c j₀ d base zs)
  exact ⟨hdq.trans hq, hdg.trans (by rw [hg])⟩

/-- Transfers the static outer word's block encoding to the decoded word and decoded frame. The
encoded matrix, scale, and error remain the same when `R` is an isometry. -/
theorem originalStaticDecodedWord_blockEncoding (U : Matrix W W ℂ)
    (R : Matrix W I ℂ) (hR : IsIsometry R) (α Λ : ℝ) (s : J → ℝ)
    (c : J → ℂ) (j₀ : J) (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ)
    (A : Matrix I I ℂ) (β ε : ℝ)
    (henc : BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := OriginalStaticLabels J) U))
        (originalStaticOuterWord R α Λ s c j₀ d base zs))
      (originalStaticFrame R j₀) (originalStaticFrame R j₀) β ε) :
    BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := OriginalStaticLabels J) U))
        (originalStaticDecodedWord R α Λ s c j₀ d base zs))
      (originalStaticDecodedFrame R j₀) (originalStaticDecodedFrame R j₀) β ε := by
  apply basisConvertedWord_blockEncoding _ _ originalStaticAveragePrepare_unitary
    _ _ _ (originalStaticDecodedFrame_isIsometry R hR j₀)
  simpa only [originalStaticAveragePrepare_frame] using! henc
end Static
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
