/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CommonNormalizationBridge
import Qatlib.Papers.Cbmd26.Algorithms.QSVTBridge
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix

variable {J H I : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I]

theorem evaluate_indexedParallelQSVT (U : J → Matrix H H ℂ)
    (P Q : Matrix H H ℂ) (base : J → ℂ) (zs : List (J → ℂ)) :
    evaluate (select U) (compileParallelQSVT P Q base zs) =
      select (fun j => phasedAlternating (U j) P Q (base j) (zs.map (fun z => z j))) := by
  induction zs generalizing U P Q with
  | nil => simp [compileParallelQSVT, evaluate, instructionMatrix, phasedAlternating]
  | cons z zs ih =>
    simp only [compileParallelQSVT, evaluate, instructionMatrix, evaluate_swapQueries,
      parallel_select_adjoint, ih]
    rw [parallel_select_mul, parallel_select_mul]
    congr 1
    funext j
    simp [phasedAlternating, Matrix.mul_assoc]

def indexedRealPartWord (P : Matrix H H ℂ) (base : J → ℂ) (zs : List (J → ℂ)) :
    List (AdjointStep (J × (Bool × H))) :=
  reindexAdjointWord (Equiv.prodAssoc J Bool H).symm
    (compileParallelQSVT P P
      (fun jb : J × Bool => conjugateParallelPhase (base jb.1) jb.2)
      (zs.map (fun z jb => conjugateParallelPhase (z jb.1) jb.2)))

theorem indexedRealPartWord_evaluate (U : J → Matrix H H ℂ)
    (P : Matrix H H ℂ) (base : J → ℂ) (zs : List (J → ℂ)) :
    evaluate (select (fun j => parallelOracle (J := Bool) (U j)))
        (indexedRealPartWord P base zs) =
      select (fun j => realPartQSVT (U j) P P (base j) (zs.map (fun z => z j))) := by
  have ho : select (fun j => parallelOracle (J := Bool) (U j)) =
      (select (fun jb : J × Bool => U jb.1)).submatrix
        (Equiv.prodAssoc J Bool H).symm (Equiv.prodAssoc J Bool H).symm := by
    ext ⟨j,b,i⟩ ⟨k,c,l⟩
    by_cases hj : j = k <;> by_cases hb : b = c <;>
      simp [parallelOracle, select, hj, hb]
  rw [ho, indexedRealPartWord, reindexAdjointWord_evaluate, evaluate_indexedParallelQSVT]
  ext ⟨j,b,i⟩ ⟨k,c,l⟩
  by_cases hj : j = k
  · subst k
    by_cases hb : b = c
    · subst c
      cases b <;> simp [select, realPartQSVT, averageCircuit, conjugateParallelPhase,
        List.map_map, Function.comp_def]
    · simp [select, realPartQSVT, averageCircuit, hb]
  · simp [select, realPartQSVT, averageCircuit, hj]

omit [Fintype J] [Fintype H] [Fintype I] [DecidableEq I] in

theorem indexedRealPartWord_cost (P : Matrix H H ℂ)
    (base : J → ℂ) (zs : List (J → ℂ)) :
    adjointQueryCount (indexedRealPartWord P base zs) = zs.length ∧
    adjointGateCount (indexedRealPartWord P base zs) = zs.length + 1 := by
  simp [indexedRealPartWord, (reindexAdjointWord_cost _ _).1,
    (reindexAdjointWord_cost _ _).2, queryCount_compileParallelQSVT,
    gateCount_compileParallelQSVT]

theorem indexedRealPartWord_wellFormed {P : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (base : J → ℂ) (hb : ∀ j, IsPhase (base j))
    (zs : List (J → ℂ)) (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit (indexedRealPartWord P base zs) := by
  apply reindexAdjointWord_wellFormed
  apply compileParallelQSVT_wellFormed hP hP
  · intro ⟨j,b⟩
    cases b <;> simpa [conjugateParallelPhase, IsPhase, mul_comm] using hb j
  · intro z hz ⟨j,b⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    cases b <;> simpa [conjugateParallelPhase, IsPhase, mul_comm] using hzs w hw j

def indexedHermitianResponseWord (F : Matrix H I ℂ) (d : ℕ)
    (base : J → ℂ) (zs : List (J → ℂ)) :
    List (AdjointStep (J × (Bool × H))) :=
  if d % 2 = 1 then indexedRealPartWord (rangeProjector F) base zs
  else (indexedRealPartWord (rangeProjector F) base zs).map swapQueries

omit [DecidableEq I] in

theorem indexedHermitianResponseWord_evaluate (U : J → Matrix H H ℂ)
    (F : Matrix H I ℂ) (d : ℕ) (base : J → ℂ) (zs : List (J → ℂ)) :
    evaluate (select (fun j => parallelOracle (J := Bool) (U j)))
        (indexedHermitianResponseWord F d base zs) =
      select (fun j => evaluate (parallelOracle (U j))
        (hermitianResponseWord F d (base j) (zs.map (fun z => z j)))) := by
  unfold indexedHermitianResponseWord hermitianResponseWord
  split_ifs
  · simp only [indexedRealPartWord_evaluate, evaluate_compileRealPartQSVT]
  · simp only [evaluate_swapQueries, parallel_select_adjoint, parallelOracle_adjoint,
      indexedRealPartWord_evaluate, evaluate_compileRealPartQSVT]

omit [Fintype J] [Fintype H] [DecidableEq I] in

theorem indexedHermitianResponseWord_cost (F : Matrix H I ℂ) (d : ℕ)
    (base : J → ℂ) (zs : List (J → ℂ)) :
    adjointQueryCount (indexedHermitianResponseWord F d base zs) = zs.length ∧
    adjointGateCount (indexedHermitianResponseWord F d base zs) = zs.length + 1 := by
  unfold indexedHermitianResponseWord
  split_ifs <;> simpa using indexedRealPartWord_cost (rangeProjector F) base zs

theorem indexedHermitianResponseWord_wellFormed (F : Matrix H I ℂ) (hF : IsIsometry F)
    (d : ℕ) (base : J → ℂ) (hb : ∀ j, IsPhase (base j))
    (zs : List (J → ℂ)) (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit (indexedHermitianResponseWord F d base zs) := by
  have hw := indexedRealPartWord_wellFormed (rangeProjector_isOrthogonalProjector hF)
    base hb zs hzs
  unfold indexedHermitianResponseWord
  split_ifs
  · exact hw
  · exact hw.swapQueries

def expandedIndexedResponseWord (body : List (AdjointStep (J × H)))
    (F : Matrix H I ℂ) (d : ℕ) (base : J → ℂ) (zs : List (J → ℂ)) :
    List (AdjointStep (J × (Bool × H))) :=
  substituteAdjointCircuit (insertPaddingWord body)
    (indexedHermitianResponseWord F d base zs)

omit [DecidableEq I] in

theorem expandedIndexedResponseWord_evaluate (O : Matrix H H ℂ)
    (body : List (AdjointStep (J × H))) (U : J → Matrix H H ℂ)
    (he : evaluate (parallelOracle O) body = select U)
    (F : Matrix H I ℂ) (d : ℕ) (base : J → ℂ) (zs : List (J → ℂ)) :
    evaluate (parallelOracle (J := J) (parallelOracle (J := Bool) O))
        (expandedIndexedResponseWord body F d base zs) =
      select (fun j => evaluate (parallelOracle (U j))
        (hermitianResponseWord F d (base j) (zs.map (fun z => z j)))) := by
  unfold expandedIndexedResponseWord
  rw [(substitute_adjoint_evaluate_cost _ _ _).1,
    insertPaddingWord_evaluate O body U he, indexedHermitianResponseWord_evaluate]

omit [DecidableEq I] in

theorem expandedIndexedResponseWord_cost (body : List (AdjointStep (J × H)))
    (F : Matrix H I ℂ) (d : ℕ) (base : J → ℂ) (zs : List (J → ℂ)) :
    adjointQueryCount (expandedIndexedResponseWord body F d base zs) =
      zs.length * adjointQueryCount body ∧
    adjointGateCount (expandedIndexedResponseWord body F d base zs) =
      zs.length + 1 + zs.length * adjointGateCount body := by
  obtain ⟨_, hq, hg, _⟩ := substitute_adjoint_evaluate_cost
    (1 : Matrix (J × (Bool × H)) (J × (Bool × H)) ℂ)
    (insertPaddingWord body) (indexedHermitianResponseWord F d base zs)
  rw [(indexedHermitianResponseWord_cost F d base zs).1, (insertPaddingWord_cost body).1] at hq
  rw [(indexedHermitianResponseWord_cost F d base zs).1,
    (indexedHermitianResponseWord_cost F d base zs).2, (insertPaddingWord_cost body).2] at hg
  exact ⟨hq, hg⟩

theorem expandedIndexedResponseWord_wellFormed (body : List (AdjointStep (J × H)))
    (hbody : WellFormedAdjointCircuit body) (F : Matrix H I ℂ) (hF : IsIsometry F)
    (d : ℕ) (base : J → ℂ) (hb : ∀ j, IsPhase (base j))
    (zs : List (J → ℂ)) (hzs : ∀ z ∈ zs, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit (expandedIndexedResponseWord body F d base zs) := by
  exact (substitute_adjoint_evaluate_cost
    (1 : Matrix (J × (Bool × H)) (J × (Bool × H)) ℂ) _ _).2.2.2
    (insertPaddingWord_wellFormed hbody)
    (indexedHermitianResponseWord_wellFormed F hF d base hb zs hzs)

def outerCoefficientWord (c : J → ℂ) (j₀ : J)
    (cs : List (AdjointStep (J × H))) : List (AdjointStep (J × H)) :=
  [.gate (prepareRegister (I := H) (coefficientPrepare c j₀))ᴴ,
   .gate (select (phaseAbsorbed c (fun _ => (1 : Matrix H H ℂ))))] ++ cs ++
  [.gate (prepareRegister (I := H) (coefficientPrepare c j₀))]

theorem outerCoefficientWord_evaluate (c : J → ℂ) (j₀ : J)
    (O : Matrix (J × H) (J × H) ℂ) (cs : List (AdjointStep (J × H)))
    (U : J → Matrix H H ℂ) (he : evaluate O cs = select U) :
    evaluate O (outerCoefficientWord c j₀ cs) = coefficientLCUUnitary c U j₀ := by
  have hphase : select (phaseAbsorbed c (fun _ => (1 : Matrix H H ℂ))) * select U =
      select (phaseAbsorbed c U) := by
    rw [parallel_select_mul]
    congr 1
    funext j
    simp [phaseAbsorbed]
  simp only [outerCoefficientWord, evaluate_append, evaluate, instructionMatrix,
    Matrix.mul_one, he]
  rw [Matrix.mul_assoc _ _ (select U), hphase]
  rfl

omit [Fintype H] [Fintype I] [DecidableEq I] in

theorem outerCoefficientWord_cost (c : J → ℂ) (j₀ : J)
    (cs : List (AdjointStep (J × H))) :
    adjointQueryCount (outerCoefficientWord c j₀ cs) = adjointQueryCount cs ∧
    adjointGateCount (outerCoefficientWord c j₀ cs) = adjointGateCount cs + 3 := by
  simp [outerCoefficientWord, adjointQueryCount, adjointGateCount]

theorem outerCoefficientWord_wellFormed (c : J → ℂ) (j₀ : J)
    (hc : 0 < coefficientMass c) {cs : List (AdjointStep (J × H))}
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (outerCoefficientWord c j₀ cs) := by
  have hp := prepareRegister_unitary (I := H) (coefficientPrepare_unitary c j₀ hc)
  unfold outerCoefficientWord
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨adjoint_unitary hp, select_unitary _ (phaseAbsorbed_unitary c _
        (fun _ => (Matrix.unitaryGroup H ℂ).one_mem))⟩
    · exact hcs
  · simpa using hp

theorem counted_outer_lcu_encoding (c : J → ℂ) (j₀ : J)
    (O : Matrix (J × H) (J × H) ℂ) (cs : List (AdjointStep (J × H)))
    (U : J → Matrix H H ℂ) (he : evaluate O cs = select U)
    (hcs : WellFormedAdjointCircuit cs) (A : J → Matrix I I ℂ)
    (F : Matrix H I ℂ) (α ε : J → ℝ)
    (henc : ∀ j, BlockEncoding (A j) (U j) F F (α j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c α)) :
    WellFormedAdjointCircuit (outerCoefficientWord (scaledLCUCoefficients c α) j₀ cs) ∧
    BlockEncoding (∑ j, c j • A j)
      (evaluate O (outerCoefficientWord (scaledLCUCoefficients c α) j₀ cs))
      (tagFrame j₀ F) (tagFrame j₀ F) (∑ j, ‖c j‖ * α j) (∑ j, ‖c j‖ * ε j) ∧
    adjointQueryCount (outerCoefficientWord (scaledLCUCoefficients c α) j₀ cs) =
      adjointQueryCount cs ∧
    adjointGateCount (outerCoefficientWord (scaledLCUCoefficients c α) j₀ cs) =
      adjointGateCount cs + 3 := by
  refine ⟨outerCoefficientWord_wellFormed _ _ hmass hcs, ?_, outerCoefficientWord_cost _ _ _⟩
  rw [outerCoefficientWord_evaluate _ _ O cs U he]
  exact scaled_approximate_lcu_encoding j₀ A U F F c α ε henc hmass

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
