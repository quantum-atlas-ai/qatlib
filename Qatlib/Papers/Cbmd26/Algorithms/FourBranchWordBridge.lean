/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.IndexedQSVTBridge
import Qatlib.Papers.Cbmd26.Algorithms.ControlledAccessBridge
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix

def fourLabelEquiv : Fin 4 ≃ Bool × Bool where
  toFun j := (decide (2 ≤ j.val), decide (j.val % 2 = 1))
  invFun b := ⟨(if b.1 then 2 else 0) + (if b.2 then 1 else 0), by
    rcases b with ⟨a,b⟩; cases a <;> cases b <;> decide⟩
  left_inv j := by fin_cases j <;> rfl
  right_inv b := by rcases b with ⟨a,b⟩; cases a <;> cases b <;> rfl

def fourWorkspaceEquiv (H : Type) : Fin 4 × H ≃ Bool × (Bool × H) :=
  (Equiv.prodCongr fourLabelEquiv (Equiv.refl H)).trans (Equiv.prodAssoc Bool Bool H)

variable {H : Type} [Fintype H] [DecidableEq H]

def compileFourSelected (cs : Fin 4 → List (AdjointStep H)) :
    List (AdjointStep (Fin 4 × H)) :=
  reindexAdjointWord (fourWorkspaceEquiv H)
    (compileSelected (compileSelected (cs 3) (cs 2)) (compileSelected (cs 1) (cs 0)))

def fourActive (j : Fin 4) : Bool := decide (j = 3)

theorem compileFourSelected_evaluate (U : Matrix H H ℂ)
    (cs : Fin 4 → List (AdjointStep H)) :
    evaluate (maskedOracle fourActive U) (compileFourSelected cs) =
      select (fun j => evaluate U (cs j)) := by
  have ho : maskedOracle fourActive U =
      (controlOracle (controlOracle U)).submatrix
        (fourWorkspaceEquiv H) (fourWorkspaceEquiv H) := by
    ext ⟨j,i⟩ ⟨k,l⟩
    fin_cases j <;> fin_cases k <;>
      simp [maskedOracle, fourActive, select, controlOracle, fourWorkspaceEquiv,
        fourLabelEquiv, Matrix.one_apply]
  rw [ho, compileFourSelected, reindexAdjointWord_evaluate]
  simp only [evaluate_compileSelected]
  ext ⟨j,i⟩ ⟨k,l⟩
  fin_cases j <;> fin_cases k <;>
    simp [select, fourWorkspaceEquiv, fourLabelEquiv]

omit [Fintype H] in

theorem compileFourSelected_cost (cs : Fin 4 → List (AdjointStep H)) :
    adjointQueryCount (compileFourSelected cs) = ∑ j, adjointQueryCount (cs j) ∧
    adjointGateCount (compileFourSelected cs) = (∑ j, adjointGateCount (cs j)) + 6 := by
  simp [compileFourSelected, (reindexAdjointWord_cost _ _).1,
    (reindexAdjointWord_cost _ _).2, queryCount_compileSelected, gateCount_compileSelected,
    Fin.sum_univ_succ]
  omega

theorem compileFourSelected_wellFormed (cs : Fin 4 → List (AdjointStep H))
    (hcs : ∀ j, WellFormedAdjointCircuit (cs j)) :
    WellFormedAdjointCircuit (compileFourSelected cs) :=
  reindexAdjointWord_wellFormed _ (compileSelected_wellFormed
    (compileSelected_wellFormed (hcs 3) (hcs 2))
    (compileSelected_wellFormed (hcs 1) (hcs 0)))

def fourCoefficientWord (c : Fin 4 → ℂ) (cs : Fin 4 → List (AdjointStep H)) :
    List (AdjointStep (Fin 4 × H)) :=
  outerCoefficientWord c 0 (compileFourSelected cs)

theorem fourCoefficientWord_evaluate (U : Matrix H H ℂ) (c : Fin 4 → ℂ)
    (cs : Fin 4 → List (AdjointStep H)) :
    evaluate (maskedOracle fourActive U) (fourCoefficientWord c cs) =
      coefficientLCUUnitary c (fun j => evaluate U (cs j)) 0 :=
  outerCoefficientWord_evaluate _ _ _ _ _ (compileFourSelected_evaluate U cs)

omit [Fintype H] in

theorem fourCoefficientWord_cost (c : Fin 4 → ℂ) (cs : Fin 4 → List (AdjointStep H)) :
    adjointQueryCount (fourCoefficientWord c cs) = ∑ j, adjointQueryCount (cs j) ∧
    adjointGateCount (fourCoefficientWord c cs) = (∑ j, adjointGateCount (cs j)) + 9 := by
  obtain ⟨hq, hg⟩ := outerCoefficientWord_cost c 0 (compileFourSelected cs)
  rw [(compileFourSelected_cost cs).1] at hq
  rw [(compileFourSelected_cost cs).2] at hg
  exact ⟨hq, hg.trans (by omega)⟩

theorem fourCoefficientWord_wellFormed (c : Fin 4 → ℂ) (hc : 0 < coefficientMass c)
    (cs : Fin 4 → List (AdjointStep H)) (hcs : ∀ j, WellFormedAdjointCircuit (cs j)) :
    WellFormedAdjointCircuit (fourCoefficientWord c cs) :=
  outerCoefficientWord_wellFormed c 0 hc (compileFourSelected_wellFormed cs hcs)

def cleanFourCoefficientWord (c : Fin 4 → ℂ) (cs : Fin 4 → List (AdjointStep H)) :
    List (AdjointStep (Bool × (Fin 4 × H))) :=
  cleanMaskedWord fourActive (fourCoefficientWord c cs)

theorem cleanFourCoefficientWord_cost (c : Fin 4 → ℂ)
    (cs : Fin 4 → List (AdjointStep H)) :
    adjointQueryCount (cleanFourCoefficientWord c cs) = ∑ j, adjointQueryCount (cs j) ∧
    adjointGateCount (cleanFourCoefficientWord c cs) =
      (∑ j, adjointGateCount (cs j)) + 9 + 2 * (∑ j, adjointQueryCount (cs j)) := by
  obtain ⟨hq, hg⟩ := cleanMaskedWord_cost fourActive (fourCoefficientWord c cs)
  rw [(fourCoefficientWord_cost c cs).1] at hq
  rw [(fourCoefficientWord_cost c cs).1, (fourCoefficientWord_cost c cs).2] at hg
  exact ⟨hq, hg⟩

theorem cleanFourCoefficientWord_blockEncoding {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (c : Fin 4 → ℂ) (hc : 0 < coefficientMass c)
    (cs : Fin 4 → List (AdjointStep H)) (hcs : ∀ j, WellFormedAdjointCircuit (cs j))
    (A : Matrix I I ℂ) (F : Matrix (Fin 4 × H) I ℂ) (α ε : ℝ)
    (henc : BlockEncoding A (coefficientLCUUnitary c (fun j => evaluate U (cs j)) 0) F F α ε) :
    WellFormedAdjointCircuit (cleanFourCoefficientWord c cs) ∧
    BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := Fin 4) U)) (cleanFourCoefficientWord c cs))
      (tagFrame false F) (tagFrame false F) α ε ∧
    adjointQueryCount (cleanFourCoefficientWord c cs) = ∑ j, adjointQueryCount (cs j) ∧
    adjointGateCount (cleanFourCoefficientWord c cs) =
      (∑ j, adjointGateCount (cs j)) + 9 + 2 * (∑ j, adjointQueryCount (cs j)) := by
  have hb : BlockEncoding A (evaluate (maskedOracle fourActive U) (fourCoefficientWord c cs))
      F F α ε := by rw [fourCoefficientWord_evaluate]; exact henc
  obtain ⟨hw, he, _, _⟩ := cleanMaskedWord_blockEncoding fourActive U hU
    (fourCoefficientWord c cs) (fourCoefficientWord_wellFormed c hc cs hcs) A F α ε hb
  exact ⟨hw, he, cleanFourCoefficientWord_cost c cs⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
