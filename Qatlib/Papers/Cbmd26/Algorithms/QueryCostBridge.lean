/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.InputBridge
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Foundations.InstrumentCore.Measurement
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

variable {W : Type} [Fintype W] [DecidableEq W]

def coefficientLabelPhase (d : Bool → ℂ) : Matrix (Bool × W) (Bool × W) ℂ :=
  select (phaseAbsorbed d (fun _ => (1 : Matrix W W ℂ)))

theorem coefficientLabelPhase_unitary (d : Bool → ℂ) :
    coefficientLabelPhase (W := W) d ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
  select_unitary _ (phaseAbsorbed_unitary d (fun _ => (1 : Matrix W W ℂ))
    (fun _ => (Matrix.unitaryGroup W ℂ).one_mem))

def coefficientAdjointWord (d : Bool → ℂ) (j₀ : Bool) :
    List (AdjointStep (Bool × W)) :=
  [.gate (prepareRegister (I := W) (coefficientPrepare d j₀))ᴴ,
    .gate (coefficientLabelPhase d)] ++
    compileSelected ([.backward] : List (AdjointStep W)) [.forward] ++
    [.gate (prepareRegister (coefficientPrepare d j₀))]

theorem coefficientAdjointWord_evaluate (d : Bool → ℂ) (j₀ : Bool)
    (U : Matrix W W ℂ) :
    evaluate (controlOracle U) (coefficientAdjointWord d j₀) =
      coefficientLCUUnitary d (oracleAdjointPair U) j₀ := by
  have hphase : coefficientLabelPhase d * select (oracleAdjointPair U) =
      select (phaseAbsorbed d (oracleAdjointPair U)) := by
    rw [coefficientLabelPhase, parallel_select_mul]
    congr 1
    funext b
    simp [phaseAbsorbed]
  calc
    _ = (prepareRegister (coefficientPrepare d j₀))ᴴ *
        (coefficientLabelPhase d * select (oracleAdjointPair U)) *
        prepareRegister (coefficientPrepare d j₀) := by
      simp [coefficientAdjointWord, evaluate_append, evaluate_compileSelected,
        evaluate, instructionMatrix, Matrix.mul_assoc]
      rfl
    _ = _ := by rw [hphase]; rfl

omit [Fintype W] in

theorem coefficientAdjointWord_cost (d : Bool → ℂ) (j₀ : Bool) :
    adjointQueryCount (coefficientAdjointWord (W := W) d j₀) = 2 ∧
      adjointGateCount (coefficientAdjointWord (W := W) d j₀) = 5 := by
  simp [coefficientAdjointWord, queryCount_compileSelected, gateCount_compileSelected,
    adjointQueryCount, adjointGateCount]

theorem coefficientAdjointWord_wellFormed (d : Bool → ℂ) (j₀ : Bool)
    (hd : 0 < coefficientMass d) :
    WellFormedAdjointCircuit (coefficientAdjointWord (W := W) d j₀) := by
  have hp := prepareRegister_unitary (I := W) (coefficientPrepare_unitary d j₀ hd)
  have hs : WellFormedAdjointCircuit
      (compileSelected ([.backward] : List (AdjointStep W)) [.forward]) :=
    compileSelected_wellFormed (by simp) (by simp)
  unfold coefficientAdjointWord
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨adjoint_unitary hp, coefficientLabelPhase_unitary d⟩
    · exact hs
  · simpa using hp

def sampleInputWord (α s : ℝ) : List (AdjointStep (Bool × W)) :=
  coefficientAdjointWord (scaledLCUCoefficients (sampleCoefficients s) (fun _ => α)) false

def firstOrderInputWord (α s : ℝ) : List (AdjointStep (Bool × W)) :=
  coefficientAdjointWord (scaledLCUCoefficients (firstOrderCoefficients s) (fun _ => α)) false

theorem sampleInputWord_evaluate (α s : ℝ) (U : Matrix W W ℂ) :
    evaluate (controlOracle U) (sampleInputWord α s) = sampleInputUnitary U α s :=
  coefficientAdjointWord_evaluate _ _ U

theorem firstOrderInputWord_evaluate (α s : ℝ) (U : Matrix W W ℂ) :
    evaluate (controlOracle U) (firstOrderInputWord α s) = firstOrderInputUnitary U α s :=
  coefficientAdjointWord_evaluate _ _ U

omit [Fintype W] in

theorem sampleInputWord_cost (α s : ℝ) :
    adjointQueryCount (sampleInputWord (W := W) α s) = 2 ∧
      adjointGateCount (sampleInputWord (W := W) α s) = 5 :=
  coefficientAdjointWord_cost _ _

omit [Fintype W] in

theorem firstOrderInputWord_cost (α s : ℝ) :
    adjointQueryCount (firstOrderInputWord (W := W) α s) = 2 ∧
      adjointGateCount (firstOrderInputWord (W := W) α s) = 5 :=
  coefficientAdjointWord_cost _ _

theorem sampleInputWord_wellFormed (α s : ℝ) (hα : 0 < α) :
    WellFormedAdjointCircuit (sampleInputWord (W := W) α s) := by
  apply coefficientAdjointWord_wellFormed
  rw [sample_scaled_coefficient_mass s α hα]
  exact mul_pos hα (Real.sqrt_pos.2 (by positivity))

theorem firstOrderInputWord_wellFormed (α s : ℝ) (hα : 0 < α) :
    WellFormedAdjointCircuit (firstOrderInputWord (W := W) α s) := by
  apply coefficientAdjointWord_wellFormed
  rw [(scaled_lcu_coefficient_mass (firstOrderCoefficients s) (fun _ => α)
    (fun _ => hα)).1, ← Finset.sum_mul, first_order_coefficient_weight]
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) hα

theorem sampleInputWord_substitute (α s : ℝ) (U : Matrix W W ℂ)
    (cs : List (AdjointStep (Bool × W))) :
    evaluate (controlOracle U) (substituteAdjointCircuit (sampleInputWord α s) cs) =
        evaluate (sampleInputUnitary U α s) cs ∧
      adjointQueryCount (substituteAdjointCircuit (sampleInputWord α s) cs) =
        2 * adjointQueryCount cs ∧
      adjointGateCount (substituteAdjointCircuit (sampleInputWord α s) cs) =
        adjointGateCount cs + 5 * adjointQueryCount cs ∧
      (0 < α → WellFormedAdjointCircuit cs →
        WellFormedAdjointCircuit (substituteAdjointCircuit (sampleInputWord α s) cs)) := by
  obtain ⟨he, hq, hg, hw⟩ := substitute_adjoint_evaluate_cost (controlOracle U)
    (sampleInputWord α s) cs
  rw [sampleInputWord_evaluate] at he
  rw [(sampleInputWord_cost α s).1, Nat.mul_comm] at hq
  rw [(sampleInputWord_cost α s).2, Nat.mul_comm (adjointQueryCount cs)] at hg
  exact ⟨he, hq, hg, fun hα hcs => hw (sampleInputWord_wellFormed α s hα) hcs⟩

theorem firstOrderInputWord_substitute (α s : ℝ) (U : Matrix W W ℂ)
    (cs : List (AdjointStep (Bool × W))) :
    evaluate (controlOracle U) (substituteAdjointCircuit (firstOrderInputWord α s) cs) =
        evaluate (firstOrderInputUnitary U α s) cs ∧
      adjointQueryCount (substituteAdjointCircuit (firstOrderInputWord α s) cs) =
        2 * adjointQueryCount cs ∧
      adjointGateCount (substituteAdjointCircuit (firstOrderInputWord α s) cs) =
        adjointGateCount cs + 5 * adjointQueryCount cs ∧
      (0 < α → WellFormedAdjointCircuit cs →
        WellFormedAdjointCircuit (substituteAdjointCircuit (firstOrderInputWord α s) cs)) := by
  obtain ⟨he, hq, hg, hw⟩ := substitute_adjoint_evaluate_cost (controlOracle U)
    (firstOrderInputWord α s) cs
  rw [firstOrderInputWord_evaluate] at he
  rw [(firstOrderInputWord_cost α s).1, Nat.mul_comm] at hq
  rw [(firstOrderInputWord_cost α s).2, Nat.mul_comm (adjointQueryCount cs)] at hg
  exact ⟨he, hq, hg, fun hα hcs => hw (firstOrderInputWord_wellFormed α s hα) hcs⟩

theorem original_oracle_sample_counted {I : Type} [Fintype I] [DecidableEq I]
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α ε s : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α ε) :
    WellFormedAdjointCircuit (sampleInputWord (W := W) α s) ∧
    controlOracle U ∈ Matrix.unitaryGroup (Bool × W) ℂ ∧
    BlockEncoding (L + (s : ℂ) • H)
      (evaluate (controlOracle U) (sampleInputWord α s))
      (tagFrame false R) (tagFrame false R)
      (α * Real.sqrt (1 + s ^ 2)) (ε * Real.sqrt (1 + s ^ 2)) ∧
    adjointQueryCount (sampleInputWord (W := W) α s) = 2 ∧
    adjointGateCount (sampleInputWord (W := W) α s) = 5 := by
  refine ⟨sampleInputWord_wellFormed α s henc.normalization_pos,
    controlOracle_unitary henc.unitary, ?_, sampleInputWord_cost α s⟩
  rw [sampleInputWord_evaluate]
  exact original_oracle_sample_blockEncoding L H hL hH U R α ε s henc

theorem original_oracle_first_order_counted {I : Type} [Fintype I] [DecidableEq I]
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix W W ℂ) (R : Matrix W I ℂ) (α ε s : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U R R α ε) :
    WellFormedAdjointCircuit (firstOrderInputWord (W := W) α s) ∧
    controlOracle U ∈ Matrix.unitaryGroup (Bool × W) ℂ ∧
    BlockEncoding (H + (s : ℂ) • L)
      (evaluate (controlOracle U) (firstOrderInputWord α s))
      (tagFrame false R) (tagFrame false R)
      (α * Real.sqrt (1 + s ^ 2)) (ε * Real.sqrt (1 + s ^ 2)) ∧
    adjointQueryCount (firstOrderInputWord (W := W) α s) = 2 ∧
    adjointGateCount (firstOrderInputWord (W := W) α s) = 5 := by
  refine ⟨firstOrderInputWord_wellFormed α s henc.normalization_pos,
    controlOracle_unitary henc.unitary, ?_, firstOrderInputWord_cost α s⟩
  rw [firstOrderInputWord_evaluate]
  exact original_oracle_first_order_blockEncoding L H hL hH U R α ε s henc

def spectatorLiftStep (J : Type) [DecidableEq J] {H : Type} :
    AdjointStep H → AdjointStep (J × H)
  | .gate V => .gate (parallelOracle V)
  | .forward => .forward
  | .backward => .backward

def spectatorLiftWord (J : Type) [DecidableEq J] {H : Type}
    (cs : List (AdjointStep H)) : List (AdjointStep (J × H)) :=
  cs.map (spectatorLiftStep J)

theorem spectatorLiftWord_evaluate (J : Type) [Fintype J] [DecidableEq J]
    (U : Matrix W W ℂ) (cs : List (AdjointStep W)) :
    evaluate (parallelOracle (J := J) U) (spectatorLiftWord J cs) =
      parallelOracle (evaluate U cs) := by
  induction cs with
  | nil => simp [spectatorLiftWord, evaluate, parallelOracle, parallel_select_one]
  | cons c cs ih =>
    change instructionMatrix (parallelOracle U) (spectatorLiftStep J c) *
      evaluate (parallelOracle U) (spectatorLiftWord J cs) =
        parallelOracle (instructionMatrix U c * evaluate U cs)
    rw [ih]
    cases c <;> simp [spectatorLiftStep, instructionMatrix, parallelOracle,
      parallel_select_adjoint, parallel_select_mul]

theorem spectatorLiftWord_cost (J : Type) [DecidableEq J] {H : Type}
    (cs : List (AdjointStep H)) :
    adjointQueryCount (spectatorLiftWord J cs) = adjointQueryCount cs ∧
      adjointGateCount (spectatorLiftWord J cs) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [spectatorLiftWord, spectatorLiftStep, adjointQueryCount,
      adjointGateCount] at ih ⊢ <;> exact ih

theorem spectatorLiftWord_wellFormed (J : Type) [Fintype J] [DecidableEq J]
    {cs : List (AdjointStep W)} (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (spectatorLiftWord J cs) := by
  induction cs with
  | nil => simp [spectatorLiftWord]
  | cons c cs ih =>
    cases c <;> simp only [spectatorLiftWord, List.map_cons, spectatorLiftStep,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨parallelOracle_unitary hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

theorem sampleInputWord_parallel_substitute (J : Type) [Fintype J] [DecidableEq J]
    (α s : ℝ) (U : Matrix W W ℂ) (cs : List (AdjointStep (J × (Bool × W)))) :
    evaluate (parallelOracle (J := J) (controlOracle U))
        (substituteAdjointCircuit (spectatorLiftWord J (sampleInputWord α s)) cs) =
      evaluate (parallelOracle (J := J) (sampleInputUnitary U α s)) cs ∧
    adjointQueryCount
        (substituteAdjointCircuit (spectatorLiftWord J (sampleInputWord α s)) cs) =
      2 * adjointQueryCount cs ∧
    adjointGateCount
        (substituteAdjointCircuit (spectatorLiftWord J (sampleInputWord α s)) cs) =
      adjointGateCount cs + 5 * adjointQueryCount cs ∧
    (0 < α → WellFormedAdjointCircuit cs → WellFormedAdjointCircuit
      (substituteAdjointCircuit (spectatorLiftWord J (sampleInputWord α s)) cs)) := by
  obtain ⟨he, hq, hg, hw⟩ := substitute_adjoint_evaluate_cost
    (parallelOracle (J := J) (controlOracle U))
    (spectatorLiftWord J (sampleInputWord α s)) cs
  rw [spectatorLiftWord_evaluate, sampleInputWord_evaluate] at he
  rw [(spectatorLiftWord_cost J _).1, (sampleInputWord_cost α s).1, Nat.mul_comm] at hq
  rw [(spectatorLiftWord_cost J _).2, (sampleInputWord_cost α s).2,
    Nat.mul_comm (adjointQueryCount cs)] at hg
  exact ⟨he, hq, hg, fun hα hcs => hw
    (spectatorLiftWord_wellFormed J (sampleInputWord_wellFormed α s hα)) hcs⟩

theorem firstOrderInputWord_parallel_substitute (J : Type) [Fintype J] [DecidableEq J]
    (α s : ℝ) (U : Matrix W W ℂ) (cs : List (AdjointStep (J × (Bool × W)))) :
    evaluate (parallelOracle (J := J) (controlOracle U))
        (substituteAdjointCircuit (spectatorLiftWord J (firstOrderInputWord α s)) cs) =
      evaluate (parallelOracle (J := J) (firstOrderInputUnitary U α s)) cs ∧
    adjointQueryCount
        (substituteAdjointCircuit (spectatorLiftWord J (firstOrderInputWord α s)) cs) =
      2 * adjointQueryCount cs ∧
    adjointGateCount
        (substituteAdjointCircuit (spectatorLiftWord J (firstOrderInputWord α s)) cs) =
      adjointGateCount cs + 5 * adjointQueryCount cs ∧
    (0 < α → WellFormedAdjointCircuit cs → WellFormedAdjointCircuit
      (substituteAdjointCircuit (spectatorLiftWord J (firstOrderInputWord α s)) cs)) := by
  obtain ⟨he, hq, hg, hw⟩ := substitute_adjoint_evaluate_cost
    (parallelOracle (J := J) (controlOracle U))
    (spectatorLiftWord J (firstOrderInputWord α s)) cs
  rw [spectatorLiftWord_evaluate, firstOrderInputWord_evaluate] at he
  rw [(spectatorLiftWord_cost J _).1, (firstOrderInputWord_cost α s).1, Nat.mul_comm] at hq
  rw [(spectatorLiftWord_cost J _).2, (firstOrderInputWord_cost α s).2,
    Nat.mul_comm (adjointQueryCount cs)] at hg
  exact ⟨he, hq, hg, fun hα hcs => hw
    (spectatorLiftWord_wellFormed J (firstOrderInputWord_wellFormed α s hα)) hcs⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
