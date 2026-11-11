/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.QueryCostBridge

/-!
# Coherently selected sample input circuits

The `coherentCoefficientAdjointWord` construction builds selected linear combinations of an
oracle and its adjoint with coefficients depending on a sample label. The sample and first-order
input words evaluate to their corresponding selected unitaries and have constant circuit costs.
These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `coherentCoefficientAdjointWord_evaluate`: identifies the selected coefficient LCU unitary.
* `coherentFirstOrderInputWord_cost`: gives two queries and five gates.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

variable {J W : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]

/-- Constructs a label-controlled coefficient LCU word for the oracle-adjoint pair. -/
def coherentCoefficientAdjointWord (d : J → Bool → ℂ) (b₀ : Bool) :
    List (AdjointStep (J × (Bool × W))) :=
  [.gate (select (fun j => (prepareRegister (I := W) (coefficientPrepare (d j) b₀))ᴴ)),
   .gate (select (fun j => coefficientLabelPhase (W := W) (d j)))] ++
    spectatorLiftWord J (compileSelected ([.backward] : List (AdjointStep W)) [.forward]) ++
  [.gate (select (fun j => prepareRegister (I := W) (coefficientPrepare (d j) b₀)))]

/-- The coherent coefficient word evaluates to the selected family of coefficient LCU unitaries
for the oracle-adjoint pair. -/
theorem coherentCoefficientAdjointWord_evaluate (d : J → Bool → ℂ) (b₀ : Bool)
    (U : Matrix W W ℂ) :
    evaluate (parallelOracle (J := J) (controlOracle U))
        (coherentCoefficientAdjointWord d b₀) =
      select (fun j => coefficientLCUUnitary (d j) (oracleAdjointPair U) b₀) := by
  have hmiddle : evaluate (parallelOracle (J := J) (controlOracle U))
      (spectatorLiftWord J
        (compileSelected ([.backward] : List (AdjointStep W)) [.forward])) =
      select (fun _ : J => select (oracleAdjointPair U)) := by
    rw [spectatorLiftWord_evaluate, evaluate_compileSelected]
    simp only [parallelOracle, evaluate, instructionMatrix, Matrix.mul_one]
    congr 1
  simp only [coherentCoefficientAdjointWord, evaluate_append, evaluate,
    instructionMatrix, Matrix.mul_one, hmiddle]
  simp only [parallel_select_mul]
  congr 1
  funext j
  have hphase : coefficientLabelPhase (d j) * select (oracleAdjointPair U) =
      select (phaseAbsorbed (d j) (oracleAdjointPair U)) := by
    rw [coefficientLabelPhase, parallel_select_mul]
    congr 1
    funext b
    simp [phaseAbsorbed]
  rw [Matrix.mul_assoc _ (coefficientLabelPhase (d j)) (select (oracleAdjointPair U)), hphase]
  rfl

omit [Fintype J] [Fintype W] in

/-- The coherent coefficient word uses exactly two queries and five gates. -/
theorem coherentCoefficientAdjointWord_cost (d : J → Bool → ℂ) (b₀ : Bool) :
    adjointQueryCount (coherentCoefficientAdjointWord (W := W) d b₀) = 2 ∧
    adjointGateCount (coherentCoefficientAdjointWord (W := W) d b₀) = 5 := by
  simp [coherentCoefficientAdjointWord, (spectatorLiftWord_cost J _).1,
    (spectatorLiftWord_cost J _).2, queryCount_compileSelected,
    gateCount_compileSelected, adjointQueryCount, adjointGateCount]

/-- Positive coefficient mass at every label makes the coherent coefficient word well formed. -/
theorem coherentCoefficientAdjointWord_wellFormed (d : J → Bool → ℂ) (b₀ : Bool)
    (hd : ∀ j, 0 < coefficientMass (d j)) :
    WellFormedAdjointCircuit (coherentCoefficientAdjointWord (W := W) d b₀) := by
  have hp := fun j => prepareRegister_unitary (I := W)
    (coefficientPrepare_unitary (d j) b₀ (hd j))
  have hs : WellFormedAdjointCircuit
      (compileSelected ([.backward] : List (AdjointStep W)) [.forward]) :=
    compileSelected_wellFormed (by simp) (by simp)
  unfold coherentCoefficientAdjointWord
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨select_unitary _ (fun j => adjoint_unitary (hp j)),
        select_unitary _ (fun j => coefficientLabelPhase_unitary (d j))⟩
    · exact spectatorLiftWord_wellFormed J hs
  · simpa using select_unitary _ hp

/-- Specializes the coherent coefficient word to the scaled sample coefficients at each label. -/
def coherentSampleInputWord (α : ℝ) (s : J → ℝ) :
    List (AdjointStep (J × (Bool × W))) :=
  coherentCoefficientAdjointWord
    (fun j => scaledLCUCoefficients (sampleCoefficients (s j)) (fun _ => α)) false

/-- Specializes the coherent coefficient word to the scaled first-order coefficients at each
label. -/
def coherentFirstOrderInputWord (α : ℝ) (s : J → ℝ) :
    List (AdjointStep (J × (Bool × W))) :=
  coherentCoefficientAdjointWord
    (fun j => scaledLCUCoefficients (firstOrderCoefficients (s j)) (fun _ => α)) false

/-- The coherent sample word evaluates to the selected family of sample input unitaries. -/
theorem coherentSampleInputWord_evaluate (α : ℝ) (s : J → ℝ) (U : Matrix W W ℂ) :
    evaluate (parallelOracle (J := J) (controlOracle U)) (coherentSampleInputWord α s) =
      select (fun j => sampleInputUnitary U α (s j)) :=
  coherentCoefficientAdjointWord_evaluate _ _ U

/-- The coherent first-order word evaluates to the selected family of first-order input
unitaries. -/
theorem coherentFirstOrderInputWord_evaluate (α : ℝ) (s : J → ℝ) (U : Matrix W W ℂ) :
    evaluate (parallelOracle (J := J) (controlOracle U)) (coherentFirstOrderInputWord α s) =
      select (fun j => firstOrderInputUnitary U α (s j)) :=
  coherentCoefficientAdjointWord_evaluate _ _ U

omit [Fintype J] [Fintype W] in

/-- The coherent sample input word uses exactly two queries and five gates. -/
theorem coherentSampleInputWord_cost (α : ℝ) (s : J → ℝ) :
    adjointQueryCount (coherentSampleInputWord (W := W) α s) = 2 ∧
    adjointGateCount (coherentSampleInputWord (W := W) α s) = 5 :=
  coherentCoefficientAdjointWord_cost _ _

omit [Fintype J] [Fintype W] in

/-- The coherent first-order input word uses exactly two queries and five gates. -/
theorem coherentFirstOrderInputWord_cost (α : ℝ) (s : J → ℝ) :
    adjointQueryCount (coherentFirstOrderInputWord (W := W) α s) = 2 ∧
    adjointGateCount (coherentFirstOrderInputWord (W := W) α s) = 5 :=
  coherentCoefficientAdjointWord_cost _ _

/-- A positive input normalization makes the coherent sample input word well formed. -/
theorem coherentSampleInputWord_wellFormed (α : ℝ) (s : J → ℝ) (hα : 0 < α) :
    WellFormedAdjointCircuit (coherentSampleInputWord (W := W) α s) := by
  apply coherentCoefficientAdjointWord_wellFormed
  intro j
  rw [sample_scaled_coefficient_mass (s j) α hα]
  exact mul_pos hα (Real.sqrt_pos.2 (by positivity))

/-- A positive input normalization makes the coherent first-order input word well formed. -/
theorem coherentFirstOrderInputWord_wellFormed (α : ℝ) (s : J → ℝ) (hα : 0 < α) :
    WellFormedAdjointCircuit (coherentFirstOrderInputWord (W := W) α s) := by
  apply coherentCoefficientAdjointWord_wellFormed
  intro j
  rw [(scaled_lcu_coefficient_mass (firstOrderCoefficients (s j)) (fun _ => α)
    (fun _ => hα)).1, ← Finset.sum_mul, first_order_coefficient_weight]
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) hα

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
