/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.InputBridge
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion

/-!
# Counted Access to the Original Matrix Oracle

`coefficientAdjointWord` implements a two-term coefficient LCU of an oracle and its adjoint
using controlled access. The specializations `sampleInputWord` and `firstOrderInputWord` recover
the Hermitian combinations needed for CBMD from an encoding of `L + Complex.I • H`.

The module supplies exact substitution costs and well-formedness results for these words,
including after adding spectator registers with `spectatorLiftWord`. Each substituted query uses
two original-oracle queries and five fixed gates, making the original input-oracle cost explicit
for the algorithms of [WangEtAl2026].

## Main statements

* `coefficientAdjointWord_evaluate` identifies the circuit with the coefficient LCU of
  `oracleAdjointPair`.
* `original_oracle_sample_counted` and `original_oracle_first_order_counted` give the encoded
  operators, scaled errors, and exact costs.
* `sampleInputWord_substitute` and `firstOrderInputWord_substitute` give semantic and cost
  formulas for subroutine expansion.
* `spectatorLiftWord_evaluate` and the parallel substitution theorems extend the same results to
  spectator registers.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- The label-controlled coefficient-phase gate acting trivially on the data workspace. -/
def coefficientLabelPhase (d : Bool → ℂ) : Matrix (Bool × W) (Bool × W) ℂ :=
  select (phaseAbsorbed d (fun _ => (1 : Matrix W W ℂ)))

/-- The coefficient-label phase gate is unitary for every coefficient function `d`. -/
theorem coefficientLabelPhase_unitary (d : Bool → ℂ) :
    coefficientLabelPhase (W := W) d ∈ Matrix.unitaryGroup (Bool × W) ℂ :=
  select_unitary _ (phaseAbsorbed_unitary d (fun _ => (1 : Matrix W W ℂ))
    (fun _ => (Matrix.unitaryGroup W ℂ).one_mem))

/-- A controlled-oracle word implementing the coefficient LCU of the oracle-adjoint pair, with
coefficient preparation and label-phase gates. -/
def coefficientAdjointWord (d : Bool → ℂ) (j₀ : Bool) :
    List (AdjointStep (Bool × W)) :=
  [.gate (prepareRegister (I := W) (coefficientPrepare d j₀))ᴴ,
    .gate (coefficientLabelPhase d)] ++
    compileSelected ([.backward] : List (AdjointStep W)) [.forward] ++
    [.gate (prepareRegister (coefficientPrepare d j₀))]

/-- Evaluating `coefficientAdjointWord` against the controlled oracle gives
`coefficientLCUUnitary d (oracleAdjointPair U) j₀`. -/
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

/-- The coefficient-adjoint word uses exactly two oracle queries and five fixed gates. -/
theorem coefficientAdjointWord_cost (d : Bool → ℂ) (j₀ : Bool) :
    adjointQueryCount (coefficientAdjointWord (W := W) d j₀) = 2 ∧
      adjointGateCount (coefficientAdjointWord (W := W) d j₀) = 5 := by
  simp [coefficientAdjointWord, queryCount_compileSelected, gateCount_compileSelected,
    adjointQueryCount, adjointGateCount]

/-- Positive coefficient mass makes the coefficient-adjoint word well formed. -/
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

/-- The coefficient-adjoint word for the scaled sample coefficients, initialized at the false
label. -/
def sampleInputWord (α s : ℝ) : List (AdjointStep (Bool × W)) :=
  coefficientAdjointWord (scaledLCUCoefficients (sampleCoefficients s) (fun _ => α)) false

/-- The coefficient-adjoint word for the scaled first-order coefficients, initialized at the
false label. -/
def firstOrderInputWord (α s : ℝ) : List (AdjointStep (Bool × W)) :=
  coefficientAdjointWord (scaledLCUCoefficients (firstOrderCoefficients s) (fun _ => α)) false

/-- Evaluating `sampleInputWord` against the controlled oracle gives `sampleInputUnitary U α s`. -/
theorem sampleInputWord_evaluate (α s : ℝ) (U : Matrix W W ℂ) :
    evaluate (controlOracle U) (sampleInputWord α s) = sampleInputUnitary U α s :=
  coefficientAdjointWord_evaluate _ _ U

/-- Evaluating `firstOrderInputWord` against the controlled oracle gives `firstOrderInputUnitary
U α s`. -/
theorem firstOrderInputWord_evaluate (α s : ℝ) (U : Matrix W W ℂ) :
    evaluate (controlOracle U) (firstOrderInputWord α s) = firstOrderInputUnitary U α s :=
  coefficientAdjointWord_evaluate _ _ U

omit [Fintype W] in

/-- The sample input word uses exactly two oracle queries and five fixed gates. -/
theorem sampleInputWord_cost (α s : ℝ) :
    adjointQueryCount (sampleInputWord (W := W) α s) = 2 ∧
      adjointGateCount (sampleInputWord (W := W) α s) = 5 :=
  coefficientAdjointWord_cost _ _

omit [Fintype W] in

/-- The first-order input word uses exactly two oracle queries and five fixed gates. -/
theorem firstOrderInputWord_cost (α s : ℝ) :
    adjointQueryCount (firstOrderInputWord (W := W) α s) = 2 ∧
      adjointGateCount (firstOrderInputWord (W := W) α s) = 5 :=
  coefficientAdjointWord_cost _ _

/-- The sample input word is well formed when `α` is positive. -/
theorem sampleInputWord_wellFormed (α s : ℝ) (hα : 0 < α) :
    WellFormedAdjointCircuit (sampleInputWord (W := W) α s) := by
  apply coefficientAdjointWord_wellFormed
  rw [sample_scaled_coefficient_mass s α hα]
  exact mul_pos hα (Real.sqrt_pos.2 (by positivity))

/-- The first-order input word is well formed when `α` is positive. -/
theorem firstOrderInputWord_wellFormed (α s : ℝ) (hα : 0 < α) :
    WellFormedAdjointCircuit (firstOrderInputWord (W := W) α s) := by
  apply coefficientAdjointWord_wellFormed
  rw [(scaled_lcu_coefficient_mass (firstOrderCoefficients s) (fun _ => α)
    (fun _ => hα)).1, ← Finset.sum_mul, first_order_coefficient_weight]
  exact mul_pos (Real.sqrt_pos.2 (by positivity)) hα

/-- Substituting the sample input word preserves the intended sample-unitary evaluation, doubles
the query count, and adds five fixed gates per original query. Positive `α` also preserves
well-formedness. -/
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

/-- Substituting the first-order input word preserves the intended first-order-unitary
evaluation, doubles the query count, and adds five fixed gates per original query. Positive
`α` also preserves well-formedness. -/
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

/-- For Hermitian `L` and `H`, an encoding of `L + Complex.I • H` yields a well-formed
controlled-oracle word encoding `L + (s : ℂ) • H`, with normalization and error multiplied
by `sqrt (1 + s ^ 2)`. The word uses two queries and five fixed gates. -/
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

/-- For Hermitian `L` and `H`, an encoding of `L + Complex.I • H` yields a well-formed
controlled-oracle word encoding `H + (s : ℂ) • L`, with normalization and error multiplied
by `sqrt (1 + s ^ 2)`. The word uses two queries and five fixed gates. -/
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

/-- Lifts an adjoint-circuit step to a spectator register by parallelizing fixed gates and
retaining forward and backward queries. -/
def spectatorLiftStep (J : Type) [DecidableEq J] {H : Type} :
    AdjointStep H → AdjointStep (J × H)
  | .gate V => .gate (parallelOracle V)
  | .forward => .forward
  | .backward => .backward

/-- Lifts every step of an adjoint-circuit word to a workspace with spectator register `J`. -/
def spectatorLiftWord (J : Type) [DecidableEq J] {H : Type}
    (cs : List (AdjointStep H)) : List (AdjointStep (J × H)) :=
  cs.map (spectatorLiftStep J)

/-- Evaluating a spectator-lifted word against the parallel oracle gives the parallel lift of
the original circuit evaluation. -/
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

/-- Adding a spectator register preserves the oracle-query and fixed-gate counts. -/
theorem spectatorLiftWord_cost (J : Type) [DecidableEq J] {H : Type}
    (cs : List (AdjointStep H)) :
    adjointQueryCount (spectatorLiftWord J cs) = adjointQueryCount cs ∧
      adjointGateCount (spectatorLiftWord J cs) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [spectatorLiftWord, spectatorLiftStep, adjointQueryCount,
      adjointGateCount] at ih ⊢ <;> exact ih

/-- Adding a spectator register preserves well-formedness of an adjoint circuit. -/
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

/-- Substituting the spectator-lifted sample word realizes the parallel sample unitary, with
twice the queries and five additional fixed gates per original query. For positive `α`,
well-formedness is preserved. -/
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

/-- Substituting the spectator-lifted first-order word realizes the parallel first-order
unitary, with twice the queries and five additional fixed gates per original query. For
positive `α`, well-formedness is preserved. -/
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
