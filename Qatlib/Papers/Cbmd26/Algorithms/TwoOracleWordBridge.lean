/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.SeparateOracleBridge
import Qatlib.Papers.Cbmd26.Algorithms.RegisterLCUBridge
import Qatlib.Papers.Cbmd26.Algorithms.ControlledAccessBridge
import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
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

def substituteTwoOracleWord {H : Type*} (body : List (PreparedStep H)) :
    List (AdjointStep H) → List (PreparedStep H)
  | [] => []
  | .gate V :: cs => .gate V :: substituteTwoOracleWord body cs
  | .forward :: cs => body ++ substituteTwoOracleWord body cs
  | .backward :: cs => Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord body ++ substituteTwoOracleWord body cs

theorem substituteTwoOracleWord_evaluate {H : Type*} [Fintype H] [DecidableEq H]
    (O1 O2 : Matrix H H ℂ) (body : List (PreparedStep H)) (cs : List (AdjointStep H)) :
    evaluatePrepared O1 O2 (substituteTwoOracleWord body cs) =
      evaluate (evaluatePrepared O1 O2 body) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [substituteTwoOracleWord, evaluatePrepared_append,
      evaluatePrepared, preparedInstruction, evaluate, instructionMatrix,
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_evaluate, ih]

theorem substituteTwoOracleWord_cost {H : Type*}
    (body : List (PreparedStep H)) (cs : List (AdjointStep H)) :
    preparedDataQueries (substituteTwoOracleWord body cs) =
        adjointQueryCount cs * preparedDataQueries body ∧
    preparedInputQueries (substituteTwoOracleWord body cs) =
        adjointQueryCount cs * preparedInputQueries body ∧
    preparedFixedGates (substituteTwoOracleWord body cs) =
        adjointGateCount cs + adjointQueryCount cs * preparedFixedGates body := by
  induction cs with
  | nil => simp [substituteTwoOracleWord, preparedDataQueries, preparedInputQueries,
      preparedFixedGates, adjointQueryCount, adjointGateCount]
  | cons c cs ih =>
    have hinv := Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_counts body
    cases c <;> simp [substituteTwoOracleWord, Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.data_append,
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.input_append, Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.gates_append,
      preparedDataQueries, preparedInputQueries, preparedFixedGates,
      adjointQueryCount, adjointGateCount, ih.1, ih.2.1, ih.2.2,
      hinv.1, hinv.2.1, hinv.2.2, Nat.add_mul] <;> omega

theorem substituteTwoOracleWord_valid {H : Type*} [Fintype H] [DecidableEq H]
    {body : List (PreparedStep H)} {cs : List (AdjointStep H)}
    (hbody : PreparedCircuitValid body) (hcs : WellFormedAdjointCircuit cs) :
    PreparedCircuitValid (substituteTwoOracleWord body cs) := by
  induction cs with
  | nil => simp [substituteTwoOracleWord, PreparedCircuitValid]
  | cons c cs ih =>
    have ht : WellFormedAdjointCircuit cs := fun V hV => hcs V (List.mem_cons_of_mem c hV)
    have hi := ih ht
    cases c with
    | gate V =>
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hcs V (by simp)
      · exact hi d hd
    | forward =>
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hbody d hd
      · exact hi d hd
    | backward =>
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.inverseWord_valid hbody d hd
      · exact hi d hd

theorem substituteTwoOracleWord_unitary {H : Type*} [Fintype H] [DecidableEq H]
    {O1 O2 : Matrix H H ℂ} {body : List (PreparedStep H)} {cs : List (AdjointStep H)}
    (hbody : PreparedCircuitValid body) (hcs : WellFormedAdjointCircuit cs)
    (hO1 : O1 ∈ Matrix.unitaryGroup H ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup H ℂ) :
    evaluatePrepared O1 O2 (substituteTwoOracleWord body cs) ∈ Matrix.unitaryGroup H ℂ :=
  (substituteTwoOracleWord_valid hbody hcs).evaluate_unitary hO1 hO2

def spectatorLiftPreparedStep (J : Type*) [DecidableEq J] {H : Type*} :
    PreparedStep H → PreparedStep (J × H)
  | .gate V => .gate (parallelOracle V)
  | .dataForward => .dataForward
  | .dataBackward => .dataBackward
  | .prepareForward => .prepareForward
  | .prepareBackward => .prepareBackward

def spectatorLiftPreparedWord (J : Type*) [DecidableEq J] {H : Type*}
    (cs : List (PreparedStep H)) : List (PreparedStep (J × H)) :=
  cs.map (spectatorLiftPreparedStep J)

theorem spectatorLiftPreparedWord_evaluate (J : Type*) [Fintype J] [DecidableEq J]
    {H : Type*} [Fintype H] [DecidableEq H] (O1 O2 : Matrix H H ℂ)
    (cs : List (PreparedStep H)) :
    evaluatePrepared (parallelOracle (J := J) O1) (parallelOracle (J := J) O2)
      (spectatorLiftPreparedWord J cs) = parallelOracle (evaluatePrepared O1 O2 cs) := by
  induction cs with
  | nil => simp [spectatorLiftPreparedWord, evaluatePrepared, parallelOracle, parallel_select_one]
  | cons c cs ih =>
    change preparedInstruction (parallelOracle O1) (parallelOracle O2)
        (spectatorLiftPreparedStep J c) *
      evaluatePrepared (parallelOracle O1) (parallelOracle O2) (spectatorLiftPreparedWord J cs) =
      parallelOracle (preparedInstruction O1 O2 c * evaluatePrepared O1 O2 cs)
    rw [ih]
    cases c <;> simp [spectatorLiftPreparedStep, preparedInstruction, parallelOracle,
      parallel_select_adjoint, parallel_select_mul]

theorem spectatorLiftPreparedWord_cost (J : Type*) [DecidableEq J] {H : Type*}
    (cs : List (PreparedStep H)) :
    preparedDataQueries (spectatorLiftPreparedWord J cs) = preparedDataQueries cs ∧
    preparedInputQueries (spectatorLiftPreparedWord J cs) = preparedInputQueries cs ∧
    preparedFixedGates (spectatorLiftPreparedWord J cs) = preparedFixedGates cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [spectatorLiftPreparedWord, spectatorLiftPreparedStep,
      preparedDataQueries, preparedInputQueries, preparedFixedGates] at ih ⊢ <;> exact ih

theorem spectatorLiftPreparedWord_valid (J : Type*) [Fintype J] [DecidableEq J]
    {H : Type*} [Fintype H] [DecidableEq H] {cs : List (PreparedStep H)}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (spectatorLiftPreparedWord J cs) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hv := hcs d hd
  cases d <;> simp only [spectatorLiftPreparedStep, PreparedInstructionValid] at *
  exact parallelOracle_unitary hv

def reindexPreparedStep {H K : Type*} (e : K ≃ H) : PreparedStep H → PreparedStep K
  | .gate V => .gate (V.submatrix e e)
  | .dataForward => .dataForward
  | .dataBackward => .dataBackward
  | .prepareForward => .prepareForward
  | .prepareBackward => .prepareBackward

def reindexPreparedWord {H K : Type*} (e : K ≃ H)
    (cs : List (PreparedStep H)) : List (PreparedStep K) := cs.map (reindexPreparedStep e)

theorem reindexPreparedWord_evaluate {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (e : K ≃ H) (O1 O2 : Matrix H H ℂ)
    (cs : List (PreparedStep H)) :
    evaluatePrepared (O1.submatrix e e) (O2.submatrix e e) (reindexPreparedWord e cs) =
      (evaluatePrepared O1 O2 cs).submatrix e e := by
  induction cs with
  | nil => simp [reindexPreparedWord, evaluatePrepared, Matrix.submatrix_one_equiv]
  | cons c cs ih =>
    change preparedInstruction (O1.submatrix e e) (O2.submatrix e e) (reindexPreparedStep e c) *
      evaluatePrepared (O1.submatrix e e) (O2.submatrix e e) (reindexPreparedWord e cs) =
      (preparedInstruction O1 O2 c * evaluatePrepared O1 O2 cs).submatrix e e
    rw [ih, ← Matrix.submatrix_mul_equiv _ _ e e e]
    cases c <;> simp [reindexPreparedStep, preparedInstruction, Matrix.conjTranspose_submatrix]

theorem reindexPreparedWord_cost {H K : Type*} (e : K ≃ H) (cs : List (PreparedStep H)) :
    preparedDataQueries (reindexPreparedWord e cs) = preparedDataQueries cs ∧
    preparedInputQueries (reindexPreparedWord e cs) = preparedInputQueries cs ∧
    preparedFixedGates (reindexPreparedWord e cs) = preparedFixedGates cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [reindexPreparedWord, reindexPreparedStep,
      preparedDataQueries, preparedInputQueries, preparedFixedGates] at ih ⊢ <;> exact ih

theorem reindexPreparedWord_valid {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (e : K ≃ H) {cs : List (PreparedStep H)}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (reindexPreparedWord e cs) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hv := hcs d hd
  cases d <;> simp only [reindexPreparedStep, PreparedInstructionValid] at *
  exact relabelGate_mem_unitary hv e.symm

section InsertFlag
variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

def insertTwoOracleWord (cs : List (PreparedStep (J × H))) :
    List (PreparedStep (J × (Bool × H))) :=
  reindexPreparedWord (swapLabelEquiv J Bool H) (spectatorLiftPreparedWord Bool cs)

theorem insertTwoOracleWord_evaluate (O1 O2 : Matrix H H ℂ)
    (cs : List (PreparedStep (J × H))) (U : J → Matrix H H ℂ)
    (he : evaluatePrepared (parallelOracle O1) (parallelOracle O2) cs = select U) :
    evaluatePrepared (parallelOracle (J := J) (parallelOracle (J := Bool) O1))
        (parallelOracle (J := J) (parallelOracle (J := Bool) O2))
        (insertTwoOracleWord cs) = select (fun j => parallelOracle (J := Bool) (U j)) := by
  have ho (O : Matrix H H ℂ) : parallelOracle (J := J) (parallelOracle (J := Bool) O) =
      (parallelOracle (J := Bool) (parallelOracle (J := J) O)).submatrix
        (swapLabelEquiv J Bool H) (swapLabelEquiv J Bool H) := by
    ext ⟨j, b, i⟩ ⟨k, c, l⟩
    by_cases hj : j = k <;> by_cases hb : b = c <;>
      simp [parallelOracle, select, swapLabelEquiv, hj, hb]
  rw [ho O1, ho O2, insertTwoOracleWord, reindexPreparedWord_evaluate,
    spectatorLiftPreparedWord_evaluate, he]
  ext ⟨j, b, i⟩ ⟨k, c, l⟩
  by_cases hj : j = k <;> by_cases hb : b = c <;>
    simp [parallelOracle, select, swapLabelEquiv, hj, hb]

omit [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] in

theorem insertTwoOracleWord_cost (cs : List (PreparedStep (J × H))) :
    preparedDataQueries (insertTwoOracleWord cs) = preparedDataQueries cs ∧
    preparedInputQueries (insertTwoOracleWord cs) = preparedInputQueries cs ∧
    preparedFixedGates (insertTwoOracleWord cs) = preparedFixedGates cs :=
  ⟨(reindexPreparedWord_cost _ _).1.trans (spectatorLiftPreparedWord_cost _ _).1,
   (reindexPreparedWord_cost _ _).2.1.trans (spectatorLiftPreparedWord_cost _ _).2.1,
   (reindexPreparedWord_cost _ _).2.2.trans (spectatorLiftPreparedWord_cost _ _).2.2⟩

theorem insertTwoOracleWord_valid {cs : List (PreparedStep (J × H))}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (insertTwoOracleWord cs) :=
  reindexPreparedWord_valid _ (spectatorLiftPreparedWord_valid Bool hcs)
end InsertFlag

section Mask
variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

def maskPreparedStep (mask : J → Bool) : PreparedStep H → PreparedStep (J × H)
  | .gate V => .gate (maskedOracle mask V)
  | .dataForward => .dataForward
  | .dataBackward => .dataBackward
  | .prepareForward => .prepareForward
  | .prepareBackward => .prepareBackward

def maskPreparedWord (mask : J → Bool) (cs : List (PreparedStep H)) :
    List (PreparedStep (J × H)) := cs.map (maskPreparedStep mask)

theorem maskedOracle_mul (mask : J → Bool) (A B : Matrix H H ℂ) :
    maskedOracle mask (A * B) = maskedOracle mask A * maskedOracle mask B := by
  rw [maskedOracle, maskedOracle, maskedOracle, parallel_select_mul]
  congr 1
  funext j
  cases h : mask j <;> simp

omit [Fintype J] [Fintype H] in

theorem maskedOracle_adjoint (mask : J → Bool) (A : Matrix H H ℂ) :
    maskedOracle mask Aᴴ = (maskedOracle mask A)ᴴ := by
  rw [maskedOracle, maskedOracle, parallel_select_adjoint]
  congr 1
  funext j
  cases h : mask j <;> simp

omit [Fintype J] [Fintype H] in

theorem maskedOracle_one (mask : J → Bool) : maskedOracle mask (1 : Matrix H H ℂ) = 1 := by
  simp [maskedOracle, parallel_select_one]

theorem maskedOracle_unitary (mask : J → Bool) {A : Matrix H H ℂ}
    (hA : A ∈ Matrix.unitaryGroup H ℂ) : maskedOracle mask A ∈ Matrix.unitaryGroup (J × H) ℂ := by
  apply select_unitary
  intro j
  cases h : mask j <;> simp [hA]

theorem maskPreparedWord_evaluate (mask : J → Bool) (O1 O2 : Matrix H H ℂ)
    (cs : List (PreparedStep H)) :
    evaluatePrepared (maskedOracle mask O1) (maskedOracle mask O2) (maskPreparedWord mask cs) =
      maskedOracle mask (evaluatePrepared O1 O2 cs) := by
  induction cs with
  | nil => simp [maskPreparedWord, evaluatePrepared, maskedOracle_one]
  | cons c cs ih =>
    change preparedInstruction (maskedOracle mask O1) (maskedOracle mask O2)
        (maskPreparedStep mask c) *
      evaluatePrepared (maskedOracle mask O1) (maskedOracle mask O2) (maskPreparedWord mask cs) =
      maskedOracle mask (preparedInstruction O1 O2 c * evaluatePrepared O1 O2 cs)
    rw [ih, maskedOracle_mul]
    cases c <;> simp [maskPreparedStep, preparedInstruction, maskedOracle_adjoint]

omit [Fintype J] [Fintype H] in

theorem maskPreparedWord_cost (mask : J → Bool) (cs : List (PreparedStep H)) :
    preparedDataQueries (maskPreparedWord mask cs) = preparedDataQueries cs ∧
    preparedInputQueries (maskPreparedWord mask cs) = preparedInputQueries cs ∧
    preparedFixedGates (maskPreparedWord mask cs) = preparedFixedGates cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [maskPreparedWord, maskPreparedStep,
      preparedDataQueries, preparedInputQueries, preparedFixedGates] at ih ⊢ <;> exact ih

theorem maskPreparedWord_valid (mask : J → Bool) {cs : List (PreparedStep H)}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (maskPreparedWord mask cs) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hv := hcs d hd
  cases d <;> simp only [maskPreparedStep, PreparedInstructionValid] at *
  exact maskedOracle_unitary mask hv
end Mask

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
