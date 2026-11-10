/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.TwoOracleWordBridge
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

variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

def cleanTwoOracleStep (mask : J → Bool) : PreparedStep (J × H) →
    List (PreparedStep (Bool × (J × H)))
  | .gate V => [.gate (parallelOracle (J := Bool) V)]
  | .dataForward => [.gate (maskCompute mask), .dataForward, .gate (maskCompute mask)]
  | .dataBackward => [.gate (maskCompute mask), .dataBackward, .gate (maskCompute mask)]
  | .prepareForward => [.gate (maskCompute mask), .prepareForward, .gate (maskCompute mask)]
  | .prepareBackward => [.gate (maskCompute mask), .prepareBackward, .gate (maskCompute mask)]

def cleanTwoOracleWord (mask : J → Bool) : List (PreparedStep (J × H)) →
    List (PreparedStep (Bool × (J × H)))
  | [] => []
  | c :: cs => cleanTwoOracleStep mask c ++ cleanTwoOracleWord mask cs

theorem cleanTwoOracleStep_evaluate (mask : J → Bool) (O1 O2 : Matrix H H ℂ)
    (c : PreparedStep (J × H)) :
    evaluatePrepared (controlOracle (parallelOracle (J := J) O1))
        (controlOracle (parallelOracle (J := J) O2)) (cleanTwoOracleStep mask c) =
      select (fun b : Bool => preparedInstruction
        (maskedOracle (fun j => xor b (mask j)) O1)
        (maskedOracle (fun j => xor b (mask j)) O2) c) := by
  have hf (O : Matrix H H ℂ) := maskQueryWord_evaluate (W := H) mask O
  have hb (O : Matrix H H ℂ) := maskQueryWord_evaluate (W := H) mask Oᴴ
  simp only [maskQueryWord, evaluate, instructionMatrix, Matrix.mul_one] at hf hb
  simp only [← parallelOracle_adjoint, ← controlOracle_adjoint, maskedOracle_adjoint] at hb
  cases c with
  | gate V => simp [cleanTwoOracleStep, evaluatePrepared, preparedInstruction, parallelOracle]
  | dataForward => simpa only [cleanTwoOracleStep, evaluatePrepared, preparedInstruction,
      Matrix.mul_one] using hf O1
  | dataBackward => simpa only [cleanTwoOracleStep, evaluatePrepared, preparedInstruction,
      Matrix.mul_one] using hb O1
  | prepareForward => simpa only [cleanTwoOracleStep, evaluatePrepared, preparedInstruction,
      Matrix.mul_one] using hf O2
  | prepareBackward => simpa only [cleanTwoOracleStep, evaluatePrepared, preparedInstruction,
      Matrix.mul_one] using hb O2

theorem cleanTwoOracleWord_evaluate (mask : J → Bool) (O1 O2 : Matrix H H ℂ)
    (cs : List (PreparedStep (J × H))) :
    evaluatePrepared (controlOracle (parallelOracle (J := J) O1))
        (controlOracle (parallelOracle (J := J) O2)) (cleanTwoOracleWord mask cs) =
      select (fun b : Bool => evaluatePrepared
        (maskedOracle (fun j => xor b (mask j)) O1)
        (maskedOracle (fun j => xor b (mask j)) O2) cs) := by
  induction cs with
  | nil => simp [cleanTwoOracleWord, evaluatePrepared, parallel_select_one]
  | cons c cs ih =>
    rw [cleanTwoOracleWord, evaluatePrepared_append, cleanTwoOracleStep_evaluate, ih,
      parallel_select_mul]
    rfl

omit [Fintype J] [Fintype H] in

theorem cleanTwoOracleWord_cost (mask : J → Bool) (cs : List (PreparedStep (J × H))) :
    preparedDataQueries (cleanTwoOracleWord mask cs) = preparedDataQueries cs ∧
    preparedInputQueries (cleanTwoOracleWord mask cs) = preparedInputQueries cs ∧
    preparedFixedGates (cleanTwoOracleWord mask cs) =
      preparedFixedGates cs + 2 * (preparedDataQueries cs + preparedInputQueries cs) := by
  induction cs with
  | nil => simp [cleanTwoOracleWord, preparedDataQueries, preparedInputQueries, preparedFixedGates]
  | cons c cs ih =>
    cases c <;> simp [cleanTwoOracleWord, cleanTwoOracleStep,
      preparedDataQueries, preparedInputQueries, preparedFixedGates,
      ih.1, ih.2.1, ih.2.2] <;> omega

theorem cleanTwoOracleStep_valid (mask : J → Bool) {c : PreparedStep (J × H)}
    (hc : PreparedInstructionValid c) : PreparedCircuitValid (cleanTwoOracleStep mask c) := by
  have hm := maskCompute_unitary (W := H) mask
  cases c with
  | gate V =>
    intro d hd
    have hd' : d = .gate (parallelOracle (J := Bool) V) := List.mem_singleton.mp hd
    subst d
    exact parallelOracle_unitary hc
  | dataForward | dataBackward | prepareForward | prepareBackward =>
    intro d hd
    simp only [cleanTwoOracleStep, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp only [PreparedInstructionValid] <;> exact hm

theorem cleanTwoOracleWord_valid (mask : J → Bool) {cs : List (PreparedStep (J × H))}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (cleanTwoOracleWord mask cs) := by
  induction cs with
  | nil => simp [cleanTwoOracleWord, PreparedCircuitValid]
  | cons c cs ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact cleanTwoOracleStep_valid mask (hcs c (by simp)) d hd
    · exact ih (fun e he => hcs e (List.mem_cons_of_mem c he)) d hd

theorem cleanTwoOracleWord_unitary (mask : J → Bool) {O1 O2 : Matrix H H ℂ}
    (hO1 : O1 ∈ Matrix.unitaryGroup H ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup H ℂ)
    {cs : List (PreparedStep (J × H))} (hcs : PreparedCircuitValid cs) :
    evaluatePrepared (controlOracle (parallelOracle (J := J) O1))
      (controlOracle (parallelOracle (J := J) O2)) (cleanTwoOracleWord mask cs) ∈
        Matrix.unitaryGroup (Bool × (J × H)) ℂ :=
  (cleanTwoOracleWord_valid mask hcs).evaluate_unitary
    (controlOracle_unitary (parallelOracle_unitary hO1))
    (controlOracle_unitary (parallelOracle_unitary hO2))

theorem cleanTwoOracleWord_blockEncoding {I : Type} [Fintype I] [DecidableEq I]
    (mask : J → Bool) (O1 O2 : Matrix H H ℂ)
    (hO1 : O1 ∈ Matrix.unitaryGroup H ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup H ℂ)
    (cs : List (PreparedStep (J × H))) (hcs : PreparedCircuitValid cs)
    (A : Matrix I I ℂ) (F : Matrix (J × H) I ℂ) (α ε : ℝ)
    (henc : BlockEncoding A (evaluatePrepared (maskedOracle mask O1) (maskedOracle mask O2) cs)
      F F α ε) :
    BlockEncoding A
      (evaluatePrepared (controlOracle (parallelOracle (J := J) O1))
        (controlOracle (parallelOracle (J := J) O2)) (cleanTwoOracleWord mask cs))
      (tagFrame false F) (tagFrame false F) α ε := by
  refine ⟨cleanTwoOracleWord_unitary mask hO1 hO2 hcs,
    tagFrame_isIsometry _ _ henc.left_isometry, tagFrame_isIsometry _ _ henc.right_isometry,
    henc.normalization_pos, henc.error_nonneg, ?_⟩
  rw [cleanTwoOracleWord_evaluate, compress_tagFrame_select]
  simpa only [Bool.false_xor] using henc.error_le

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
