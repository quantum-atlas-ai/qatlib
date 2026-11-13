/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.TwoOracleWordBridge

/-!
# Clean compilation of masked two-oracle words

`cleanTwoOracleStep` and `cleanTwoOracleWord` compile masked data and input queries using an
additional Boolean register and controlled parallel oracles. `cleanTwoOracleWord_evaluate`
identifies the two Boolean sectors, while `cleanTwoOracleWord_cost` preserves each query count
and adds two fixed gates per query. Validity, unitarity, and `cleanTwoOracleWord_blockEncoding`
transport the original block encoding to the sector tagged `false`.

This compilation supports the separate-oracle CBMD implementations associated with
[WangEtAl2026].

## Main statements

* `cleanTwoOracleWord_evaluate` identifies the Boolean sectors of the compiled word.
* `cleanTwoOracleWord_cost` gives exact query and fixed-gate counts.
* `cleanTwoOracleWord_blockEncoding` transports a block encoding to the sector tagged `false`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- Compiles a prepared instruction onto an extra Boolean register, lifting fixed gates in
parallel and surrounding each data or input query by two mask-computation gates. -/
def cleanTwoOracleStep (mask : J → Bool) : PreparedStep (J × H) →
    List (PreparedStep (Bool × (J × H)))
  | .gate V => [.gate (parallelOracle (J := Bool) V)]
  | .dataForward => [.gate (maskCompute mask), .dataForward, .gate (maskCompute mask)]
  | .dataBackward => [.gate (maskCompute mask), .dataBackward, .gate (maskCompute mask)]
  | .prepareForward => [.gate (maskCompute mask), .prepareForward, .gate (maskCompute mask)]
  | .prepareBackward => [.gate (maskCompute mask), .prepareBackward, .gate (maskCompute mask)]

/-- Compiles a prepared two-oracle word by concatenating the compiled instructions in their
original order. -/
def cleanTwoOracleWord (mask : J → Bool) : List (PreparedStep (J × H)) →
    List (PreparedStep (Bool × (J × H)))
  | [] => []
  | c :: cs => cleanTwoOracleStep mask c ++ cleanTwoOracleWord mask cs

/-- The compiled instruction evaluated with controlled parallel oracles is block diagonal in the
added Boolean register. In sector `b`, it applies the original instruction with each oracle
masked by `xor b (mask j)`. -/
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

/-- The compiled word evaluated with controlled parallel oracles is block diagonal in the added
Boolean register. In sector `b`, it evaluates the original word with both oracles masked by
`xor b (mask j)`. -/
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

/-- Compilation preserves the data-query and input-query counts exactly and increases the
fixed-gate count by twice the total number of those queries. -/
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

/-- Compilation of a valid prepared instruction yields a valid prepared circuit. -/
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

/-- Compilation preserves validity of a prepared two-oracle circuit. -/
theorem cleanTwoOracleWord_valid (mask : J → Bool) {cs : List (PreparedStep (J × H))}
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (cleanTwoOracleWord mask cs) := by
  induction cs with
  | nil => simp [cleanTwoOracleWord, PreparedCircuitValid]
  | cons c cs ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact cleanTwoOracleStep_valid mask (hcs c (by simp)) d hd
    · exact ih (fun e he => hcs e (List.mem_cons_of_mem c he)) d hd

/-- If both oracles are unitary and the original prepared circuit is valid, the compiled word
evaluated with controlled parallel oracles is unitary. -/
theorem cleanTwoOracleWord_unitary (mask : J → Bool) {O1 O2 : Matrix H H ℂ}
    (hO1 : O1 ∈ Matrix.unitaryGroup H ℂ) (hO2 : O2 ∈ Matrix.unitaryGroup H ℂ)
    {cs : List (PreparedStep (J × H))} (hcs : PreparedCircuitValid cs) :
    evaluatePrepared (controlOracle (parallelOracle (J := J) O1))
      (controlOracle (parallelOracle (J := J) O2)) (cleanTwoOracleWord mask cs) ∈
        Matrix.unitaryGroup (Bool × (J × H)) ℂ :=
  (cleanTwoOracleWord_valid mask hcs).evaluate_unitary
    (controlOracle_unitary (parallelOracle_unitary hO1))
    (controlOracle_unitary (parallelOracle_unitary hO2))

/-- For unitary oracles and a valid prepared circuit, any block encoding obtained from the
original masked-oracle word lifts to the compiled word in the Boolean sector tagged `false`.
The normalization and error parameters are preserved. -/
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
