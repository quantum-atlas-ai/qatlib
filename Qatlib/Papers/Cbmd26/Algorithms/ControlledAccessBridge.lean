/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CommonNormalizationBridge

/-!
# Masked oracle access with a clean control register

The `maskQueryWord` construction implements a label-dependent oracle mask by computing it into a
Boolean control, querying a controlled oracle, and uncomputing. Substitution through
`cleanMaskedWord` preserves the encoded block on the false control sector and gives exact
resource counts. These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `cleanMaskedWord_evaluate`: describes evaluation in each Boolean control sector.
* `cleanMaskedWord_blockEncoding`: transfers a masked block encoding with explicit circuit
  costs.

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
open scoped Matrix.Norms.L2Operator

variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

/-- Selects `U` or the identity according to a Boolean mask on the label register. -/
def maskedOracle (mask : J → Bool) (U : Matrix W W ℂ) : Matrix (J × W) (J × W) ℂ :=
  select (fun j => if mask j then U else 1)

/-- Defines the permutation matrix that flips the control bit exactly on labels where the mask
is true. -/
def maskCompute (mask : J → Bool) : Matrix (Bool × (J × W)) (Bool × (J × W)) ℂ :=
  (select (fun j => if mask j then controlFlip (H := W) else 1)).submatrix
    (controlSpectatorEquiv J W) (controlSpectatorEquiv J W)

/-- The mask-computation matrix is unitary. -/
theorem maskCompute_unitary (mask : J → Bool) :
    maskCompute (W := W) mask ∈ Matrix.unitaryGroup (Bool × (J × W)) ℂ := by
  apply relabelGate_mem_unitary (e := (controlSpectatorEquiv J W).symm)
  apply select_unitary
  intro j
  cases hm : mask j
  · simp
  · exact controlFlip_unitary

/-- Computes a mask into the control, makes one forward query, and uncomputes the mask. -/
def maskQueryWord (mask : J → Bool) : List (AdjointStep (Bool × (J × W))) :=
  [.gate (maskCompute mask), .forward, .gate (maskCompute mask)]

/-- The mask query word evaluates in control sector `b` to the oracle masked by the exclusive-or
of `b` and the label mask. -/
theorem maskQueryWord_evaluate (mask : J → Bool) (U : Matrix W W ℂ) :
    evaluate (controlOracle (parallelOracle (J := J) U)) (maskQueryWord mask) =
      select (fun b : Bool => maskedOracle (fun j => xor b (mask j)) U) := by
  simp only [maskQueryWord, evaluate, instructionMatrix, Matrix.mul_one]
  rw [controlOracle_parallelOracle]
  unfold maskCompute
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simp only [parallelOracle, parallel_select_mul]
  have hi (j : J) :
      (if mask j then controlFlip else 1) * controlOracle U *
        (if mask j then controlFlip else 1) =
      select (fun b : Bool => if xor b (mask j) then U else 1) := by
    cases hm : mask j
    · simp [controlOracle]
    · simp only [↓reduceIte, controlOracle, controlFlip_select]
      congr 1
  simp_rw [← Matrix.mul_assoc, hi]
  ext ⟨b,j,i⟩ ⟨c,k,l⟩
  by_cases hb : b = c <;> by_cases hj : j = k <;>
    simp [select, maskedOracle, controlSpectatorEquiv, hb, hj]

omit [Fintype J] [Fintype W] [Fintype I] [DecidableEq I] in

/-- The mask query word uses exactly one query and two gates. -/
theorem maskQueryWord_cost (mask : J → Bool) :
    adjointQueryCount (maskQueryWord (W := W) mask) = 1 ∧
    adjointGateCount (maskQueryWord (W := W) mask) = 2 := by
  exact ⟨rfl, rfl⟩

/-- The mask query word is a well-formed adjoint circuit. -/
theorem maskQueryWord_wellFormed (mask : J → Bool) :
    WellFormedAdjointCircuit (maskQueryWord (W := W) mask) := by
  simpa [maskQueryWord] using maskCompute_unitary (W := W) mask

/-- Evaluating a spectator-lifted word against a selected oracle equals selecting the branchwise
evaluations. -/
theorem evaluate_spectatorLiftWord_select {K H : Type} [Fintype K] [DecidableEq K]
    [Fintype H] [DecidableEq H] (U : K → Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (select U) (spectatorLiftWord K cs) = select (fun k => evaluate (U k) cs) := by
  induction cs with
  | nil => simp [spectatorLiftWord, evaluate, parallel_select_one]
  | cons c cs ih =>
    change instructionMatrix (select U) (spectatorLiftStep K c) *
      evaluate (select U) (spectatorLiftWord K cs) =
      select (fun k => instructionMatrix (U k) c * evaluate (U k) cs)
    rw [ih]
    cases c <;> simp [spectatorLiftStep, instructionMatrix, parallelOracle,
      parallel_select_adjoint, parallel_select_mul]

/-- Substitutes the mask query implementation into the Boolean spectator lift of an adjoint
word. -/
def cleanMaskedWord (mask : J → Bool) (cs : List (AdjointStep (J × W))) :
    List (AdjointStep (Bool × (J × W))) :=
  substituteAdjointCircuit (maskQueryWord mask) (spectatorLiftWord Bool cs)

/-- The clean masked word evaluates in control sector `b` to the original word with the
exclusive-or mask applied to its oracle. -/
theorem cleanMaskedWord_evaluate (mask : J → Bool) (U : Matrix W W ℂ)
    (cs : List (AdjointStep (J × W))) :
    evaluate (controlOracle (parallelOracle (J := J) U)) (cleanMaskedWord mask cs) =
      select (fun b : Bool => evaluate (maskedOracle (fun j => xor b (mask j)) U) cs) := by
  unfold cleanMaskedWord
  rw [(substitute_adjoint_evaluate_cost _ _ _).1, maskQueryWord_evaluate,
    evaluate_spectatorLiftWord_select]

/-- The clean masked word preserves the query count and adds two gates for every original query. -/
theorem cleanMaskedWord_cost (mask : J → Bool) (cs : List (AdjointStep (J × W))) :
    adjointQueryCount (cleanMaskedWord mask cs) = adjointQueryCount cs ∧
    adjointGateCount (cleanMaskedWord mask cs) = adjointGateCount cs + 2 * adjointQueryCount cs := by
  obtain ⟨_, hq, hg, _⟩ := substitute_adjoint_evaluate_cost
    (1 : Matrix (Bool × (J × W)) (Bool × (J × W)) ℂ)
    (maskQueryWord mask) (spectatorLiftWord Bool cs)
  rw [(spectatorLiftWord_cost _ _).1, (maskQueryWord_cost mask).1, mul_one] at hq
  rw [(spectatorLiftWord_cost _ _).1, (spectatorLiftWord_cost _ _).2,
    (maskQueryWord_cost mask).2, Nat.mul_comm] at hg
  exact ⟨hq, hg⟩

/-- The clean masked transformation preserves well-formedness. -/
theorem cleanMaskedWord_wellFormed (mask : J → Bool) {cs : List (AdjointStep (J × W))}
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (cleanMaskedWord mask cs) :=
  (substitute_adjoint_evaluate_cost
    (1 : Matrix (Bool × (J × W)) (Bool × (J × W)) ℂ) _ _).2.2.2
    (maskQueryWord_wellFormed mask) (spectatorLiftWord_wellFormed Bool hcs)

/-- Compressing a selected matrix on a tagged frame equals compressing the matrix in the tagged
sector. -/
theorem compress_tagFrame_select {K H : Type} [Fintype K] [DecidableEq K]
    [Fintype H] [DecidableEq H] (b : K) (V : K → Matrix H H ℂ)
    (F : Matrix H I ℂ) :
    compress (tagFrame b F) (select V) (tagFrame b F) = compress F (V b) F := by
  rw [compress_tagFrame, prepare_select_compress]
  simp [lcuMatrix, Ket, compress]

/-- A masked-oracle block encoding transfers to the false-tagged clean-control frame with the
same scale and error, preserving queries and adding two gates per query. -/
theorem cleanMaskedWord_blockEncoding (mask : J → Bool) (U : Matrix W W ℂ)
    (hU : U ∈ Matrix.unitaryGroup W ℂ) (cs : List (AdjointStep (J × W)))
    (hcs : WellFormedAdjointCircuit cs) (A : Matrix I I ℂ) (F : Matrix (J × W) I ℂ)
    (α ε : ℝ) (henc : BlockEncoding A (evaluate (maskedOracle mask U) cs) F F α ε) :
    WellFormedAdjointCircuit (cleanMaskedWord mask cs) ∧
    BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := J) U)) (cleanMaskedWord mask cs))
      (tagFrame false F) (tagFrame false F) α ε ∧
    adjointQueryCount (cleanMaskedWord mask cs) = adjointQueryCount cs ∧
    adjointGateCount (cleanMaskedWord mask cs) = adjointGateCount cs + 2 * adjointQueryCount cs := by
  have hw := cleanMaskedWord_wellFormed mask hcs
  refine ⟨hw, ?_, cleanMaskedWord_cost mask cs⟩
  refine ⟨hw.evaluate_unitary (controlOracle_unitary (parallelOracle_unitary hU)),
    tagFrame_isIsometry _ _ henc.left_isometry, tagFrame_isIsometry _ _ henc.right_isometry,
    henc.normalization_pos, henc.error_nonneg, ?_⟩
  rw [cleanMaskedWord_evaluate, compress_tagFrame_select]
  simpa using henc.error_le

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
