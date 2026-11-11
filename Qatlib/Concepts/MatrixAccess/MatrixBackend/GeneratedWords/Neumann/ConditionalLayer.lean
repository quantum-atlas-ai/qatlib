/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

/-!
Conditional layers for the Neumann word.


The original definitions, proofs, and accounting for the same word are retained.
Known matrix macros do not establish elementary gate synthesis; input preparation,
retries, and bit costs require separate analysis.
-/

/-! A disabled Neumann layer need not control its data queries: controlling
only the two known flag gates leaves U U† = 1 on every inactive branch. The
identity is on the entire flag space, not merely its clean corner. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix

variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

/-- Only the known flag gates depend on the branch predicate. -/
def selectedNeumannPairWord (active : J → Bool) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H))) :=
  [.gate (Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) else 1)), .forward,
    .gate (Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) else 1)), .backward]

/-- The exact `selected_evaluate` invariant under the original hypotheses and resource conventions. -/
private theorem selected_evaluate (active : J → Bool) (P : Matrix H H ℂ)
    (V : J → Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.BlockEncoding.LCU.select V) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => (if active j then Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) else 1) *
        V j * (if active j then Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) else 1) * (V j)ᴴ) := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul, Matrix.mul_assoc]

/-- Whole-space equality eliminates the extra control on the unknown shifted
oracle. Unitarity is essential; all two original data calls remain charged. -/
theorem neumann_conditional_queries_eliminated (active : J → Bool) (P U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
        Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U else 1))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) := by
  let V := Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U
  have hv : V*Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
      (Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ).one_mem hU)
  simp only [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, selected_evaluate]
  apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
  funext j
  cases ha : active j
  · simpa only [ha, Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, Matrix.mul_one,
      Matrix.conjTranspose_one] using hv
  · simp only [↓reduceIte]

/-- Explicit full block-diagonal operator and the actual fixed cost. -/
theorem selected_neumann_pair_word (active : J → Bool) (P U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U))
        (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
        Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P)
        else 1) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) = 2 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) = 2 ∧
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P) := by
  let V := Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U
  have hv : V*Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
      (Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ).one_mem hU)
  have hlegal := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_pair_word_legal P hP
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] at hlegal
  refine ⟨?_, rfl, rfl, ?_⟩
  · simp only [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, selected_evaluate]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext j
    cases ha : active j
    · simpa only [ha, Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, Matrix.mul_one] using hv
    · simp only [↓reduceIte, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix,
        Matrix.mul_one, Matrix.mul_assoc]
  · simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
    refine ⟨Qatlib.Concepts.BlockEncoding.LCU.select_unitary (fun j : J => if active j then
        Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) else 1) ?_,
      Qatlib.Concepts.BlockEncoding.LCU.select_unitary (fun j : J => if active j then
        Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) else 1) ?_⟩
    all_goals intro j
    · cases ha : active j <;> simp only [ha, Bool.false_eq_true, ↓reduceIte]
      · exact (unitaryGroup _ ℂ).one_mem
      · exact hlegal.1
    · cases ha : active j <;> simp only [ha, Bool.false_eq_true, ↓reduceIte]
      · exact (unitaryGroup _ ℂ).one_mem
      · exact hlegal.2

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
