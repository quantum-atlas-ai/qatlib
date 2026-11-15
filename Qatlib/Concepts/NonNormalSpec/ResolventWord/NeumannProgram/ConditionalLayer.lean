/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.FreshFlagWord

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix

variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

def selectedNeumannPairWord (active : J → Bool) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (J × (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H))) :=
  [.gate (Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) else 1)), .forward,
    .gate (Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) else 1)), .backward]

/-- Evaluating the selected Neumann pair word yields the branchwise product of the conditional
flag gates, the selected matrix, and its adjoint. -/
private theorem selected_evaluate (active : J → Bool) (P : Matrix H H ℂ)
    (V : J → Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H) ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.BlockEncoding.LCU.select V) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => (if active j then Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) else 1) *
        V j * (if active j then Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) else 1) * (V j)ᴴ) := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul, Matrix.mul_assoc]

/-- For a unitary data oracle, replacing inactive oracle branches by the identity leaves the
selected Neumann pair word evaluation unchanged. -/
theorem neumann_conditional_queries_eliminated (active : J → Bool) (P U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U))
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) =
      Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
        Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U else 1))
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) := by
  let V :=
      Qatlib.Foundations.PureStateMath.TensorGate
      (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U
  have hv : V*Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
      (Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ).one_mem hU)
  simp only [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, selected_evaluate]
  apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
  funext j
  cases ha : active j
  · simpa only [ha, Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, Matrix.mul_one,
      Matrix.conjTranspose_one] using hv
  · simp only [↓reduceIte]

/-- The selected Neumann pair word evaluates to the active branchwise Neumann word and inactive
identity, with two queries, two gates, and well-formedness. -/
theorem selected_neumann_pair_word (active : J → Bool) (P U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U))
        (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun j => if active j then
        Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P)
        else 1) ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) = 2 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) = 2 ∧
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord active P) := by
  let V :=
      Qatlib.Foundations.PureStateMath.TensorGate
      (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U
  have hv : V*Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp
      (Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ).one_mem hU)
  have hlegal :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_pair_word_legal P hP
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true] at hlegal
  refine ⟨?_, rfl, rfl, ?_⟩
  · simp only [Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, selected_evaluate]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext j
    cases ha : active j
    · simpa only [ha, Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, Matrix.mul_one] using hv
    · simp only [↓reduceIte, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix,
        Matrix.mul_one, Matrix.mul_assoc]
  · simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.selectedNeumannPairWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
    refine ⟨Qatlib.Concepts.BlockEncoding.LCU.select_unitary (fun j : J => if active j then
        Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) else 1) ?_,
      Qatlib.Concepts.BlockEncoding.LCU.select_unitary (fun j : J => if active j then
        Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) else 1) ?_⟩
    all_goals intro j
    · cases active j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (unitaryGroup _ ℂ).one_mem
      · exact hlegal.1
    · cases active j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (unitaryGroup _ ℂ).one_mem
      · exact hlegal.2

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
