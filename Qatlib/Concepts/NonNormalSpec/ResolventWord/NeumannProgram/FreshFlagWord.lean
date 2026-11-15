/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OperatorAccess.EncodedAccess.FreshPositivePower
public import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
public import Qatlib.Concepts.QspSimulation.WordModel.CPPAdjointDefs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
open Matrix
open scoped BigOperators Kronecker

abbrev NeumannFlagPair := Bool × Bool
abbrev NeumannBranchSpace (m : ℕ) (H : Type) :=
    (Fin m → Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair) × H

variable {H : Type} [Fintype H] [DecidableEq H]

def neumannDataOracle (m : ℕ) (U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace m H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace m H) ℂ :=
  Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix (Fin m → Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair) (Fin m → Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair) ℂ) U

def neumannPairOracle (U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H) ℂ :=
  Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair ℂ) U

def neumannPairWord (P : Matrix H H ℂ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H)) :=
  [.gate (Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1 - P))), .forward,
    .gate (Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P)), .backward]

/-- The independent right lift preserves matrix multiplication. -/
private theorem right_lift_mul (V W : Matrix (Bool × H) (Bool × H) ℂ) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (V * W) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight V * Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight W := by
  simp only [Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight_eq]
  rw [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]
  congr 1
  simp only [Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.one_mul]

omit [Fintype H] [DecidableEq H] in

/-- The independent right lift of the data gate equals the Neumann pair oracle. -/
private theorem right_lift_data (U : Matrix H H ℂ) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Bool Bool ℂ) U) =
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U := by
  ext ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩
  simp [Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_apply,
    Prod.mk.injEq, ite_mul]
  split_ifs <;> simp_all

/-- An identity-ancilla data gate intertwines with the encoding fiber embedding. -/
theorem neumann_fiber_data (K : Type) [Fintype K] [DecidableEq K]
    (seed : K) (U : Matrix H H ℂ) :
    Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix K K ℂ) U * Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed = Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed * U := by
  ext ⟨a,i⟩ j
  by_cases ha : a = seed <;>
    simp [Matrix.mul_apply, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_apply,
      Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_apply, Prod.mk.injEq, ite_mul, mul_ite, ha]

/-- The adjoint encoding fiber intertwines an identity-ancilla data gate with the data matrix. -/
theorem neumann_fiber_data_left (K : Type) [Fintype K] [DecidableEq K]
    (seed : K) (U : Matrix H H ℂ) :
    (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed)ᴴ * Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix K K ℂ) U = U * (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed)ᴴ := by
  have h :=
      congrArg Matrix.conjTranspose
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fiber_data K seed Uᴴ)
  simpa only [Matrix.conjTranspose_mul, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose] using h

/-- The false-fiber corner of `cppNot P` is the complement of `P`. -/
private theorem cpp_corner (P : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) = 1 - P := by
  ext i j
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.compress_encodingFiber_eq]
  rfl

/-- The all-false corner of the Neumann pair word is the projected oracle-complement-adjoint
product. -/
theorem neumann_pair_word_corner (P U : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) = P * U * (1-P) * Uᴴ := by
  let V := Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Bool Bool ℂ) U
  have hd : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle Uᴴ = (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U)ᴴ := by
    simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle,
        Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]
  have he : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) *
        Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (V * Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P * Vᴴ) := by
    simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
      right_lift_mul, V, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one,
      right_lift_data, hd, Matrix.mul_assoc]
  rw [he]
  have hi := (Qatlib.Concepts.BlockEncoding.EncodingCore.independent_ancilla_lift_laws false false (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P))
    (V * Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P * Vᴴ)).2.2.2.2
  change Qatlib.Concepts.Execution.WorkspaceCP.compress
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) _
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) = _ at hi
  rw [hi, cpp_corner]
  have hc : Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) (V * Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P * Vᴴ) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) =
      U * (1-P) * Uᴴ := by
    simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc, V, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
      Matrix.conjTranspose_one]
    rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false)ᴴ, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fiber_data_left,
      Matrix.mul_assoc U, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fiber_data Bool false Uᴴ]
    simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc] using
      congrArg (fun T : Matrix H H ℂ => U * T * Uᴴ) (cpp_corner P)
  have hp : (1 : Matrix H H ℂ) - (1-P) = P := by abel
  rw [hc, hp]
  simp only [Matrix.mul_assoc]

/-- The complement of an orthogonal projector is an orthogonal projector. -/
private theorem complement_projector {P : Matrix H H ℂ} (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector (1-P) := by
  constructor
  · calc (1-P)*(1-P) = 1-P-P+P*P := by noncomm_ring
      _ = 1-P := by rw [hP.1]; abel
  · change (1-P)ᴴ = 1-P
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, show Pᴴ = P from hP.2]

/-- The Neumann pair word is well formed when `P` is an orthogonal projector. -/
theorem neumann_pair_word_legal (P : Matrix H H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P) := by
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
  exact ⟨Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft_unitary (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot_unitary (complement_projector hP)),
    Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight_unitary (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot_unitary hP)⟩

omit [Fintype H] [DecidableEq H] in

/-- Lifting the Neumann pair oracle to any fresh slot gives the shared Neumann data oracle. -/
theorem neumann_fresh_data (m : ℕ) (j : Fin m) (U : Matrix H H ℂ) :
    Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U) = Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U := by
  ext ⟨f,i⟩ ⟨g,k⟩
  simp only [Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Foundations.PureStateMath.TensorGate,
    Matrix.of_apply, Matrix.kronecker_apply, Matrix.one_apply]
  by_cases he : f = g
  · subst g
    simp
  · by_cases hj : f j = g j
    · have hn : ¬ ∀ l : Fin m, l ≠ j → f l = g l := by
        intro h
        apply he
        funext l
        by_cases hl : l = j
        · simpa only [hl] using hj
        · exact h l hl
      simp [he, hj, hn]
    · simp [he, hj]

omit [Fintype H] [DecidableEq H] in
/-- Fresh lifting commutes with conjugate transpose. -/
theorem neumann_fresh_adjoint [Fintype H] [DecidableEq H] (m : ℕ) (j : Fin m)
    (V : Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannFlagPair × H) ℂ) :
    Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j Vᴴ = (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j V)ᴴ := by
  simp only [Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_reindex, Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Matrix.conjTranspose_reindex,
    Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]

def freshNeumannLayer {m : ℕ} (j : Fin m) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace m H)) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P)

def freshNeumannBranchWord (m : ℕ) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace m H)) :=
  .backward :: (List.ofFn (fun j : Fin m => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P)).reverse.flatten

/-- Evaluating a fresh Neumann layer gives the fresh lift of the evaluated pair word. -/
private theorem layer_evaluate {m : ℕ} (j : Fin m) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P) =
      Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P)) := by
  rw [← Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fresh_data m j U]
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_one j)
    (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_mul j) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fresh_adjoint m j) _ _

omit [Fintype H] in

/-- A fresh Neumann layer uses two adjoint queries and two explicit gates. -/
private theorem layer_cost {m : ℕ} (j : Fin m) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P) = 2 ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P) = 2 := by
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts
      (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j)
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P)

/-- A fresh Neumann layer is well formed when `P` is an orthogonal projector. -/
private theorem layer_legal {m : ℕ} (j : Fin m) (P : Matrix H H ℂ)
    (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (fun _ h => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_unitary j h)
    (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_pair_word_legal P hP)

/-- The reversed concatenation of fresh layers evaluates to their ordered lifted product, with
two queries and gates per layer and conditional well-formedness. -/
private theorem layers_properties {m : ℕ} (js : List (Fin m)) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U) ((js.map (fun j => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P)).reverse.flatten) =
      (js.map (fun j => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P)))).foldl
        (fun acc V => V * acc) 1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount ((js.map (fun j => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P)).reverse.flatten) = 2 * js.length ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount ((js.map (fun j => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P)).reverse.flatten) = 2 * js.length ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P →
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit ((js.map (fun j => Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannLayer j P)).reverse.flatten)) := by
  induction js with
  | nil => exact ⟨rfl, rfl, rfl, fun _ => Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil⟩
  | cons j js ih =>
    simp only [List.map_cons, List.reverse_cons, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, ih.1, layer_evaluate, List.foldl_cons, Matrix.mul_one]
      exact (Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc _ _).symm
    · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, ih.2.1, (layer_cost j P).1, List.length_cons]
      omega
    · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, ih.2.2.1, (layer_cost j P).2, List.length_cons]
      omega
    · intro hP
      exact (ih.2.2.2 hP).append (layer_legal j P hP)

/-- The fresh Neumann branch has twice the exponent plus one queries, twice the exponent gates,
and is well formed for an orthogonal projector. -/
theorem fresh_neumann_branch_cost_legal (m : ℕ) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord m P) = 2*m+1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord m P) = 2*m ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P → Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord m P)) := by
  have h := layers_properties (List.ofFn (fun j : Fin m => j)) P (1 : Matrix H H ℂ)
  simp only [List.length_ofFn, List.map_ofFn, Function.comp_def] at h
  exact ⟨by simpa only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount] using
      congrArg (·+1) h.2.1,
    h.2.2.1, fun hp => (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff _).mpr (h.2.2.2 hp)⟩

/-- The fresh Neumann branch corner is the oracle adjoint multiplied by the corresponding power
of the projected defect product. -/
theorem fresh_neumann_branch_corner (m : ℕ) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin m => (false,false)))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord m P))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin m => (false,false))) =
        Uᴴ * (P * U * (1-P) * Uᴴ)^m := by
  have h := (layers_properties (List.ofFn (fun j : Fin m => j)) P U).1
  simp only [List.map_ofFn, Function.comp_def] at h
  have hc := Qatlib.Concepts.OperatorAccess.EncodedAccess.fresh_product_corner (List.ofFn (fun j : Fin m => j))
    (List.nodup_ofFn.mpr Function.injective_id) (false,false)
    (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairOracle U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannPairWord P))
  simp only [List.length_ofFn, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_pair_word_corner, List.map_ofFn,
    Function.comp_def] at hc
  simp only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix]
  rw [h]
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress,
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin m => (false,false)))ᴴ,
    Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_fiber_data_left]
  simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc] using
      congrArg (Uᴴ * ·) hc

variable {I : Type} [Fintype I] [DecidableEq I]

def freshNeumannFrame (m : ℕ) (F : Matrix H I ℂ) :
    Matrix (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace m H) I ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (fun _ : Fin m => (false,false)) * F

/-- Compressing the oracle-conjugated frame complement gives the left defect of the compressed
unitary. -/
theorem neumann_frame_defect (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress F (U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) F =
      1 - Qatlib.Concepts.Execution.WorkspaceCP.compress F U F * (Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ := by
  have hu : U*Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have hf : Fᴴ * F = 1 := hF
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, hu, Matrix.one_mul, hf]

/-- Powers of the frame-projected defect product intertwine with the frame and its compressed
matrix powers. -/
theorem neumann_frame_power (U : Matrix H H ℂ) (F : Matrix H I ℂ) (m : ℕ) :
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F * U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ)^m * F =
      F * (Qatlib.Concepts.Execution.WorkspaceCP.compress F (U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) F)^m := by
  have h : (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F * U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) * F =
      F * Qatlib.Concepts.Execution.WorkspaceCP.compress F (U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) F := by
    simp only [Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector,
        Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h,
      Matrix.mul_assoc, ← pow_succ']

/-- For a unitary oracle and an isometric frame, the fresh branch exactly encodes the compressed
adjoint multiplied by a power of its left defect. -/
theorem fresh_neumann_branch_encoding (m : ℕ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      ((Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ * (1-Qatlib.Concepts.Execution.WorkspaceCP.compress F U F*(Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ)^m)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame m F) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame m F) := by
  have hw := (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.fresh_neumann_branch_cost_legal m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)).2.2
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector hF)
  have hq : Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U ∈ unitaryGroup (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.NeumannBranchSpace m H) ℂ :=
    Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem hU
  have he :
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame m F) :=
      Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _) hF
  refine ⟨hw.evaluate_unitary hq, he, he, ?_⟩
  have hc :=
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.fresh_neumann_branch_corner m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) U
  have hcomp : Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame m F)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumannDataOracle m U) (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannBranchWord m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)))
      (Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame m F) = Fᴴ * (Uᴴ * (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F * U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^m) * F := by
    simpa only [Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.freshNeumannFrame, Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      using congrArg (fun T : Matrix H H ℂ => Fᴴ*T*F) hc
  rw [hcomp, Matrix.mul_assoc, Matrix.mul_assoc,
      Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_frame_power, Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram.neumann_frame_defect U F hU hF]
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end Qatlib.Concepts.NonNormalSpec.ResolventWord.NeumannProgram
