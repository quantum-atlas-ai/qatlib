/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OperatorAccess.EncodedAccess.FreshPositivePower
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
import Qatlib.Concepts.QspSimulation.WordModel.CPPAdjointDefs
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

/-!
Fresh flags for the inverse Neumann word.


The original definitions, proofs, and accounting for the same word are retained.
Known matrix macros do not establish elementary gate synthesis; input preparation,
retries, and bit costs require separate analysis.
-/

/-! Explicit paid query words for the fresh-flag inverse branches. The fixed
gates depend only on the supplied known projector, never on the queried matrix.
This is a matrix-macro compiler, distinct from elementary gate synthesis. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
open scoped BigOperators Kronecker

/-- Abbreviation for Neumann Flag Pair in the fresh flag word model. -/
abbrev NeumannFlagPair := Bool × Bool
/-- Abbreviation for Neumann Branch Space in the fresh flag word model. -/
abbrev NeumannBranchSpace (m : ℕ) (H : Type) := (Fin m → Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair) × H

variable {H : Type} [Fintype H] [DecidableEq H]

/-- The same supplied data oracle on every flag sector. -/
def neumannDataOracle (m : ℕ) (U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace m H) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace m H) ℂ :=
  Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix (Fin m → Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair) (Fin m → Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair) ℂ) U

/-- Construction for neumann Pair Oracle in the fresh flag word model. -/
def neumannPairOracle (U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) ℂ :=
  Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U

/-- Product order: physically query backward, flag I-P, query forward, flag P. -/
def neumannPairWord (P : Matrix H H ℂ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H)) :=
  [.gate (Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1 - P))), .forward,
    .gate (Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P)), .backward]

/-- The exact `right_lift_mul` invariant under the original hypotheses and resource conventions. -/
private theorem right_lift_mul (V W : Matrix (Bool × H) (Bool × H) ℂ) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (V * W) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight V * Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight W := by
  simp only [Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight_eq]
  rw [← Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul]
  congr 1
  simp only [Qatlib.Foundations.PureStateMath.tensorGate_mul, Matrix.one_mul]

omit [Fintype H] [DecidableEq H] in
/-- The exact `right_lift_data` invariant under the original hypotheses and resource conventions. -/
private theorem right_lift_data (U : Matrix H H ℂ) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Bool Bool ℂ) U) =
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U := by
  ext ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩
  simp [Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_apply,
    Prod.mk.injEq, ite_mul]
  split_ifs <;> simp_all

/-- The exact `neumann_fiber_data` invariant under the original hypotheses and resource conventions. -/
theorem neumann_fiber_data (K : Type) [Fintype K] [DecidableEq K]
    (seed : K) (U : Matrix H H ℂ) :
    Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix K K ℂ) U * Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed = Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed * U := by
  ext ⟨a,i⟩ j
  by_cases ha : a = seed <;>
    simp [Matrix.mul_apply, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_apply,
      Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_apply, Prod.mk.injEq, ite_mul, mul_ite, ha]

/-- The exact `neumann_fiber_data_left` invariant under the original hypotheses and resource conventions. -/
theorem neumann_fiber_data_left (K : Type) [Fintype K] [DecidableEq K]
    (seed : K) (U : Matrix H H ℂ) :
    (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed)ᴴ * Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix K K ℂ) U = U * (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) seed)ᴴ := by
  have h := congrArg Matrix.conjTranspose (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data K seed Uᴴ)
  simpa only [Matrix.conjTranspose_mul, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose] using h

/-- The exact `cpp_corner` invariant under the original hypotheses and resource conventions. -/
private theorem cpp_corner (P : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) = 1 - P := by
  ext i j
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.compress_encodingFiber_eq]
  rfl

/-- The actual two-query body has corner P U (I-P) U†; no desired corner input. -/
theorem neumann_pair_word_corner (P U : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) = P * U * (1-P) * Uᴴ := by
  let V := Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Bool Bool ℂ) U
  have hd : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle Uᴴ = (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U)ᴴ := by
    simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]
  have he : Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P) =
      Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft (K := Bool) (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P)) *
        Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight (J := Bool) (V * Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P * Vᴴ) := by
    simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix, Matrix.mul_one,
      right_lift_mul, V, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one,
      right_lift_data, hd, Matrix.mul_assoc]
  rw [he]
  have hi := (Qatlib.Concepts.BlockEncoding.EncodingCore.independent_ancilla_lift_laws false false (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot (1-P))
    (V * Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P * Vᴴ)).2.2.2.2
  change Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) _ (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) = _ at hi
  rw [hi, cpp_corner]
  have hc : Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) (V * Qatlib.Concepts.QsvtCore.QsVtMain.cppNot P * Vᴴ) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false) =
      U * (1-P) * Uᴴ := by
    simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc, V, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose,
      Matrix.conjTranspose_one]
    rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber false)ᴴ, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data_left,
      Matrix.mul_assoc U, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data Bool false Uᴴ]
    simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc] using
      congrArg (fun T : Matrix H H ℂ => U * T * Uᴴ) (cpp_corner P)
  have hp : (1 : Matrix H H ℂ) - (1-P) = P := by abel
  rw [hc, hp]
  simp only [Matrix.mul_assoc]

/-- The exact `complement_projector` invariant under the original hypotheses and resource conventions. -/
private theorem complement_projector {P : Matrix H H ℂ} (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector (1-P) := by
  constructor
  · calc (1-P)*(1-P) = 1-P-P+P*P := by noncomm_ring
      _ = 1-P := by rw [hP.1]; abel
  · change (1-P)ᴴ = 1-P
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, show Pᴴ = P from hP.2]

/-- The exact `neumann_pair_word_legal` invariant under the original hypotheses and resource conventions. -/
theorem neumann_pair_word_legal (P : Matrix H H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P) := by
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff,
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
  exact ⟨Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftLeft_unitary (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot_unitary (complement_projector hP)),
    Qatlib.Concepts.BlockEncoding.EncodingCore.independentLiftRight_unitary (Qatlib.Concepts.QsvtCore.QsVtMain.cppNot_unitary hP)⟩

omit [Fintype H] [DecidableEq H] in
/-- The exact `neumann_fresh_data` invariant under the original hypotheses and resource conventions. -/
theorem neumann_fresh_data (m : ℕ) (j : Fin m) (U : Matrix H H ℂ) :
    Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) = Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U := by
  ext ⟨f,i⟩ ⟨g,k⟩
  simp only [Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.TensorGate,
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

/-- The exact `neumann_fresh_adjoint` invariant under the original hypotheses and resource conventions. -/
theorem neumann_fresh_adjoint (m : ℕ) (j : Fin m)
    (V : Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) ℂ) :
    Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j Vᴴ = (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j V)ᴴ := by
  simp only [Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_reindex, Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Matrix.conjTranspose_reindex,
    Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]

/-- Every layer updates its own fresh flag pair. Syntax contains no unknown U. -/
def freshNeumannLayer {m : ℕ} (j : Fin m) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace m H)) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P)

/-- The final inverse query follows all m layers in physical execution order. -/
def freshNeumannBranchWord (m : ℕ) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace m H)) :=
  .backward :: (List.ofFn (fun j : Fin m => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P)).reverse.flatten


/-- The exact `layer_evaluate` invariant under the original hypotheses and resource conventions. -/
private theorem layer_evaluate {m : ℕ} (j : Fin m) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P) =
      Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P)) := by
  rw [← Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fresh_data m j U]
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_one j)
    (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_mul j) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fresh_adjoint m j) _ _

omit [Fintype H] in
/-- The exact `layer_cost` invariant under the original hypotheses and resource conventions. -/
private theorem layer_cost {m : ℕ} (j : Fin m) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P) = 2 ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P) = 2 := by
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P)

/-- The exact `layer_legal` invariant under the original hypotheses and resource conventions. -/
private theorem layer_legal {m : ℕ} (j : Fin m) (P : Matrix H H ℂ)
    (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (fun _ h => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_unitary j h)
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_pair_word_legal P hP)

/-- The exact `layers_properties` invariant under the original hypotheses and resource conventions. -/
private theorem layers_properties {m : ℕ} (js : List (Fin m)) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U) ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P)).reverse.flatten) =
      (js.map (fun j => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P)))).foldl
        (fun acc V => V * acc) 1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P)).reverse.flatten) = 2 * js.length ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P)).reverse.flatten) = 2 * js.length ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P →
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannLayer j P)).reverse.flatten)) := by
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

/-- The declared literal branch retains two queries and two known flag gates per
layer, plus the final backward query. -/
theorem fresh_neumann_branch_cost_legal (m : ℕ) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord m P) = 2*m+1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord m P) = 2*m ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P → Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord m P)) := by
  have h := layers_properties (List.ofFn (fun j : Fin m => j)) P (1 : Matrix H H ℂ)
  simp only [List.length_ofFn, List.map_ofFn, Function.comp_def] at h
  exact ⟨by simpa only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount] using
      congrArg (·+1) h.2.1,
    h.2.2.1, fun hp => (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff _).mpr (h.2.2.2 hp)⟩

/-- The actual full branch matrix has clean H-corner U†(P U(I-P)U†)^m.
The algebraic fresh-power lemma is used only for semantics, not its zero-query ledger. -/
theorem fresh_neumann_branch_corner (m : ℕ) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin m => (false,false)))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord m P))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin m => (false,false))) =
        Uᴴ * (P * U * (1-P) * Uᴴ)^m := by
  have h := (layers_properties (List.ofFn (fun j : Fin m => j)) P U).1
  simp only [List.map_ofFn, Function.comp_def] at h
  have hc := Qatlib.Concepts.OperatorAccess.EncodedAccess.fresh_product_corner (List.ofFn (fun j : Fin m => j))
    (List.nodup_ofFn.mpr Function.injective_id) (false,false)
    (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P))
  simp only [List.length_ofFn, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_pair_word_corner, List.map_ofFn,
    Function.comp_def] at hc
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix]
  rw [h]
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin m => (false,false)))ᴴ,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data_left]
  simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc] using congrArg (Uᴴ * ·) hc

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Known common frame plus the literal fresh flag seed. -/
def freshNeumannFrame (m : ℕ) (F : Matrix H I ℂ) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace m H) I ℂ :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := H) (fun _ : Fin m => (false,false)) * F

/-- The exact `neumann_frame_defect` invariant under the original hypotheses and resource conventions. -/
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

/-- The exact `neumann_frame_power` invariant under the original hypotheses and resource conventions. -/
theorem neumann_frame_power (U : Matrix H H ℂ) (F : Matrix H I ℂ) (m : ℕ) :
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F * U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ)^m * F =
      F * (Qatlib.Concepts.Execution.WorkspaceCP.compress F (U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) F)^m := by
  have h : (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F * U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) * F =
      F * Qatlib.Concepts.Execution.WorkspaceCP.compress F (U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) * Uᴴ) F := by
    simp only [Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector, Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h,
      Matrix.mul_assoc, ← pow_succ']

/-- The same legal, charged branch encodes S†(I-SS†)^m in the original common
frame. No corner, inverse, defect norm or queried matrix is stored in a fixed gate. -/
theorem fresh_neumann_branch_encoding (m : ℕ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      ((Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ * (1-Qatlib.Concepts.Execution.WorkspaceCP.compress F U F*(Qatlib.Concepts.Execution.WorkspaceCP.compress F U F)ᴴ)^m)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F) := by
  have hw := (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.fresh_neumann_branch_cost_legal m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)).2.2
    (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector_isOrthogonalProjector hF)
  have hq : Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U ∈ unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace m H) ℂ :=
    Qatlib.Foundations.PureStateMath.tensorGate_unitary (unitaryGroup _ ℂ).one_mem hU
  have he : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F) := Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry _) hF
  refine ⟨hw.evaluate_unitary hq, he, he, ?_⟩
  change Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F) _ (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F) = _
  have hc := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.fresh_neumann_branch_corner m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F) U
  have hcomp : Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F)
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle m U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannBranchWord m (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame m F) = Fᴴ * (Uᴴ * (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F * U * (1-Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector F)*Uᴴ)^m) * F := by
    simpa only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.freshNeumannFrame, Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      using congrArg (fun T : Matrix H H ℂ => Fᴴ*T*F) hc
  rw [hcomp, Matrix.mul_assoc, Matrix.mul_assoc, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_frame_power, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_frame_defect U F hU hF]
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
