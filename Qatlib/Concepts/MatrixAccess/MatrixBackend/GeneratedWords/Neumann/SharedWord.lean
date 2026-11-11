/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.ConditionalLayer
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
A shared oracle word for uniform Neumann powers.

Adapted from TiMidlY's OQ #91 at `4c76e75a5a94e48c8d3c2705569f6e0499784fc7`.
The original definitions, proofs, and accounting for the same word are retained.
Known matrix macros do not establish elementary gate synthesis; input preparation,
retries, and bit costs require separate analysis.
-/

/-! One shared flag workspace for the coherent Neumann branches. Every data
call remains an explicit query. Known branch predicates affect only flag gates.
This module uses matrix macros, not an elementary-gate refinement claim. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
open scoped BigOperators Kronecker

variable {H J : Type} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- A fixed label/flag wire permutation, independent of all queried data. -/
def neumannLabelWire (J H : Type) : J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H) ≃ Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype H] [DecidableEq H] [Fintype J] in
/-- The exact `label_wire_data` invariant under the original hypotheses and resource conventions. -/
private theorem label_wire_data (U : Matrix H H ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U)) =
      Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U) := by
  ext ⟨f,j,h⟩ ⟨g,k,i⟩
  simp [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle,
    Qatlib.Foundations.PureStateMath.TensorGate, Matrix.one_apply, ite_mul, mul_ite]

/-- The exact `wire_one` invariant under the original hypotheses and resource conventions. -/
private theorem wire_one : Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H)
    (1 : Matrix (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H)) (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H)) ℂ) = 1 :=
  Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one _

/-- The exact `wire_mul` invariant under the original hypotheses and resource conventions. -/
private theorem wire_mul (U V : Matrix (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H))
    (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H)) ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H) (U*V) =
      Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H) U * Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H) V :=
  Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul _ _ _

omit [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J] in
/-- The exact `wire_adjoint` invariant under the original hypotheses and resource conventions. -/
private theorem wire_adjoint (U : Matrix (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H))
    (J × (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × H)) ℂ) :
    Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H) Uᴴ = (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H) U)ᴴ := by
  simp only [Qatlib.Foundations.PureStateMath.BornBridge.relabelGate, Matrix.conjTranspose_reindex]

/-- Different layers may have different known predicates on the same label. -/
def uniformNeumannLayer {M : ℕ} (j : Fin M) (active : J → Bool) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace M (J × H))) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j)
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P))

/-- Construction for selected Body in the shared word model. -/
private def selectedBody (active : J → Bool) (P U : Matrix H H ℂ) :
    Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H)) ℂ :=
  Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H)
    (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P))

/-- The exact `uniform_layer_evaluate` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_layer_evaluate {M : ℕ} (j : Fin M) (active : J → Bool)
    (P U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle M (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j active P) =
      Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (selectedBody active P U) := by
  rw [← Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fresh_data M j]
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer selectedBody
  rw [Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j) (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_one j) (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_mul j)
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fresh_adjoint M j)]
  rw [← label_wire_data]
  rw [Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate _ wire_one wire_mul wire_adjoint]

omit [Fintype H] [Fintype J] in
/-- The exact `uniform_layer_cost` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_layer_cost {M : ℕ} (j : Fin M) (active : J → Bool)
    (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j active P) = 2 ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j active P) = 2 := by
  have h₁ := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j)
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P))
  have h₂ := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannLabelWire J H)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selectedNeumannPairWord active P)
  exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- The exact `uniform_layer_legal` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_layer_legal {M : ℕ} (j : Fin M) (active : J → Bool)
    (P : Matrix H H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j active P) := by
  have h := (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selected_neumann_pair_word active P 1 (unitaryGroup H ℂ).one_mem hP).2.2.2
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed _ (fun _ hu => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_unitary j hu)
    (Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed _ (fun _ hu => Qatlib.Concepts.BlockEncoding.EncodingCore.relabelGate_mem_unitary hu _) h)

/-- The exact `varying_preserves` invariant under the original hypotheses and resource conventions. -/
private theorem varying_preserves {M : ℕ} (j : Fin M) (js : List (Fin M))
    (hj : j ∉ js) (V : Fin M → Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H))
      (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H)) ℂ) :
    Qatlib.Concepts.OperatorAccess.EncodedAccess.FreshPreserves j ((js.map (fun l => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift l (V l))).foldl (fun acc W => W*acc) 1) := by
  induction js with
  | nil => exact Qatlib.Concepts.OperatorAccess.EncodedAccess.FreshPreserves.one j
  | cons l js ih =>
    have hjl : j ≠ l := by intro he; subst l; exact hj List.mem_cons_self
    have ht : j ∉ js := fun h => hj (List.mem_cons_of_mem l h)
    simp only [List.map_cons, List.foldl_cons]
    rw [Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc, Matrix.mul_one]
    exact (ih ht).mul (Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift_preserves j l hjl (V l))

/-- The exact `varying_corner` invariant under the original hypotheses and resource conventions. -/
private theorem varying_corner {M : ℕ} (js : List (Fin M)) (hn : js.Nodup)
    (V : Fin M → Matrix (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair × (J × H)) ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin M => (false,false)))
      ((js.map (fun j => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (V j))).foldl (fun acc W => W*acc) 1)
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin M => (false,false))) =
      (js.map (fun j => Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) (V j)
        (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)))).foldl (fun acc W => W*acc) 1 := by
  induction js with
  | nil =>
    simpa [Qatlib.Concepts.Execution.WorkspaceCP.compress,Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry] using Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_isIsometry (I := J × H)
      (fun _ : Fin M => (false,false))
  | cons j js ih =>
    have hnot := (List.nodup_cons.mp hn).1
    have htail := (List.nodup_cons.mp hn).2
    simp only [List.map_cons, List.foldl_cons]
    rw [Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc, Matrix.mul_one,
      Qatlib.Concepts.OperatorAccess.EncodedAccess.fresh_corner_product j (false,false) _ (V j) (varying_preserves j js hnot V), ih htail]
    simpa only [Matrix.mul_one] using (Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc
      (js.map (fun l => Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) (V l) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false))))
      (Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) (V j) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)))).symm

/-- The exact `selected_body_corner` invariant under the original hypotheses and resource conventions. -/
private theorem selected_body_corner (active : J → Bool) (P U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) (selectedBody active P U) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (false,false)) =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun k => if active k then P*U*(1-P)*Uᴴ else 1) := by
  have h := (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.selected_neumann_pair_word active P U hU hP).1
  unfold selectedBody
  change Qatlib.Concepts.Execution.WorkspaceCP.compress _ (Qatlib.Foundations.PureStateMath.BornBridge.relabelGate _
    (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannFlagPair ℂ) U)) _)) _ = _
  rw [h]
  ext ⟨k,i⟩ ⟨l,t⟩
  rw [Qatlib.Concepts.BlockEncoding.EncodingCore.compress_encodingFiber_eq]
  change (if k = l then
      (if active k then Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairOracle U) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannPairWord P) else 1)
        ((false,false),i) ((false,false),t) else 0) =
    if k = l then (if active k then P*U*(1-P)*Uᴴ else 1) i t else 0
  by_cases he : k = l
  · subst l
    cases ha : active k
    · simp [Matrix.one_apply, Prod.mk.injEq]
    · have hc := congrFun (congrFun (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_pair_word_corner P U) i) t
      simpa only [ha, ↓reduceIte, Qatlib.Concepts.BlockEncoding.EncodingCore.compress_encodingFiber_eq] using hc
  · simp [he]


/-- The exact `uniform_layers_properties` invariant under the original hypotheses and resource conventions. -/
private theorem uniform_layers_properties {M : ℕ} (js : List (Fin M))
    (active : Fin M → J → Bool) (P U : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle M (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := J) U))
      ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j (active j) P)).reverse.flatten) =
      (js.map (fun j => Qatlib.Concepts.OperatorAccess.EncodedAccess.freshLift j (selectedBody (active j) P U))).foldl (fun acc V => V*acc) 1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j (active j) P)).reverse.flatten) =
      2*js.length ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j (active j) P)).reverse.flatten) =
      2*js.length ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P →
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit ((js.map (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j (active j) P)).reverse.flatten)) := by
  induction js with
  | nil => exact ⟨rfl,rfl,rfl,fun _ => Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil⟩
  | cons j js ih =>
    simp only [List.map_cons, List.reverse_cons, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, ih.1, uniform_layer_evaluate, List.foldl_cons, Matrix.mul_one]
      exact (Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc _ _).symm
    · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, ih.2.1, (uniform_layer_cost j (active j) P).1,
        List.length_cons]
      omega
    · rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, ih.2.2.1, (uniform_layer_cost j (active j) P).2,
        List.length_cons]
      omega
    · intro hp
      exact (ih.2.2.2 hp).append (uniform_layer_legal j (active j) P hp)

/-- The exact `select_fold` invariant under the original hypotheses and resource conventions. -/
private theorem select_fold {M : ℕ} (js : List (Fin M))
    (V : Fin M → J → Matrix H H ℂ) :
    (js.map (fun j => Qatlib.Concepts.BlockEncoding.LCU.select (V j))).foldl (fun acc W => W*acc) 1 =
      Qatlib.Concepts.BlockEncoding.LCU.select (fun k => (js.map (fun j => V j k)).foldl (fun acc W => W*acc) 1) := by
  induction js with
  | nil => exact Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_one.symm
  | cons j js ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc, Matrix.mul_one, ih, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext k
    simpa only [Matrix.mul_one] using
      (Qatlib.Concepts.OperatorAccess.EncodedAccess.positiveMacro_fold_acc (js.map (fun j => V j k)) (V j k)).symm

/-- The exact `prefix_power` invariant under the original hypotheses and resource conventions. -/
private theorem prefix_power (K : Matrix H H ℂ) (M k : ℕ) :
    (List.ofFn (fun j : Fin M => if j.val < k then K else 1)).foldl (fun acc W => W*acc) 1 =
      K^(min M k) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Fin.val_castSucc, Fin.val_last]
    change (if M < k then K else 1) *
      (List.ofFn (fun j : Fin M => if j.val < k then K else 1)).foldl
        (fun acc W : Matrix H H ℂ => W*acc) 1 = _
    rw [ih]
    by_cases he : M < k
    · rw [ite_eq_left he, min_eq_left (by omega), min_eq_left (by omega), ← pow_succ']
    · rw [ite_eq_right he, Matrix.one_mul, min_eq_right (by omega), min_eq_right (by omega)]

/-- One literal query word over a common flag workspace for all b branches. -/
def sharedNeumannWord (b : ℕ) (P : Matrix H H ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × H))) :=
  .backward :: (List.ofFn (fun j : Fin (b-1) =>
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannLayer j (fun k : Fin b => decide (j.val < k.val)) P)).reverse.flatten

/-- The shared program pays its worst-case queries, including inactive labels. -/
theorem shared_neumann_word_cost_legal (b : ℕ) (hb : 0 < b) (P : Matrix H H ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord b P) = 2*b-1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord b P) = 2*(b-1) ∧
    (Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P → Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord b P)) := by
  have h := uniform_layers_properties (List.ofFn (fun j : Fin (b-1) => j))
    (fun (j : Fin (b-1)) (k : Fin b) => decide (j.val < k.val)) P (1 : Matrix H H ℂ)
  simp only [List.length_ofFn, List.map_ofFn, Function.comp_def] at h
  refine ⟨?_, h.2.2.1, fun hp => (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.backward_cons_iff _).mpr (h.2.2.2 hp)⟩
  change Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount _ + 1 = _
  omega


/-- The same flag workspace produces every requested power before averaging. -/
theorem shared_neumann_word_corner (b : ℕ) (hb : 0 < b) (P U : Matrix H H ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hP : Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement.IsOrthogonalProjector P) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin (b-1) => (false,false)))
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle (b-1) (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U)) (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord b P))
      (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin (b-1) => (false,false))) =
        Qatlib.Concepts.BlockEncoding.LCU.select (fun k : Fin b => Uᴴ*(P*U*(1-P)*Uᴴ)^k.val) := by
  let active := fun (j : Fin (b-1)) (k : Fin b) => decide (j.val < k.val)
  let js := List.ofFn (fun j : Fin (b-1) => j)
  have he := (uniform_layers_properties js active P U).1
  have hc := varying_corner js (List.nodup_ofFn.mpr Function.injective_id)
    (fun j => selectedBody (active j) P U)
  simp only [selected_body_corner _ P U hU hP] at hc
  rw [select_fold] at hc
  have hp : (fun k : Fin b =>
      (js.map (fun j => if active j k then P*U*(1-P)*Uᴴ else 1)).foldl (fun acc W => W*acc) 1) =
      fun k => (P*U*(1-P)*Uᴴ)^k.val := by
    funext k
    simp only [js, List.map_ofFn, Function.comp_def, active, decide_eq_true_eq]
    rw [prefix_power, min_eq_right (by omega : k.val ≤ b-1)]
  rw [hp] at hc
  simp only [js, List.map_ofFn, Function.comp_def, active] at he hc
  simp only [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.sharedNeumannWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix]
  rw [he]
  simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumannDataOracle, Qatlib.Foundations.PureStateMath.tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (fun _ : Fin (b-1) => (false,false)))ᴴ,
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.neumann_fiber_data_left]
  have h := congrArg ((Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Fin b) U)ᴴ * ·) hc
  simpa only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.mul_assoc, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_adjoint,
    Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul] using h

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann
