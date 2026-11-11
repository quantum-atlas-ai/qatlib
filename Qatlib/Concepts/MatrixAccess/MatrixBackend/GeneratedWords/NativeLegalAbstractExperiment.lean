/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeNeumann
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeMultiNodeRelabel
import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.NativeWeightedLCUSlot
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.FreshFlagWord
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.SharedOriginalOracle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.UniformEncoding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! Local experiment: structural well-formedness at the macro level only. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped Kronecker

/-- The actual finite word or frame satisfies `abstract_substitute_legal` with all displayed legality, input and workspace hypotheses. -/
private theorem abstract_substitute_legal {D : Type} [Fintype D] [DecidableEq D]
    (body cs : List (AdjointStep D))
    (hbody : WellFormedAdjointCircuit body) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (substituteAdjointCircuit body cs) := by
  exact (substitute_adjoint_evaluate_cost (1 : Matrix D D ℂ) body cs).2.2.2 hbody hcs

/-- The actual finite word or frame satisfies `abstract_decEq_transport` with all displayed legality, input and workspace hypotheses. -/
private theorem abstract_decEq_transport {D : Type} [Fintype D]
    (d₁ d₂ : DecidableEq D) (cs : List (AdjointStep D)) :
    @WellFormedAdjointCircuit D _ d₁ cs → @WellFormedAdjointCircuit D _ d₂ cs := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  exact id

/-- The actual finite word or frame satisfies `abstract_lift_legal` with all displayed legality, input and workspace hypotheses. -/
private theorem abstract_lift_legal {T D : Type} [Fintype T] [DecidableEq T]
    [Fintype D] [DecidableEq D] (lift : Matrix T T ℂ → Matrix D D ℂ)
    (hlift : ∀ U, U ∈ unitaryGroup T ℂ → lift U ∈ unitaryGroup D ℂ)
    (body : List (AdjointStep T)) (hbody : WellFormedAdjointCircuit body) :
    WellFormedAdjointCircuit (phaseLiftWord lift body) :=
  phaseLiftWord_wellFormed lift hlift hbody

/-- The actual finite word or frame satisfies `abstract_weighted_legal` with all displayed legality, input and workspace hypotheses. -/
private theorem abstract_weighted_legal {J T : Type} [Fintype J] [DecidableEq J]
    [Fintype T] [DecidableEq T] [outer : DecidableEq (J × T)]
    (d : J → ℂ) (j₀ : J) (W : List (AdjointStep (J × T)))
    (hmass : 0 < coefficientMass d) (hW : WellFormedAdjointCircuit W) :
    WellFormedAdjointCircuit (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ W) := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  let body := Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotBody d W
  let cs := scaledLCUAdjointWord (H := T) d j₀
  have hP := prepareRegister_unitary (I := T) (coefficientPrepare_unitary d j₀ hmass)
  have hD : select (phaseAbsorbed d (fun _ => (1 : Matrix T T ℂ))) ∈
      unitaryGroup (J × T) ℂ :=
    Qatlib.Concepts.BlockEncoding.LCU.select_unitary _
      (phaseAbsorbed_unitary d _ (fun _ => (unitaryGroup T ℂ).one_mem))
  change WellFormedAdjointCircuit (substituteAdjointCircuit body cs)
  apply abstract_substitute_legal
  · exact (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff _ _).2 ⟨hD, hW⟩
  · simpa only [cs, scaledLCUAdjointWord, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
      Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil,
      and_true] using And.intro (adjoint_unitary hP) hP

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Typeclass instance for experiment Branch Dec Eq in the native legal abstract experiment model. -/
local instance experimentBranchDecEq (b : ℕ) : DecidableEq
    (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (J × (Reg 6 × H)))) := Classical.decEq _

/-- The actual finite word or frame satisfies `experiment_unitary_lift` with all displayed legality, input and workspace hypotheses. -/
private theorem experiment_unitary_lift {T : Type} [Fintype T] [DecidableEq T] (b : ℕ)
    [outer : DecidableEq (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × T))]
    (U : Matrix T T ℂ) (hU : U ∈ unitaryGroup T ℂ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b U ∈
      unitaryGroup (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × T)) ℂ := by
  have heq : outer = instDecidableEqProd := Subsingleton.elim _ _
  subst outer
  exact tensorGate_unitary (unitaryGroup _ ℂ).one_mem
    (Qatlib.Concepts.BlockEncoding.LCU.select_unitary _ (fun _ => hU))

/-- The actual finite word or frame satisfies `experiment_native_multinode_legal` with all displayed legality, input and workspace hypotheses. -/
theorem experiment_native_multinode_legal (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    WellFormedAdjointCircuit (nativeMultiNodeNeumannWord b hb F ps p slack) := by
  let P := rangeProjector (nativeMultiNodeFrame (J := J) F)
  have hp : IsOrthogonalProjector P :=
    rangeProjector_isOrthogonalProjector (nativeMultiNodeFrame_isometry (J := J) F hF)
  let cs := Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannWord b hb P
  let body := phaseLiftWord (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (nativeMultiNodeBodyWord (H := H) ps p slack)
  have hc := (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniform_neumann_word_cost_legal b hb P).2.2 hp
  have hbody := abstract_lift_legal (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.uniformNeumannOracle b) (experiment_unitary_lift b)
    (nativeMultiNodeBodyWord (H := H) ps p slack) (nativeMultiNodeBody_legal ps p slack)
  change WellFormedAdjointCircuit (substituteAdjointCircuit body cs)
  exact abstract_substitute_legal body cs hbody
    (abstract_decEq_transport instDecidableEqProd (experimentBranchDecEq b) cs hc)

/-- Typeclass instance for experiment Outer Dec Eq in the native legal abstract experiment model. -/
local instance experimentOuterDecEq (b : ℕ) : DecidableEq
    (J × Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.NeumannBranchSpace (b-1) (Fin b × (Reg 6 × H))) := Classical.decEq _

/-- The actual finite word or frame satisfies `experiment_relabeled_legal` with all displayed legality, input and workspace hypotheses. -/
theorem experiment_relabeled_legal (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F) :
    WellFormedAdjointCircuit (nativeMultiNodeRelabeledWord b hb F ps p slack) := by
  change WellFormedAdjointCircuit (phaseLiftWord
    (relabelGate (nativeMultiNodeLabelEquiv (J := J) (H := H) b))
    (nativeMultiNodeNeumannWord b hb F ps p slack))
  exact abstract_lift_legal _ (fun _ hu => relabelGate_mem_unitary hu _)
    _ (experiment_native_multinode_legal b hb F ps p slack hF)

/-- The actual finite word or frame satisfies `experiment_weighted_legal` with all displayed legality, input and workspace hypotheses. -/
theorem experiment_weighted_legal (b : ℕ) (hb : 0 < b)
    (F : Matrix H I ℂ) (ps : J → Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : J → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : J → Bool) (hF : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry F)
    (d : J → ℂ) (j₀ : J) (hmass : 0 < coefficientMass d) :
    WellFormedAdjointCircuit
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot.weightedLCUSlotWord d j₀ (nativeMultiNodeRelabeledWord b hb F ps p slack)) := by
  exact abstract_weighted_legal d j₀ _ hmass
    (experiment_relabeled_legal b hb F ps p slack hF)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
