/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearch

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- For a transition matrix, establishes the detection program counts, initial marked mass, and
unitarity of the marked reflection. -/
theorem dev_source_detection_account {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (j : I) (K : ℕ) (hP : IsTransitionMatrix P) :
    SourceDetectionAccount P S j K := by
  refine ⟨detectionProgram_actual_counts j K, ?_, ?_⟩
  · exact (detection_marked_initial_mass P S hP).2
  · exact devMarkedReflection_unitary S

/-- Establishes clause five, combining the source detection account, reachable spectrum,
complete-graph gap, and bipartite walk cost ledger. -/
theorem sourceDetection_clause5_endpoint : clause5Spec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V K p S k
    exact Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.clause5_complete K p S k
  · intro I _ _ _ P hP
    exact dev_reachable_spectrum P hP
  · intro n hn
    exact complete_graph_symmetric_chain_gap n hn
  · intro a ha
    obtain ⟨L, hL⟩ := bipartite_walk_ledger a ha
    refine ⟨L, ?_⟩
    exact ⟨hL.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.2.2.1⟩

/-- Establishes clause six, combining marked-mass identities, the find endpoint, and the
relation carrier. -/
theorem sourceDetection_clause6_endpoint : clause6Spec := by
  refine ⟨?_, ?_, ?_⟩
  · intro V K p S k
    exact Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.clause6_complete K p S k
  · intro I _ _ W ψ S Mq k t
    exact dev_find_endpoint W ψ S Mq k t
  · exact dev_relation_carrier

/-- Establishes clause seven, combining the marked-reflection execution identity, uniform source
statement, and vanishing bipartite endpoint embedding. -/
theorem sourceDetection_clause7_endpoint : clause7Spec := by
  refine ⟨?_, ?_, ?_⟩
  · intro V K p S k
    exact (Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution.clause7_complete K p S k).1
  · exact dev_uniform_source
  · intro H I J _ _ _ _ _ _ A B hA hB
    exact bipartite_tau_endpoint_vanishes_dev A B hA hB

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
