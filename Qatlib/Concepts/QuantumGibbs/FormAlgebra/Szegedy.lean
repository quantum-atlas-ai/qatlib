/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.SzegedyDefs
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearch
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.Detection

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- Establishes `clause37Spec`, combining setup accounting, reachable spectrum, effective
bipartite neighbor programs, and walk cost accounting. -/
theorem clause37_endpoint : clause37Spec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V K p k
    exact Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess.clause37_complete K p k
  · intro I _ _ _ P hP
    exact dev_reachable_spectrum P hP
  · intro a ha
    exact bipartite_effectiveNeighborProgram a ha
  · intro a ha
    exact bipartite_walk_ledger a ha

/-- Establishes `clause38Spec`, including the relation carrier, find endpoint, and zero success
mass for an empty marked set. -/
theorem clause38_endpoint : clause38Spec := by
  refine ⟨dev_relation_carrier, ?_, ?_⟩
  · intro I _ _ W ψ S Mq k t
    exact dev_find_endpoint W ψ S Mq k t
  · intro I _ _ W ψ Mq k t
    exact (dev_find_endpoint W ψ ∅ Mq k t).2.2 rfl

/-- Establishes `clause39Spec`: endpoint tau embeddings vanish, and the plus-i program is no
longer than the detection program. -/
theorem clause39_endpoint : clause39Spec := by
  refine ⟨?_, ?_⟩
  · intro H I J _ _ _ _ _ _ A B hA hB
    exact bipartite_tau_endpoint_vanishes_dev A B hA hB
  · intro I _ j K
    simp [devPlusIProgram, devPlusIWalkWord, devPlusIReflectionWord,
      detectionProgram, detectionWalkWord, detectionReflectionWord]; omega

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
