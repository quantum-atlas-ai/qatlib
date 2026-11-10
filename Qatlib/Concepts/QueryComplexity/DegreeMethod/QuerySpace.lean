/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceCost
import Qatlib.Concepts.HspRecovery.CyclicRecovery.QuerySpaceValue
import Qatlib.Concepts.ShadowModels.ShadowChannel.QuerySpaceNoReference
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpace
open Qatlib Matrix
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem frontier1 (c : Bool) (C : Circuit (Data I W)) (hC : IsUnitaryCircuit C) :
    ∃ C' : Circuit (Full I W), IsUnitaryCircuit C' ∧
      QueryCount C' = QueryCount C ∧ GateCount C' = GateCount C + 5 * QueryCount C ∧
      ∀ (f : I → Bool) (r : I), f r = c → ∀ ψ : QState (Data I W),
        Run (bareOracle f) C' (referenceInput r ψ) =
          referenceInput r (Run (workspaceBitOracle f) C ψ) :=
  ⟨compileCircuit c C, compile_unitary c C hC, compile_queries c C, compile_gates c C,
    fun f r hfr ψ => run_compileCircuit c f r hfr C ψ⟩

def valueToPhaseCircuit (c : Bool) (C : Circuit ((I × ZMod 2) × W)) : Circuit (Full I W) :=
  compileCircuit c (relabelCircuit (Qatlib.Concepts.HspRecovery.CyclicRecovery.workspaceValueEquiv I W).symm C)

theorem run_valueToPhaseCircuit (c : Bool) (f : I → Bool) (r : I) (hfr : f r = c)
    (C : Circuit ((I × ZMod 2) × W)) (φ : QState ((I × ZMod 2) × W)) :
    Run (bareOracle f) (valueToPhaseCircuit c C)
      (referenceInput r (relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.workspaceValueEquiv I W).symm φ)) =
    referenceInput r (relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.workspaceValueEquiv I W).symm
      (Run (TensorGate (AddOracle (Qatlib.Concepts.HspRecovery.CyclicRecovery.boolValue f)) (1 : Matrix W W ℂ)) C φ)) := by
  rw [valueToPhaseCircuit, run_compileCircuit c f r hfr]
  rw [(Qatlib.Concepts.HspRecovery.CyclicRecovery.whole_circuit_backward f C φ ∅).1]

theorem valueToPhase_resources (c : Bool) (C : Circuit ((I × ZMod 2) × W))
    (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (valueToPhaseCircuit c C) ∧
      QueryCount (valueToPhaseCircuit c C) = QueryCount C ∧
      GateCount (valueToPhaseCircuit c C) = GateCount C + 5 * QueryCount C := by
  have hr := Qatlib.Concepts.HspRecovery.CyclicRecovery.backward_resources C
  refine ⟨compile_unitary c _ (hr.1.mpr hC), ?_, ?_⟩
  · rw [valueToPhaseCircuit, compile_queries, hr.2.1]
  · rw [valueToPhaseCircuit, compile_gates, hr.2.1, hr.2.2.1]

def phaseToValueCircuit (C : Circuit I) : Circuit (I × ZMod 2) :=
  relabelCircuit (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I) (LiftCircuitTo Bool C)

theorem run_phaseToValueCircuit (f : I → Bool) (C : Circuit I) (ψ : QState I) :
    Run (AddOracle (Qatlib.Concepts.HspRecovery.CyclicRecovery.boolValue f)) (phaseToValueCircuit C)
      (relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I) (TensorState ψ Minus)) =
    relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I) (TensorState (Run (PhaseOracle f) C ψ) Minus) := by
  have h := (run_relabelCircuit_readout (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I)
    (BitOracleOn f) (LiftCircuitTo Bool C) (TensorState ψ Minus) ∅).1
  rw [Qatlib.Concepts.HspRecovery.CyclicRecovery.bit_value_matrix, liftCircuitTo_bool,
      run_liftCircuit_bitOracleOn] at h
  simpa only [phaseToValueCircuit, liftCircuitTo_bool] using h

theorem phaseToValue_resources (C : Circuit I) (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (phaseToValueCircuit C) ∧
      QueryCount (phaseToValueCircuit C) = QueryCount C ∧
      GateCount (phaseToValueCircuit C) = GateCount C := by
  have hr := relabelCircuit_legality_resources (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I)
    (LiftCircuitTo Bool C)
  refine ⟨hr.1.mpr (isUnitaryCircuit_liftCircuitTo (J := Bool) hC), ?_, ?_⟩
  · rw [phaseToValueCircuit, hr.2.1, queryCount_liftCircuitTo]
  · rw [phaseToValueCircuit, hr.2.2.1, gateCount_liftCircuitTo]

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpace
