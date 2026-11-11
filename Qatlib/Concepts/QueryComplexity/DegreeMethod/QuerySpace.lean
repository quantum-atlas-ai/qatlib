/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceCost
import Qatlib.Concepts.HspRecovery.CyclicRecovery.QuerySpaceValue
import Qatlib.Concepts.ShadowModels.ShadowChannel.QuerySpaceNoReference

/-!
# Phase and value oracle circuit conversions

This module combines a known-reference phase-oracle compiler with register relabeling to
convert Boolean value-oracle circuits to phase access, and converts phase circuits to
value access using a minus-state response register. These constructions use the
phase-kickback viewpoint of [NielsenChuang2010].

The conversion from value to phase access preserves query count and adds five gates per
query; the reverse conversion preserves both query and gate counts.

## Main statements

* `frontier1`: simulate a unitary bit-oracle circuit using a reference of known value.
* `run_valueToPhaseCircuit`: correctness of value-to-phase compilation.
* `phaseToValue_resources`: resource preservation for phase-to-value compilation.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- Every unitary workspace bit-oracle circuit has a unitary bare-phase simulation using a
reference index of known value, preserving queries and adding five gates per query. -/
theorem frontier1 (c : Bool) (C : Circuit (Data I W)) (hC : IsUnitaryCircuit C) :
    ∃ C' : Circuit (Full I W), IsUnitaryCircuit C' ∧
      QueryCount C' = QueryCount C ∧ GateCount C' = GateCount C + 5 * QueryCount C ∧
      ∀ (f : I → Bool) (r : I), f r = c → ∀ ψ : QState (Data I W),
        Run (bareOracle f) C' (referenceInput r ψ) =
          referenceInput r (Run (workspaceBitOracle f) C ψ) :=
  ⟨compileCircuit c C, compile_unitary c C hC, compile_queries c C, compile_gates c C,
    fun f r hfr ψ => run_compileCircuit c f r hfr C ψ⟩

/-- Relabel a Boolean value-oracle circuit and compile it to bare-phase access with known
reference value `c`. -/
def valueToPhaseCircuit (c : Bool) (C : Circuit ((I × ZMod 2) × W)) : Circuit (Full I W) :=
  compileCircuit c (relabelCircuit (Qatlib.Concepts.HspRecovery.CyclicRecovery.workspaceValueEquiv I W).symm C)

/-- With a reference index of value `c`, the compiled phase circuit reproduces the value-oracle
run after register relabeling. -/
theorem run_valueToPhaseCircuit (c : Bool) (f : I → Bool) (r : I) (hfr : f r = c)
    (C : Circuit ((I × ZMod 2) × W)) (φ : QState ((I × ZMod 2) × W)) :
    Run (bareOracle f) (valueToPhaseCircuit c C)
      (referenceInput r (relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.workspaceValueEquiv I W).symm φ)) =
    referenceInput r (relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.workspaceValueEquiv I W).symm
      (Run (TensorGate (AddOracle (Qatlib.Concepts.HspRecovery.CyclicRecovery.boolValue f)) (1 : Matrix W W ℂ)) C φ)) := by
  rw [valueToPhaseCircuit, run_compileCircuit c f r hfr]
  rw [(Qatlib.Concepts.HspRecovery.CyclicRecovery.whole_circuit_backward f C φ ∅).1]

/-- Value-to-phase compilation preserves unitarity and query count, and adds five gates for
every source query. -/
theorem valueToPhase_resources (c : Bool) (C : Circuit ((I × ZMod 2) × W))
    (hC : IsUnitaryCircuit C) :
    IsUnitaryCircuit (valueToPhaseCircuit c C) ∧
      QueryCount (valueToPhaseCircuit c C) = QueryCount C ∧
      GateCount (valueToPhaseCircuit c C) = GateCount C + 5 * QueryCount C := by
  have hr := Qatlib.Concepts.HspRecovery.CyclicRecovery.backward_resources C
  refine ⟨compile_unitary c _ (hr.1.mpr hC), ?_, ?_⟩
  · rw [valueToPhaseCircuit, compile_queries, hr.2.1]
  · rw [valueToPhaseCircuit, compile_gates, hr.2.1, hr.2.2.1]

/-- Lift a phase-oracle circuit with a Boolean response register and relabel it as a `ZMod 2`
value-oracle circuit. -/
def phaseToValueCircuit (C : Circuit I) : Circuit (I × ZMod 2) :=
  relabelCircuit (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I) (LiftCircuitTo Bool C)

/-- The value-oracle conversion reproduces the phase-oracle run when the response register
starts in the minus state. -/
theorem run_phaseToValueCircuit (f : I → Bool) (C : Circuit I) (ψ : QState I) :
    Run (AddOracle (Qatlib.Concepts.HspRecovery.CyclicRecovery.boolValue f)) (phaseToValueCircuit C)
      (relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I) (TensorState ψ Minus)) =
    relabelState (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I) (TensorState (Run (PhaseOracle f) C ψ) Minus) := by
  have h := (run_relabelCircuit_readout (Qatlib.Concepts.HspRecovery.CyclicRecovery.bitValueEquiv I)
    (BitOracleOn f) (LiftCircuitTo Bool C) (TensorState ψ Minus) ∅).1
  rw [Qatlib.Concepts.HspRecovery.CyclicRecovery.bit_value_matrix, liftCircuitTo_bool,
      run_liftCircuit_bitOracleOn] at h
  simpa only [phaseToValueCircuit, liftCircuitTo_bool] using h

/-- Phase-to-value compilation preserves unitarity, query count, and gate count. -/
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
