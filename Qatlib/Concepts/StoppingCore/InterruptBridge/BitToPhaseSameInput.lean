/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.StoppingCore.InterruptBridge
open Matrix
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

def bitToPhaseCircuitSameInput (C : Circuit ((I × Bool) × W)) :
    Circuit ((I × Bool) × W) := C.flatMap bitToPhaseStep

theorem bitToPhaseCircuit_eq_header_sameInput (C : Circuit ((I × Bool) × W)) :
    bitToPhaseCircuit C = Step.gate controlHadamard :: bitToPhaseCircuitSameInput C := rfl

theorem run_bitToPhaseCircuit_input_transport (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuit C) ψ =
      Run (workspaceBitOracle f) C (ApplyGate controlHadamard ψ) := by
  have h := run_bitToPhaseCircuit f C (ApplyGate controlHadamard ψ)
  rw [← applyGate_mul, controlHadamard_mul_self, applyGate_one] at h
  exact h

theorem run_bitToPhaseCircuitSameInput (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuitSameInput C) ψ =
      Run (workspaceBitOracle f) C ψ := by
  have h := run_bitToPhaseCircuit f C ψ
  simpa only [bitToPhaseCircuit, bitToPhaseCircuitSameInput, run_gate,
    ← applyGate_mul, controlHadamard_mul_self, applyGate_one] using h

theorem measureProb_bitToPhaseCircuitSameInput (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (S : Finset ((I × Bool) × W)) :
    MeasureProb (Run (workspacePhaseOracle f) (bitToPhaseCircuitSameInput C) ψ) S =
      MeasureProb (Run (workspaceBitOracle f) C ψ) S := by
  rw [run_bitToPhaseCircuitSameInput]

theorem bitToPhaseCircuitSameInput_queryCount (C : Circuit ((I × Bool) × W)) :
    QueryCount (bitToPhaseCircuitSameInput C) = QueryCount C := by
  simpa only [bitToPhaseCircuit, bitToPhaseCircuitSameInput, queryCount_gate]
    using bitToPhaseCircuit_queryCount C

theorem bitToPhaseCircuitSameInput_gateCount (C : Circuit ((I × Bool) × W)) :
    GateCount (bitToPhaseCircuitSameInput C) = GateCount C + 2 * QueryCount C := by
  change GateCount (C.flatMap bitToPhaseStep) = _
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;>
      simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
        gateCount_gate, gateCount_query, queryCount_gate, queryCount_query, ih] <;> omega

theorem bitToPhaseCircuit_gateCount_with_header (C : Circuit ((I × Bool) × W)) :
    GateCount (bitToPhaseCircuit C) = GateCount C + 2 * QueryCount C + 1 := by
  rw [bitToPhaseCircuit_eq_header_sameInput, gateCount_gate,
    bitToPhaseCircuitSameInput_gateCount]

private theorem sameInput_controlHadamard_unitary :
    controlHadamard (I := I) (W := W) ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := by
  unfold controlHadamard
  exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

theorem bitToPhaseCircuitSameInput_isUnitaryCircuit (C : Circuit ((I × Bool) × W)) :
    IsUnitaryCircuit (bitToPhaseCircuitSameInput C) ↔ IsUnitaryCircuit C := by
  change IsUnitaryCircuit (C.flatMap bitToPhaseStep) ↔ _
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;>
      simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
        isUnitaryCircuit_gate, isUnitaryCircuit_query, sameInput_controlHadamard_unitary,
        true_and, ih]

end Qatlib.Concepts.StoppingCore.InterruptBridge
