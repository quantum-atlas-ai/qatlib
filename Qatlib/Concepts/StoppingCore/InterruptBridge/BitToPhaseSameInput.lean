/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle

/-!
# Bit-to-phase compilation on the same input

`bitToPhaseCircuitSameInput` replaces bit-oracle circuit steps by their phase-oracle simulation
without an initial Hadamard header. It preserves the output state on the same input, hence every
measurement event, and records the exact query and gate counts.

The construction uses the standard phase-kickback relation between bit and phase queries
described in [NielsenChuang2010].

## Main statements

* `run_bitToPhaseCircuitSameInput`: equality of the compiled and original output states
* `bitToPhaseCircuitSameInput_gateCount`: two added gates per query
* `bitToPhaseCircuitSameInput_isUnitaryCircuit`: equivalence of circuit unitarity

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.StoppingCore.InterruptBridge
open Matrix
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The circuit obtained by replacing each step with `bitToPhaseStep`, without an initial
Hadamard header. -/
def bitToPhaseCircuitSameInput (C : Circuit ((I × Bool) × W)) :
    Circuit ((I × Bool) × W) := C.flatMap bitToPhaseStep

/-- The original bit-to-phase compiler is a control Hadamard followed by the compiler using the
same input state. -/
theorem bitToPhaseCircuit_eq_header_sameInput (C : Circuit ((I × Bool) × W)) :
    bitToPhaseCircuit C = Step.gate controlHadamard :: bitToPhaseCircuitSameInput C := rfl

/-- The compiled phase-oracle run equals the original bit-oracle run on the input transformed by
a control Hadamard. -/
theorem run_bitToPhaseCircuit_input_transport (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuit C) ψ =
      Run (workspaceBitOracle f) C (ApplyGate controlHadamard ψ) := by
  have h := run_bitToPhaseCircuit f C (ApplyGate controlHadamard ψ)
  rw [← applyGate_mul, controlHadamard_mul_self, applyGate_one] at h
  exact h

/-- The compiler without the Hadamard header reproduces the bit-oracle run on the same input
state using the workspace phase oracle. -/
theorem run_bitToPhaseCircuitSameInput (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuitSameInput C) ψ =
      Run (workspaceBitOracle f) C ψ := by
  have h := run_bitToPhaseCircuit f C ψ
  simpa only [bitToPhaseCircuit, bitToPhaseCircuitSameInput, run_gate,
    ← applyGate_mul, controlHadamard_mul_self, applyGate_one] using h

/-- Compilation using the same input preserves every measurement event probability. -/
theorem measureProb_bitToPhaseCircuitSameInput (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (S : Finset ((I × Bool) × W)) :
    MeasureProb (Run (workspacePhaseOracle f) (bitToPhaseCircuitSameInput C) ψ) S =
      MeasureProb (Run (workspaceBitOracle f) C ψ) S := by
  rw [run_bitToPhaseCircuitSameInput]

/-- Compilation using the same input preserves the number of oracle queries. -/
theorem bitToPhaseCircuitSameInput_queryCount (C : Circuit ((I × Bool) × W)) :
    QueryCount (bitToPhaseCircuitSameInput C) = QueryCount C := by
  simpa only [bitToPhaseCircuit, bitToPhaseCircuitSameInput, queryCount_gate]
    using bitToPhaseCircuit_queryCount C

/-- Compilation using the same input adds exactly two gates per oracle query. -/
theorem bitToPhaseCircuitSameInput_gateCount (C : Circuit ((I × Bool) × W)) :
    GateCount (bitToPhaseCircuitSameInput C) = GateCount C + 2 * QueryCount C := by
  change GateCount (C.flatMap bitToPhaseStep) = _
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s <;>
      simp only [List.flatMap_cons, bitToPhaseStep, List.cons_append, List.nil_append,
        gateCount_gate, gateCount_query, queryCount_gate, queryCount_query, ih] <;> omega

/-- Compilation with the initial Hadamard adds two gates per query and one header gate. -/
theorem bitToPhaseCircuit_gateCount_with_header (C : Circuit ((I × Bool) × W)) :
    GateCount (bitToPhaseCircuit C) = GateCount C + 2 * QueryCount C + 1 := by
  rw [bitToPhaseCircuit_eq_header_sameInput, gateCount_gate,
    bitToPhaseCircuitSameInput_gateCount]

/-- The control Hadamard on the address, Boolean, and workspace registers is unitary. -/
private theorem sameInput_controlHadamard_unitary :
    controlHadamard (I := I) (W := W) ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ := by
  unfold controlHadamard
  exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

/-- The circuit compiled using the same input is unitary exactly when the original circuit is
unitary. -/
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
