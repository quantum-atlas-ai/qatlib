/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.PhysicalReadout
import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput

/-!
# Parity oracle representation change

These results relate executions with the source bit oracle to executions with
`workspacePhaseOracle`. The transformation `bitToPhaseCircuitSameInput` preserves the input
state and query count, adds two known gates per query, and preserves the unitary-circuit
condition. These results support the parity analysis of [FarhiEtAl1998].

## Main statements

* `source_answer_frame_run`: Running the transformed circuit with the workspace phase oracle
  gives the same state as running the original circuit with the source bit oracle.
* `source_answer_frame_cost`: The source-to-phase circuit transformation preserves the query
  count and adds exactly two known gates per query.

## References

* [Farhi et al., 1998][FarhiEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.CompressedQuery.CompressOracle
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- Running the transformed circuit with the workspace phase oracle gives the same state as
running the original circuit with the source bit oracle. See [Farhi et al.,
1998][FarhiEtAl1998]. -/
theorem source_answer_frame_run {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (f : Fin n → Bool) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuitSameInput C) ψ =
      Run (TensorGate (BitOracleOn f) 1) C ψ := by
  exact run_bitToPhaseCircuitSameInput f C ψ

/-- The source-to-phase circuit transformation preserves the query count and adds exactly two
known gates per query. See [Farhi et al., 1998][FarhiEtAl1998]. -/
theorem source_answer_frame_cost {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) :
    QueryCount (bitToPhaseCircuitSameInput C) = QueryCount C ∧
      GateCount (bitToPhaseCircuitSameInput C) = GateCount C + 2 * QueryCount C :=
  ⟨bitToPhaseCircuitSameInput_queryCount C, bitToPhaseCircuitSameInput_gateCount C⟩

/-- The transformed source-to-phase circuit is unitary if and only if the original circuit is
unitary. See [Farhi et al., 1998][FarhiEtAl1998]. -/
theorem source_answer_frame_unitary {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) :
    IsUnitaryCircuit (bitToPhaseCircuitSameInput C) ↔ IsUnitaryCircuit C :=
  bitToPhaseCircuitSameInput_isUnitaryCircuit C

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
