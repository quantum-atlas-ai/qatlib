/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.LowerBound.PhysicalReadout
import Qatlib.Concepts.StoppingCore.InterruptBridge.BitToPhaseSameInput
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

theorem source_answer_frame_run {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W))
    (ψ : QState (PolynomialWorkspace (Fin n) W)) (f : Fin n → Bool) :
    Run (workspacePhaseOracle f) (bitToPhaseCircuitSameInput C) ψ =
      Run (TensorGate (BitOracleOn f) 1) C ψ := by
  exact run_bitToPhaseCircuitSameInput f C ψ

theorem source_answer_frame_cost {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) :
    QueryCount (bitToPhaseCircuitSameInput C) = QueryCount C ∧
      GateCount (bitToPhaseCircuitSameInput C) = GateCount C + 2 * QueryCount C :=
  ⟨bitToPhaseCircuitSameInput_queryCount C, bitToPhaseCircuitSameInput_gateCount C⟩

theorem source_answer_frame_unitary {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace (Fin n) W)) :
    IsUnitaryCircuit (bitToPhaseCircuitSameInput C) ↔ IsUnitaryCircuit C :=
  bitToPhaseCircuitSameInput_isUnitaryCircuit C

end Qatlib.Papers.ParityLimit98.MainResults.LowerBound
