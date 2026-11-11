/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchBounds
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Papers.GroverSearch96.MainResults.LocalImplementation

/-!
# Local initialization and the workspace bit oracle program

`source_local_initialization` verifies uniform state preparation by a local Hadamard program
with exactly one gate per qubit and no oracle queries.

`source_bit_oracle_program` verifies the workspace Grover program, including unitarity, query
and gate counts, and its tensor product output with a minus state and unchanged workspace basis
state. See [Grover1997].

## Main statements

* `source_local_initialization`: The local Hadamard program realizes `HadamardN n`, prepares the
  uniform state from the zero basis state, and has length and gate count `n` with zero queries.
* `source_bit_oracle_program`: The workspace Grover circuit is unitary, uses `k` queries and
  `3*k+3` counted gates, and maps its initialized basis state to the tensor product of
  `GroverState {target} k`, `Minus`, and the workspace basis state.

## References

* [Grover, 1997][Grover1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

namespace Qatlib.Papers.GroverSearch97.MainResults

/-- The local Hadamard program realizes `HadamardN n`, prepares the uniform state from the zero
basis state, and has length and gate count `n` with zero queries. See [Grover1997]. -/
theorem source_local_initialization (n : ℕ) :
    localProgramMatrix (localHadamard n) = HadamardN n ∧
      (localHadamard n).length = n ∧
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (localProgramCircuit (localHadamard n))
        (Ket (ZeroStr n)) = Uniform (Reg n) ∧
      GateCount (localProgramCircuit (localHadamard n)) = n ∧
      QueryCount (localProgramCircuit (localHadamard n)) = 0 :=
  localHadamard_actual_implementation n

/-- The workspace Grover circuit is unitary, uses `k` queries and `3*k+3` counted gates, and
maps its initialized basis state to the tensor product of `GroverState {target} k`, `Minus`,
and the workspace basis state. See [Grover1997]. -/
theorem source_bit_oracle_program {W : Type} [Fintype W] [DecidableEq W]
    (n k : ℕ) (workspace : W) (target : Reg n) :
    IsUnitaryCircuit (workspaceGroverCircuit (W := W) n k) ∧
      QueryCount (workspaceGroverCircuit (W := W) n k) = k ∧
      GateCount (workspaceGroverCircuit (W := W) n k) = 3 * k + 3 ∧
      Run (workspaceBitOracle (W := W) (fun x => decide (x = target)))
        (workspaceGroverCircuit (W := W) n k) (Ket ((ZeroStr n, false), workspace)) =
        TensorState (TensorState (GroverState {target} k) Minus) (Ket workspace) := by
  have h := workspace_grover_bit_semantics_and_cost n k workspace (fun x => decide (x = target))
  have ho : PhaseOracle (fun x : Reg n => decide (x = target)) = preparedMark {target} := by
    rw [Qatlib.Papers.GroverSearch96.MainResults.prepared_mark_eq_source_oracle]
    simp only [SetOracle, Finset.mem_singleton]
  rw [ho, Qatlib.Papers.GroverSearch96.MainResults.prepared_aa_eq_source_grover] at h
  exact h

end Qatlib.Papers.GroverSearch97.MainResults
