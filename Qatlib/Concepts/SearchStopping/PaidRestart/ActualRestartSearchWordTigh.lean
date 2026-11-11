/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartSearchWordStat

/-!
# Execution of the bit-oracle Grover circuit

Proves `actualRestartSearchWord`, connecting the lifted source-gate circuit to its
Boolean-oracle execution. The result supplies the precise state evolution and resource counts
used by the paid restart laws. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `actualRestartSearchWord`: Establishes `ActualRestartSearchWord`, giving the exact bit-oracle
  Grover output state, circuit unitarity, and query and gate counts.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.SearchStopping.GateCore

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open scoped Classical BigOperators

/-- Establishes `ActualRestartSearchWord`, giving the exact bit-oracle Grover output state,
circuit unitarity, and query and gate counts. See [BoyerEtAl1998]. -/
theorem actualRestartSearchWord : ActualRestartSearchWord := by
  intro I _ _ hN T' v hT hv hprep A j
  have hs := section6SourceGateSubgoal I hN T' v hT hv hprep A j
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold bbhtBitSearchCircuit
    apply (isUnitaryCircuit_gate _ _).mpr
    refine ⟨tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary, ?_⟩
    exact ((isUnitaryCircuit_gate T' _).mpr ⟨hT, hs.1⟩).lift
  · simp only [bbhtBitSearchCircuit, queryCount_gate, queryCount_liftCircuit,
      bbhtPreparedSourceCircuit, hs.2.1]
  · simp [bbhtBitSearchCircuit, gateCount_liftCircuit, bbhtPreparedSourceCircuit,
      SourceGateCircuit, gateCount_repeatCircuit, SourceGateBlock, Nat.add_assoc]
  · simp only [bbhtBitSearchCircuit, run_gate]
    rw [applyGate_tensorGate, applyGate_one, applyGate_hadamard_ket_true,
      run_liftCircuit_bitOracleOn]
    simp only [bbhtPreparedSourceCircuit, run_gate]
    change TensorState (Run (SetOracle A) (SourceGateCircuit T' v j) (T' *ᵥ v)) Minus = _
    rw [hprep]
    exact congrArg (fun ψ => TensorState ψ Minus) hs.2.2.1

end Qatlib.Concepts.SearchStopping.PaidRestart
