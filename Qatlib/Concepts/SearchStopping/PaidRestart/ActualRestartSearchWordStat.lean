/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.RestartSearchDefs

/-!
# Statement of the bit-oracle Grover circuit law

Defines `ActualRestartSearchWord`, the circuit specification for implementing a prepared Grover
search with a Boolean oracle. It records unitarity, `j` queries, `j + 2` gates, and the final
tensor product of the Grover state with `Minus`. For the quantum-search analysis, see
[BoyerEtAl1998].

## Main statements

* `ActualRestartSearchWord`: The proposition that a unitary preparation of the uniform state
  yields a unitary bit-search circuit with `j` queries and `j + 2` gates, mapping the prepared
  input and `Ket true` to the Grover state tensored with `Minus`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

/-- The proposition that a unitary preparation of the uniform state yields a unitary bit-search
circuit with `j` queries and `j + 2` gates, mapping the prepared input and `Ket true` to the
Grover state tensored with `Minus`. -/
def ActualRestartSearchWord : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix I I ℂ) (v : QState I), T' ∈ Matrix.unitaryGroup I ℂ →
    Normalized v → T' *ᵥ v = Uniform I → ∀ (A : Finset I) (j : ℕ),
    IsUnitaryCircuit (bbhtBitSearchCircuit T' v j) ∧
    QueryCount (bbhtBitSearchCircuit T' v j) = j ∧
    GateCount (bbhtBitSearchCircuit T' v j) = j + 2 ∧
    Run (BitOracleOn (fun i => decide (i ∈ A))) (bbhtBitSearchCircuit T' v j)
      (TensorState v (Ket true)) = TensorState (GroverState A j) Minus

end Qatlib.Concepts.SearchStopping.PaidRestart
