/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Standard-oracle sequential-copy specification

`StandardOracleSequentialCopies` states the existence of a unitary circuit running a fixed
oracle circuit on each factor of an arbitrary tensor input. It records preservation of a clean
shared oracle register and the exact costs of routing queries. The background is described in
[BennettEtAl1997].

## Main statements

* `StandardOracleSequentialCopies`: independent execution on every tensor factor with exact
  costs.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.Amplification

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical BigOperators

/-- The assertion that a unitary standard bit-oracle circuit can be run independently on `k`
tensor factors while preserving a shared clean oracle register, with exactly `k` times its
queries and two routing gates per copied query. -/
def StandardOracleSequentialCopies : Prop :=
  ∀ (n k : ℕ) (hn : 0 < n) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (C : Circuit ((Fin n × Bool) × W)), IsUnitaryCircuit C →
    ∃ D : Circuit ((Fin n × Bool) × (Fin k → (Fin n × Bool) × W)),
      IsUnitaryCircuit D ∧ QueryCount D = k * QueryCount C ∧
      GateCount D = k * GateCount C + 2 * k * QueryCount C ∧
      ∀ (x : Fin n → Bool) (ψ : Fin k → QState ((Fin n × Bool) × W)),
      Run (workspaceBitOracle (W := Fin k → (Fin n × Bool) × W) x) D
        (TensorState (Ket (⟨0, hn⟩, false)) (PiTensorState ψ)) =
      TensorState (Ket (⟨0, hn⟩, false))
        (PiTensorState fun j => Run (workspaceBitOracle (W := W) x) C (ψ j))

end Qatlib.Concepts.UniformBqp.OracleAmplify
