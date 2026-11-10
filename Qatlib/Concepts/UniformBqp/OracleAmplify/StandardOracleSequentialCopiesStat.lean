/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.Amplification

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Matrix
open scoped Classical BigOperators

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
