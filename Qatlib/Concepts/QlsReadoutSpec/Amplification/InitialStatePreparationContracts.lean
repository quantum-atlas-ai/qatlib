/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverLowerBoundInstance

/-!
# Initial-state preparation lower bound contract

Defines `InitialStatePrepLowerBoundSubgoal`, a proposed query lower bound for circuits
approximating the indexed solution targets using `bOracle`. For at least 150 indices and error
at most `1 / 100`, the contract requires the index cardinality to be at most 64 times the
squared query count. Initial-state preparation query complexity is studied in [LowSu2026].

## Main statements

* `InitialStatePrepLowerBoundSubgoal`: states the quantified approximation-to-query-count
  implication.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix

/-- The proposition that a unitary circuit approximating every indexed solution target with
error at most `1 / 100`, for at least 150 indices and normalized seeds, satisfies
`Fintype.card I ≤ 64 * (QueryCount C) ^ 2` when run with `bOracle`. -/
def InitialStatePrepLowerBoundSubgoal : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (ν₀ : QState Bool) (ω₀ : QState W) (ε : ℝ) (C : Circuit ((I × Bool) × W)),
    150 ≤ Fintype.card I → ε ≤ 1 / 100 →
    IsUnitaryCircuit C → Normalized ν₀ → Normalized ω₀ →
    (∀ x : I,
      ‖stateVector (Run (bOracle (I := I) (W := W) x) C (solverStart ν₀ ω₀)) -
          stateVector (solutionTarget ν₀ ω₀ x)‖ ≤ ε) →
    (Fintype.card I : ℝ) ≤ 64 * ((QueryCount C : ℕ) : ℝ) ^ 2

end Qatlib.Concepts.QlsReadoutSpec.Amplification
