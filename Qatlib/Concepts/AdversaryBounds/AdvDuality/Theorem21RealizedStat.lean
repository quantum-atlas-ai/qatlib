/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat

/-!
# Statement of the realized Kushilevitz query bound

`Theorem21Realized` states a query-count lower bound for unitary circuits that classify the
twenty Kushilevitz witness inputs from a normalized initial state. The bound includes the
bounded-error factor `1 - 2 * sqrt (eps * (1 - eps))` for `0 ≤ eps ≤ 1 / 2`.

The proposition expresses the circuit consequence of the negative adversary witness associated
with Theorem 21 of [HoyerLeeSpalek2007].

## Main statements

* `Theorem21Realized`: states the workspace-uniform bounded-error circuit query lower bound.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped BigOperators Matrix.Norms.L2Operator

/-- The proposition that every unitary circuit correctly classifying the twenty witness inputs
with error at most `eps ∈ [0, 1 / 2]` has query count at least `(2 + 3 * sqrt 5 / 5) * (1 -
2 * sqrt (eps * (1 - eps))) / 2`, for every finite workspace and normalized initial state.
See [Hoyer, Lee, and Spalek, Theorem 21][HoyerLeeSpalek2007]. -/
def Theorem21Realized : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (C : Circuit ((Fin 6 × Bool) × W))
    (psi : QState ((Fin 6 × Bool) × W)) (E : Finset ((Fin 6 × Bool) × W)) (eps : ℝ),
    IsUnitaryCircuit C → Normalized psi → 0 ≤ eps → eps ≤ 1 / 2 →
    (∀ x : Fin 20, 1 - eps ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (kushilevitzInputW x)) C psi)
        (if kushilevitzFunW x = true then E else Eᶜ)) →
    (2 + 3 * Real.sqrt 5 / 5) * (1 - 2 * Real.sqrt (eps * (1 - eps))) / 2 ≤ QueryCount C

end Qatlib.Concepts.AdversaryBounds.AdvDuality
