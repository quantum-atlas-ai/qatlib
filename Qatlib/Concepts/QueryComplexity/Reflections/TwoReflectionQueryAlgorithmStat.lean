/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.BipartiteEffectiveGapCorrectedRefl
import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionConstructionRefl
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude

/-!
# Two-reflection query algorithm contract

Defines `TwoReflectionQueryAlgorithm`, asserting existence of a finite ancillary register, a
unitary bit-query circuit, and an output event for source dual-feasible data with `W ≥ 1`. The
circuit has error at most one third and explicit query and gate budgets linear in `Nat.ceil W`.

The proposition states the formal circuit endpoint for the reflection-query construction of
[Reichardt2011].

## Main statements

* `TwoReflectionQueryAlgorithm`: requires at most `1000000 * Nat.ceil W` queries and `10000000 *
  Nat.ceil W` gates.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators

/-- The assertion that source dual-feasible witnesses with budget `W ≥ 1` yield a
finite-workspace unitary bit-query circuit with success probability at least `2/3`, query
count at most `1000000 * Nat.ceil W`, and gate count at most `10000000 * Nat.ceil W`. -/
def TwoReflectionQueryAlgorithm : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ) (hn : 0 < n)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    SourceDualFeasible input f v W → 1 ≤ W →
    ∃ (r : ℕ) (hr : 0 < r) (C : Circuit ((Fin n × Bool) × Fin r))
      (E : Finset ((Fin n × Bool) × Fin r)),
      IsUnitaryCircuit C ∧
      QueryCount C ≤ 1000000 * Nat.ceil W ∧
      GateCount C ≤ 10000000 * Nat.ceil W ∧
      ∀ x : X, (2 / 3 : ℝ) ≤ MeasureProb
        (Run (workspaceBitOracle (W := Fin r) (input x)) C
          (Ket ((⟨0, hn⟩, false), ⟨0, hr⟩))) (if f x then E else Eᶜ)

end Qatlib.Concepts.QueryComplexity.Reflections
