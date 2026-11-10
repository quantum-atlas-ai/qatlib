/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.BipartiteEffectiveGapCorrectedRefl
import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionConstructionRefl
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix
open scoped Classical BigOperators

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
