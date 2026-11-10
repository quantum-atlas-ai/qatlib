/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Matrix
open scoped Classical BigOperators

def AdaptiveClassicalSimulation : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (f : (Fin n → Bool) → Bool), observedWellFormed P → Normalized ψ →
    (∀ x : Fin n → Bool,
      |observedAcceptance (workspaceBitOracle (W := W) x) P ψ -
        (if f x then (1 : ℝ) else 0)| ≤ 1/3) →
    (∃ t : BoolQueryTree (Fin n) Bool,
      (∀ x, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1 = f x) ∧
      t.MaxQueries ≤ 4096 * observedQueryDepth P ^ 6) ∧
    deterministicQueryComplexity f ≤ 4096 * observedQueryDepth P ^ 6

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
