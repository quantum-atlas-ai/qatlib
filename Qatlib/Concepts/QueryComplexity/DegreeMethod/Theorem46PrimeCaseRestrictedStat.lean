/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib

def Theorem46PrimeCaseRestricted : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (f : (Fin n → Bool) → Bool),
    0 < n →
    observedWellFormed P →
    Normalized ψ →
    (∀ x y : Fin n → Bool,
        (Finset.univ.filter (fun i => x i = true)).card =
          (Finset.univ.filter (fun i => y i = true)).card → f x = f y) →
    (∃ x y : Fin n → Bool, f x ≠ f y) →
    Nat.Prime (n + 1) →
    (∀ g : Fin n → Bool,
        observedAcceptance (workspaceBitOracle (W := W) g) P ψ =
          if f g = true then (1 : ℝ) else 0) →
    n ≤ 2 * observedQueryDepth P

end Qatlib.Concepts.QueryComplexity.DegreeMethod
