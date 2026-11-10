/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedOutputReadoutDefs
set_option warningAsError false
set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open scoped Classical

def ObservedSearchLowerBound : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (decode : ℕ → ((Fin n × Bool) × W) → Option (Fin n)),
    observedWellFormed P → Normalized ψ →
    (∀ w : Fin n, (2/3 : ℝ) ≤ observedDecodedMass
      (workspaceBitOracle (W := W) (fun z => decide (z = w))) P ψ decode (some w)) →
    ((n : ℝ) ≤ max 1 (64 * (observedQueryDepth P : ℝ)^2)) ∧
    (2 ≤ n → (n : ℝ) ≤ 64 * (observedQueryDepth P : ℝ)^2)

end Qatlib.Concepts.SearchStopping.KnownCount
