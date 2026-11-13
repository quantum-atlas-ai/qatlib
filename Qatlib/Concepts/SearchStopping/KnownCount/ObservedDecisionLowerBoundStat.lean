/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedOutputReadoutDefs

/-!
# Observed decision lower-bound contract

`ObservedDecisionLowerBound` specifies a query-depth bound for observed circuits acting on an
address, a bit, and a nonempty finite workspace. The hypotheses require a normalized initial
state and the 1/3 versus 2/3 acceptance gap.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `ObservedDecisionLowerBound`: The proposition that the stated empty-versus-singleton observed
  decision gap forces n ≤ 144 times the squared observed query depth.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open scoped Classical

/-- The proposition that the stated empty-versus-singleton observed decision gap forces n ≤ 144
times the squared observed query depth. -/
def ObservedDecisionLowerBound : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W)),
    observedWellFormed P → Normalized ψ →
    observedAcceptance (workspaceBitOracle (W := W) (fun _ => false)) P ψ ≤ 1/3 →
    (∀ w : Fin n, (2/3 : ℝ) ≤ observedAcceptance
      (workspaceBitOracle (W := W) (fun z => decide (z = w))) P ψ) →
    (n : ℝ) ≤ 144 * (observedQueryDepth P : ℝ)^2

end Qatlib.Concepts.SearchStopping.KnownCount
