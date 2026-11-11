/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification

/-!
# The adaptive block sensitivity query bound

This module defines `AdaptiveBlockSensitivityQueryBound`, the proposition bounding the block
sensitivity of a Boolean function computed by a well formed observed circuit from a normalized
state. For query depth `T`, the bounds are `16T²` at error at most one third and `8T²` for exact
acceptance probabilities.

The proposition packages the adaptive circuit form of polynomial method bounds from
[BealsEtAl2001].

## Main statements

* `AdaptiveBlockSensitivityQueryBound`: the bounded error and exact block sensitivity bounds for
  observed circuits.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Matrix
open scoped Classical BigOperators

/-- The proposition that well formed observed circuits on normalized inputs have block
sensitivity at most `16T²` for error at most one third and `8T²` for exact computation,
where `T` is their query depth. -/
def AdaptiveBlockSensitivityQueryBound : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
    (P : ObservedCircuit ((Fin n × Bool) × W)) (ψ : QState ((Fin n × Bool) × W))
    (f : (Fin n → Bool) → Bool), observedWellFormed P → Normalized ψ →
    ((∀ x : Fin n → Bool,
      |observedAcceptance (workspaceBitOracle (W := W) x) P ψ -
        (if f x then (1 : ℝ) else 0)| ≤ 1/3) →
      blockSensitivity f ≤ 16 * observedQueryDepth P ^ 2) ∧
    ((∀ x : Fin n → Bool,
      observedAcceptance (workspaceBitOracle (W := W) x) P ψ =
        (if f x then (1 : ℝ) else 0)) →
      blockSensitivity f ≤ 8 * observedQueryDepth P ^ 2)

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
