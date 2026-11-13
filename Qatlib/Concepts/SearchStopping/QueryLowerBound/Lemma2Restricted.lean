/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized

/-!
# Restricted randomized Grover success statement

Defines `Lemma2Restricted`, the randomized-iteration success formula under the explicit
condition `0 < Real.sin (2 * θ)`. It also states the one-quarter success lower bound once the
iteration range reaches `1 / Real.sin (2 * θ)`. For the quantum-search analysis, see
[BoyerEtAl1998].

## Main statements

* `Lemma2Restricted`: The proposition giving the randomized Grover success formula for positive
  range `m` and positive `Real.sin (2 * θ)`, with success at least one quarter when `m ≥ 1 /
  Real.sin (2 * θ)`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u

/-- The proposition giving the randomized Grover success formula for positive range `m` and
positive `Real.sin (2 * θ)`, with success at least one quarter when `m ≥ 1 / Real.sin (2 *
θ)`. -/
def Lemma2Restricted : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (A : Finset I) (θ : ℝ),
      (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
      0 < Real.sin (2 * θ) → ∀ (m : ℕ), 0 < m →
        RandomizedSuccess A m =
          1 / 2 - Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) ∧
        (1 / Real.sin (2 * θ) ≤ (m : ℝ) → 1 / 4 ≤ RandomizedSuccess A m)

end Qatlib.Concepts.SearchStopping.QueryLowerBound
