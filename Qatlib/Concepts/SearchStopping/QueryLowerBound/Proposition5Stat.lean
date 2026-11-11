/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm

/-!
# Statement of the finite sum-of-norms inequality

Defines `Proposition5`, the finite Cauchy-Schwarz estimate comparing the square of a sum of
complex norms with the sum of squared norms. The cardinality of the index type supplies the
multiplicative factor. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Proposition5`: The proposition that `(∑ i, ‖x i‖) ^ 2 ≤ r * ∑ i, ‖x i‖ ^ 2` for every complex
  vector indexed by `Fin r`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

/-- The proposition that `(∑ i, ‖x i‖) ^ 2 ≤ r * ∑ i, ‖x i‖ ^ 2` for every complex vector
indexed by `Fin r`. -/
def Proposition5 : Prop :=
  ∀ (r : ℕ) (x : Fin r → ℂ),
    (∑ i, ‖x i‖) ^ 2 ≤ (r : ℝ) * ∑ i, ‖x i‖ ^ 2

end Qatlib.Concepts.SearchStopping.QueryLowerBound
