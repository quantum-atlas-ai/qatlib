/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Proposition5Stat

/-!
# Finite Cauchy-Schwarz bounds for complex norms

Proves `proposition5` and variants for arbitrary finite sets and natural-number ranges. These
inequalities convert sums of query amplitudes into sums of squared projection norms. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `proposition5_finset`: For a finite set `s`, the square of the sum of `‖x i‖` is at most
  `s.card` times the sum of `‖x i‖ ^ 2` over `s`.
* `proposition5`: Establishes `Proposition5`, the Cauchy-Schwarz bound for the sum of norms of a
  complex vector on `Fin r`.
* `proposition5_range`: The square of the sum of complex norms over `Finset.range r` is at most
  `r` times the sum of their squares.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

/-- For a finite set `s`, the square of the sum of `‖x i‖` is at most `s.card` times the sum of
`‖x i‖ ^ 2` over `s`. -/
theorem proposition5_finset {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    (∑ i ∈ s, ‖x i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  exact sq_sum_le_card_mul_sum_sq

/-- Establishes `Proposition5`, the Cauchy-Schwarz bound for the sum of norms of a complex
vector on `Fin r`. See [BoyerEtAl1998]. -/
theorem proposition5 : Proposition5 := by
  intro r x
  simpa using proposition5_finset Finset.univ x

/-- The square of the sum of complex norms over `Finset.range r` is at most `r` times the sum of
their squares. -/
theorem proposition5_range (r : ℕ) (x : ℕ → ℂ) :
    (∑ i ∈ Finset.range r, ‖x i‖) ^ 2 ≤
      (r : ℝ) * ∑ i ∈ Finset.range r, ‖x i‖ ^ 2 := by
  simpa using proposition5_finset (Finset.range r) x

end Qatlib.Concepts.SearchStopping.QueryLowerBound
