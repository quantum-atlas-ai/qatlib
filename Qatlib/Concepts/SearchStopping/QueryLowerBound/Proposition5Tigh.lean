/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Proposition5Stat

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

theorem proposition5_finset {ι : Type*} (s : Finset ι) (x : ι → ℂ) :
    (∑ i ∈ s, ‖x i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖x i‖ ^ 2 := by
  exact sq_sum_le_card_mul_sum_sq

theorem proposition5 : Proposition5 := by
  intro r x
  simpa using proposition5_finset Finset.univ x

theorem proposition5_range (r : ℕ) (x : ℕ → ℂ) :
    (∑ i ∈ Finset.range r, ‖x i‖) ^ 2 ≤
      (r : ℝ) * ∑ i ∈ Finset.range r, ‖x i‖ ^ 2 := by
  simpa using proposition5_finset (Finset.range r) x

end Qatlib.Concepts.SearchStopping.QueryLowerBound
