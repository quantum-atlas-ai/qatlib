/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

@[expose] public section

/-!
# Squared distance to the sample mean

Expands the classical target of the supervised cluster assignment in
Lloyd, Mohseni, and Rebentrost, arXiv:1307.0411v2, page 3.
-/

set_option autoImplicit false

open Qatlib.Papers.SupervisedML13.MainResults

namespace Qatlib.Papers.SupervisedML13.MainResults

/-- The squared distance to the sample mean is the sum of the squared norms minus twice
the inner-product term. -/
theorem distance_to_mean_sq_expansion {M N : ℕ}
    (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ) :
    distanceToMeanSq u v =
      normSq u - 2 * (∑ i, u i * meanVector v i) + normSq (meanVector v) := by
  simp only [distanceToMeanSq, normSq, sub_sq, mul_assoc, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

end Qatlib.Papers.SupervisedML13.MainResults
