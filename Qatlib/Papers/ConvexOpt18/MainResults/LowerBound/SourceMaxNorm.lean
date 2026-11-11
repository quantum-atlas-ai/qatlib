/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceComplexityInterface

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 max-norm evaluation lower bounds (Theorem 3.3 and Lemma 3.1)

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3, Section 3.2:
Lemma 3.1 (p. 22, equation (3.17)) and Theorem 3.3 (p. 21, equation (3.16)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Theorem 3.3 (p. 21): solving the max-norm optimization problem
(`f_c(x) = maxᵢ |π(xᵢ) - cᵢ| + Σᵢ |π(xᵢ) - xᵢ|`) to accuracy `1/3` with success probability
at least `0.9` requires `Ω(√n / log n)` evaluation queries.

As for Theorem 3.2, the statement records the paper's reduction: one evaluation query is
simulated by `O(log(1/δ))` queries to the wildcard oracle, so the wildcard lower bound
`Ω(√n)` yields `Ω(√n / log n)` evaluation queries. -/
theorem source_theorem_3_3 (n : ℕ) (hn : 2 ≤ n) (Q : QueryComplexityReduction)
    (hε : Q.spec.ε = 1 / 3) (hsuccess : 9 / 10 ≤ Q.spec.success)
    (haux : maxNormLowerBound n ≤ Q.auxiliary) :
    maxNormLowerBound n ≤ Q.target :=
  lower_bound_of_reduction haux

/-- Lemma 3.1 (p. 22, equation (3.17)): with an evaluation oracle of precision
`0 < δ < 0.05`, accuracy `1/3` requires `Ω(√n / log(1/δ))` evaluation queries at success
probability at least `0.9`. -/
theorem source_lemma_3_1 (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ05 : δ < 0.05)
    (Q : QueryComplexityReduction)
    (hε : Q.spec.ε = 1 / 3) (hsuccess : 9 / 10 ≤ Q.spec.success)
    (haux : precisionLowerBound n δ ≤ Q.auxiliary) :
    precisionLowerBound n δ ≤ Q.target :=
  lower_bound_of_reduction haux

end Qatlib.Papers.ConvexOpt18.MainResults
