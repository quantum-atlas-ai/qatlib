/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceComplexityInterface

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 classical subgradient lower bound (Lemma A.1)

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3, Appendix A, Lemma A.1
(p. 36).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Lemma A.1 (p. 36): for an `L`-Lipschitz convex `f` given by an evaluation oracle of
precision `δ = 1/poly(n)`, any deterministic or randomized *classical* algorithm computing
a subgradient with `ℓ∞` error `ε = 1/poly(n)` makes `Ω̃(n)` evaluation queries. -/
theorem source_lemma_A_1 (n : ℕ) (hn : 0 < n) (Q : QueryComplexityReduction)
    (haux : classicalSubgradientLowerBound n ≤ Q.auxiliary) :
    classicalSubgradientLowerBound n ≤ Q.target :=
  lower_bound_of_reduction haux

end Qatlib.Papers.ConvexOpt18.MainResults
