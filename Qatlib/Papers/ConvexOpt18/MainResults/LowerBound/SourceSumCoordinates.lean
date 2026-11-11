/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceComplexityInterface

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 sum-of-coordinates lower bound (Theorem 3.2)

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3, Section 3.1:
Theorem 3.2 (p. 21, equation (3.4)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Theorem 3.2 (p. 21): solving the sum-of-coordinates problem
(`C_s = ×ᵢ [sᵢ-2, sᵢ+1]`, `f(x) = Σ xᵢ`) to accuracy `1/3` with success probability at least
`0.9` requires `Ω(√n)` membership queries.

The paper proves this by reducing search-with-wildcards to the sum-of-coordinates problem
(one membership query is simulated by one wildcard query) and invoking the cited
`Ω(√n)` lower bound for search with wildcards [1, Theorem 3.1].  The statement below records
exactly that reduction: `Q.auxiliary` is the wildcard-query complexity, `Q.target` the
membership-query complexity, and `Q.reduction` is the simulation inequality proved in
Section 3.1; the cited wildcard bound enters through `hwild`. -/
theorem source_theorem_3_2 (n : ℕ) (hn : 0 < n) (Q : QueryComplexityReduction)
    (hε : Q.spec.ε = 1 / 3) (hsuccess : 9 / 10 ≤ Q.spec.success)
    (hwild : wildcardSearchLowerBound n ≤ Q.auxiliary) :
    wildcardSearchLowerBound n ≤ Q.target :=
  lower_bound_of_reduction hwild

end Qatlib.Papers.ConvexOpt18.MainResults
