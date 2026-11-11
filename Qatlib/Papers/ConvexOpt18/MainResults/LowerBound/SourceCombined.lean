/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceComplexityInterface

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 combined lower bound (Theorems 1.2 and 3.4)

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3: Theorem 1.2 (p. 4,
equation (1.7)) and Theorem 3.4 (p. 23, equations (3.43)--(3.44)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Theorem 3.4 (p. 23): for `C_s = ×ᵢ [sᵢ-2, sᵢ+1]` and
`f = f_M + f_{E,c}` on `C_s × [0,1]ⁿ` (equation (3.43)), output satisfying (3.44) with
probability at least `0.8` requires `Ω(√n)` membership queries and `Ω(√n / log n)`
evaluation queries.

The statement records both reductions to the wildcard-search lower bound. -/
theorem source_theorem_3_4 (n : ℕ) (hn : 2 ≤ n) (Qmem Qeval : QueryComplexityReduction)
    (hmem : wildcardSearchLowerBound n ≤ Qmem.auxiliary)
    (heval : maxNormLowerBound n ≤ Qeval.auxiliary)
    (hmem_succ : 4 / 5 ≤ Qmem.spec.success)
    (heval_succ : 4 / 5 ≤ Qeval.spec.success) :
    wildcardSearchLowerBound n ≤ Qmem.target ∧ maxNormLowerBound n ≤ Qeval.target :=
  ⟨lower_bound_of_reduction hmem, lower_bound_of_reduction heval⟩

/-- Theorem 1.2 (p. 4, equation (1.7)): there is a convex body `K`, a convex `f` and a
precision `ε > 0` such that output satisfying `f(x̃) ≤ min_K f + ε` with success probability
at least `0.8` requires `Ω(√n)` membership queries and `Ω(√n / log n)` evaluation queries.

The statement records the two lower bounds as reductions to the wildcard-search lower
bound; existence of `K`, `f`, `ε` is absorbed in the complexity quantities `Qmem`, `Qeval`. -/
theorem source_theorem_1_2 (n : ℕ) (hn : 2 ≤ n) (Qmem Qeval : QueryComplexityReduction)
    (hmem : wildcardSearchLowerBound n ≤ Qmem.auxiliary)
    (heval : maxNormLowerBound n ≤ Qeval.auxiliary)
    (hmem_pos : 0 < Qmem.spec.ε) (heval_pos : 0 < Qeval.spec.ε)
    (hmem_succ : 4 / 5 ≤ Qmem.spec.success)
    (heval_succ : 4 / 5 ≤ Qeval.spec.success) :
    wildcardSearchLowerBound n ≤ Qmem.target ∧ maxNormLowerBound n ≤ Qeval.target :=
  ⟨lower_bound_of_reduction hmem, lower_bound_of_reduction heval⟩

end Qatlib.Papers.ConvexOpt18.MainResults
