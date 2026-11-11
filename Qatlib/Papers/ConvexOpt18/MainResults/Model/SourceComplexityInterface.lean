/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceCostModel

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 query-complexity interface for the lower-bound claims

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3 (18 Dec 2019).

The paper's lower bounds (Theorems 1.2, 3.2, 3.3, 3.4, Lemmas 3.1, A.1) are proved by
reduction to *search with wildcards* (Section 3.1 and [1, Theorem 3.1]).  This module fixes
the interface at which those statements are recorded:

* `AccuracySpec` is the accuracy/success contract of (1.7), (3.4), (3.16);
* `QueryComplexityReduction` bundles the target complexity, the complexity of the auxiliary
  (wildcard-search) problem, and the paper's simulation inequality
  `auxiliary ≤ target` (one membership/evaluation query is simulated by one wildcard query,
  Lemmas 3.2--3.4);
* `wildcardSearchLowerBound`, `maxNormLowerBound`, `precisionLowerBound` are the cited
  `Ω(√n)` / `Ω(√n / log n)` / `Ω(√n / log(1/δ))` bounds with the explicit constants used
  in the paper's arithmetic (the cited theorems only guarantee a universal constant).

The lower-bound theorems are then honest statements of the paper's reduction step: the
remaining input is the externally cited wildcard-search lower bound `[1, Theorem 3.1]`,
which is recorded as a hypothesis of the interface rather than re-derived (the paper itself
cites it and does not prove it).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Accuracy and success contract of an optimization problem: error at most `ε` in the sense
of (1.7)/(3.4)/(3.16) and success probability at least `9/10` (or `0.8` where the paper
weakens the requirement). -/
structure AccuracySpec where
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  success : ℝ
  success_ge : 9 / 10 ≤ success

/-- A query-complexity reduction: `target` is the complexity of the problem under study,
`auxiliary` that of the auxiliary wildcard-search problem, and `reduction` is the paper's
simulation inequality (Section 3.1: a `q`-query algorithm for the target yields a `q`-query
algorithm for the auxiliary problem). -/
structure QueryComplexityReduction where
  spec : AccuracySpec
  target : ℝ
  target_nonneg : 0 ≤ target
  auxiliary : ℝ
  reduction : auxiliary ≤ target

/-- The cited search-with-wildcards lower bound `[1, Theorem 3.1]`, with the constant `1/2`:
`√n / 2` queries are necessary. -/
def wildcardSearchLowerBound (n : ℕ) : ℝ := Real.sqrt n / 2

/-- The max-norm lower bound of Theorem 3.3, `Ω(√n / log n)`, with constant `1/2`. -/
def maxNormLowerBound (n : ℕ) : ℝ := Real.sqrt n / (2 * Real.log n)

/-- The precision-dependent lower bound of Lemma 3.1, `Ω(√n / log(1/δ))`, constant `1/2`. -/
def precisionLowerBound (n : ℕ) (δ : ℝ) : ℝ := Real.sqrt n / (2 * Real.log (1 / δ))

/-- The classical subgradient lower bound of Lemma A.1, `Ω̃(n)`, with constant `1/4`. -/
def classicalSubgradientLowerBound (n : ℕ) : ℝ := (n : ℝ) / 4

/-- The core reduction step shared by all lower-bound claims: if the target problem reduces
(with no query overhead) to an auxiliary problem whose complexity is at least `c`, then the
target problem's complexity is at least `c`. -/
lemma lower_bound_of_reduction {c : ℝ} {Q : QueryComplexityReduction}
    (h : c ≤ Q.auxiliary) : c ≤ Q.target :=
  le_trans h Q.reduction

end Qatlib.Papers.ConvexOpt18.MainResults
