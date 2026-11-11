/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesLearner

/-!
# Expected information drift specification

This module defines `Lemma2_3`, the expected-information drift proposition for the ordered
search analysis of [BenOrHassidim2007]. For a nonnegative normalized prior and an almost
balanced cut, the expected increase in `postInfo` is at least `queryInfo p` times 1 - 1/(3 log₂
n), under the specified noise and threshold hypotheses.

## Main definitions

* `Lemma2_3`: the dimension-dependent lower bound on one-step expected information gain.

## References

* [Ben-Or and Hassidim, Lemma 2.3][BenOrHassidim2007]
-/

set_option warningAsError false

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition that a nonnegative normalized prior and a cut with prefix mass in [1/2 - ε,
1/2) have expected information gain at least `queryInfo p` times 1 - 1/(3 log₂ n), under the
stated dimension, noise, and threshold bounds. -/
def Lemma2_3 : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (i : Fin n) (p ε : ℝ),
    2 ≤ n → 1 / 2 < p → p < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))) →
      (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 →
      1 / 2 - ε ≤ prefixMass a i → prefixMass a i < 1 / 2 →
      queryInfo p * (1 - 1 / (3 * (Real.log n / Real.log 2))) ≤
        normFalse a i p * (postInfo (updateFalse a i p) - postInfo a) +
          normTrue a i p * (postInfo (updateTrue a i p) - postInfo a)

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
