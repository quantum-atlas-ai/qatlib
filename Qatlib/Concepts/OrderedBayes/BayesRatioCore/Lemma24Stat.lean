/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesLearner

/-!
# Learner stage bound specification

This module defines `Lemma2_4`, the expected-stage estimate for a Bayesian learner started from
the uniform prior in the ordered search framework of [BenOrHassidim2007]. For n ≥ 2 and the
specified noise and threshold parameters with positive `queryInfo p`, the required bound is
log₂(n)/`queryInfo p` + 2/(3 `queryInfo p`).

## Main definitions

* `Lemma2_4`: the uniform-prior expected-stage proposition.

## References

* [Ben-Or and Hassidim, Lemma 2.4][BenOrHassidim2007]
-/

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- The proposition bounding the uniform-prior learner's expected stage count by
log₂(n)/`queryInfo p` + 2/(3 `queryInfo p`) for n ≥ 2, 1/2 < p < 1, positive query
information, and the specified positive threshold cap. -/
def Lemma2_4 : Prop :=
  ∀ (n : ℕ) (p ε : ℝ) (hn2 : 2 ≤ n) (_ : 1 / 2 < p) (_ : p < 1) (_ : 0 < ε),
      ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))) → 0 < queryInfo p →
      learnerExpectedStages (n := n) (lt_of_lt_of_le zero_lt_two hn2) p ε
          (uniformPosterior (n := n)) ≤
        ENNReal.ofReal
          ((Real.log n / Real.log 2) / queryInfo p + 2 / (3 * queryInfo p))

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
