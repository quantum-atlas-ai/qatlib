/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
# Entropy lower bound specification

This module defines `Lemma22Spec.expected`, the entropy estimate for capped finite priors
appearing in ordered Bayesian search [BenOrHassidim2007]. The proposition requires base-two
entropy at least log₂(1/ε) whenever the prior is nonnegative, sums to one, and has all cell
masses below a positive ε.

## Main definitions

* `Lemma22Spec.expected`: the entropy lower bound under a strict cell-mass cap.

## References

* [Ben-Or and Hassidim, Lemma 2.2][BenOrHassidim2007]
-/

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Spec
/-- The proposition that a nonnegative normalized finite prior whose weights are all below a
positive ε has base-two entropy at least log₂(1/ε). -/
def expected : Prop :=
  (∀ (n : ℕ) (a : Fin n → ℝ) (ε : ℝ),
  (∀ i, 0 ≤ a i) → (∑ i, a i) = 1 → 0 < ε → (∀ i, a i < ε) →
  Real.log (1 / ε) / Real.log 2 ≤ - ∑ i, a i * (Real.log (a i) / Real.log 2))
end Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Spec
