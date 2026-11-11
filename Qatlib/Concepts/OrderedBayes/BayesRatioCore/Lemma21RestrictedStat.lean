/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card

/-!
# Prefix threshold specification

This module defines `Lemma21RestrictedSpec.expected`, a finite prefix-mass statement for ordered
Bayesian search [BenOrHassidim2007]. For a normalized nonnegative prior with every cell below ε
and 0 < ε ≤ 1/2, it requires a nonempty proper prefix with mass at least 1/2 - ε and strictly
below 1/2.

## Main definitions

* `Lemma21RestrictedSpec.expected`: the restricted balanced-prefix proposition.

## References

* [Ben-Or and Hassidim, Lemma 2.1][BenOrHassidim2007]
-/

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedSpec
/-- The proposition that every nonnegative normalized finite prior with all weights below ε,
where 0 < ε ≤ 1/2, has a nonempty proper prefix of mass in [1/2 - ε, 1/2). -/
def expected : Prop :=
  (∀ (n : ℕ) (a : Fin n → ℝ) (ε : ℝ),
  0 < ε → ε ≤ 1 / 2 → (∀ i, 0 ≤ a i) → (∑ i, a i) = 1 → (∀ i, a i < ε) →
  ∃ k : ℕ, 0 < k ∧ k < n ∧
    1 / 2 - ε ≤ (∑ i : Fin n, if i.val < k then a i else 0) ∧
    (∑ i : Fin n, if i.val < k then a i else 0) < 1 / 2)
end Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedSpec
