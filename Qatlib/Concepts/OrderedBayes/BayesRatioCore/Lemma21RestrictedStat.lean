/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedSpec
def expected : Prop :=
  (∀ (n : ℕ) (a : Fin n → ℝ) (ε : ℝ),
  0 < ε → ε ≤ 1 / 2 → (∀ i, 0 ≤ a i) → (∑ i, a i) = 1 → (∀ i, a i < ε) →
  ∃ k : ℕ, 0 < k ∧ k < n ∧
    1 / 2 - ε ≤ (∑ i : Fin n, if i.val < k then a i else 0) ∧
    (∑ i : Fin n, if i.val < k then a i else 0) < 1 / 2)
end Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedSpec
