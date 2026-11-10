/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Spec
def expected : Prop :=
  (∀ (n : ℕ) (a : Fin n → ℝ) (ε : ℝ),
  (∀ i, 0 ≤ a i) → (∑ i, a i) = 1 → 0 < ε → (∀ i, a i < ε) →
  Real.log (1 / ε) / Real.log 2 ≤ - ∑ i, a i * (Real.log (a i) / Real.log 2))
end Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Spec
