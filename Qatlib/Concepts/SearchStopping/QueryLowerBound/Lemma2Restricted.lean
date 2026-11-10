/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u

def Lemma2Restricted : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (A : Finset I) (θ : ℝ),
      (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ) →
      0 < Real.sin (2 * θ) → ∀ (m : ℕ), 0 < m →
        RandomizedSuccess A m =
          1 / 2 - Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) ∧
        (1 / Real.sin (2 * θ) ≤ (m : ℝ) → 1 / 4 ≤ RandomizedSuccess A m)

end Qatlib.Concepts.SearchStopping.QueryLowerBound
