/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesLearner
set_option warningAsError false

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

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
