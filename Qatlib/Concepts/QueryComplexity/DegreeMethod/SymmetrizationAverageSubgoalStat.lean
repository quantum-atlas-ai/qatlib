/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
set_option warningAsError false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

def SymmetrizationAverageSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (p : MvPolynomial I ℝ),
    ∃ q : Polynomial ℝ,
      (∀ k : ℕ, k ≤ Fintype.card I →
        Qatlib.Concepts.QueryComplexity.DegreeMethod.layerAverage p k = Polynomial.eval (k : ℝ) q) ∧
        Polynomial.natDegree q ≤ p.totalDegree

end Qatlib.Concepts.QueryComplexity.DegreeMethod
