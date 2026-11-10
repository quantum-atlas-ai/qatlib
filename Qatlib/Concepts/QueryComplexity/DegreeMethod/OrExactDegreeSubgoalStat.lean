/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
set_option warningAsError false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

def OrExactDegreeSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (p : MvPolynomial I ℝ),
    0 < Fintype.card I →
    (∀ g : I → Bool,
        MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p
          = if (∃ i : I, g i = true) then (1 : ℝ) else 0) →
    Fintype.card I ≤ p.totalDegree

end Qatlib.Concepts.QueryComplexity.DegreeMethod
