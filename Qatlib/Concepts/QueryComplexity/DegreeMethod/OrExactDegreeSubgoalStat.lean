/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound

/-!
# Statement of the exact degree bound for OR

The proposition `OrExactDegreeSubgoal` packages the exact polynomial degree lower bound for OR
over arbitrary nonempty finite index types. It is the degree statement underlying the OR
application of the polynomial method in [BealsEtAl2001].

## Main statements

* `OrExactDegreeSubgoal`: Specifies the lower bound on the total degree of an exact real
  polynomial for OR.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The proposition that every real polynomial representing OR on a nonempty finite Boolean cube
has total degree at least the cardinality of its index type. -/
def OrExactDegreeSubgoal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (p : MvPolynomial I ℝ),
    0 < Fintype.card I →
    (∀ g : I → Bool,
        MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p
          = if (∃ i : I, g i = true) then (1 : ℝ) else 0) →
    Fintype.card I ≤ p.totalDegree

end Qatlib.Concepts.QueryComplexity.DegreeMethod
