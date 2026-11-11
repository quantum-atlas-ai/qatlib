/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# The bounded-error approximate degree query bound

This module defines `BoundedErrorApproxDegreeQueryLowerBound`, the statement relating one-third
approximate degree to the query count of a bit oracle circuit. The acceptance event and initial
state are explicit, matching the acceptance polynomial framework of [BealsEtAl2001].

## Main statements

* `BoundedErrorApproxDegreeQueryLowerBound`: a uniform one-third acceptance approximation
  implies `approxDegree f ≤ 2 * QueryCount C`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The proposition that every bit oracle circuit whose event probability approximates a Boolean
function within one-third satisfies `approxDegree f ≤ 2 * QueryCount C`. -/
def BoundedErrorApproxDegreeQueryLowerBound : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit (Qatlib.Concepts.QueryWordCore.QueryMachinery.PolynomialWorkspace I W))
    (ψ : Qatlib.Foundations.PureStateMath.QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (f : (I → Bool) → Bool),
    (∀ g : I → Bool,
        |Qatlib.Foundations.PureStateMath.MeasureProb
            (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn g) 1) C ψ) E
          - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3) →
    approxDegree f ≤ 2 * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C

end Qatlib.Concepts.QueryComplexity.DegreeMethod
