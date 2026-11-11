/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# Statement of the exact polynomial query bound

The proposition `ExactDegreeQueryLowerBound` states that a finite Boolean-oracle circuit whose
acceptance probability exactly represents a Boolean function uses at least half its exact
polynomial degree in queries. It quantifies over finite input and workspace types, initial
states, and accepting sets.

This packages the exact-computation degree bound of [BealsEtAl2001] for use by the
acceptance-polynomial proof.

## Main statements

* `ExactDegreeQueryLowerBound`: the exact-degree lower bound as a proposition over finite
  Boolean-oracle circuits.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The assertion that every finite Boolean-oracle circuit whose acceptance probability exactly
represents a Boolean function has query count at least half that function's exact polynomial
degree [BealsEtAl2001]. -/
def ExactDegreeQueryLowerBound : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit (Qatlib.Concepts.QueryWordCore.QueryMachinery.PolynomialWorkspace I W))
    (ψ : Qatlib.Foundations.PureStateMath.QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (f : (I → Bool) → Bool),
    (∀ g : I → Bool,
        Qatlib.Foundations.PureStateMath.MeasureProb
          (Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Foundations.PureStateMath.TensorGate (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn g) 1) C ψ) E
          = if f g then (1 : ℝ) else 0) →
    exactDegree f ≤ 2 * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C

end Qatlib.Concepts.QueryComplexity.DegreeMethod
