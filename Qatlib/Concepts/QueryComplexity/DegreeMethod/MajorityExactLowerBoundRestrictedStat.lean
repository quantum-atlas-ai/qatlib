/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# The restricted exact-majority query proposition

`MajorityExactQueryLowerBoundRestricted` states a query lower bound for circuits on inputs
indexed by `K ⊕ J`, where `|K| = |J| + 1`. On the restriction with every `J` bit false, the
selected event must have probability one exactly when every `K` bit is true; the asserted bound
is `|K| ≤ 2 * QueryCount C`.

The mathematical background is developed in [BealsEtAl2001].

## Main statements

* `MajorityExactQueryLowerBoundRestricted`: packages the restricted acceptance condition and the
  resulting query bound as a proposition.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The proposition that exact acceptance of AND on the restriction with all `J` bits false and
`|K| = |J| + 1` forces `|K| ≤ 2 * QueryCount C`. -/
def MajorityExactQueryLowerBoundRestricted : Prop :=
  ∀ (K J W : Type) [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
    [Fintype W] [DecidableEq W]
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit (Qatlib.Concepts.QueryWordCore.QueryMachinery.PolynomialWorkspace (K ⊕ J) W))
    (ψ : Qatlib.Foundations.PureStateMath.QState (PolynomialWorkspace (K ⊕ J) W))
    (E1 : Finset (PolynomialWorkspace (K ⊕ J) W)),
    Fintype.card J + 1 = Fintype.card K →
    (∀ g : K → Bool,
        Qatlib.Foundations.PureStateMath.MeasureProb
          (Qatlib.Foundations.QueryWordCore.Circuit.Run
            (Qatlib.Foundations.PureStateMath.TensorGate
              (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn (Sum.elim g (fun _ => false))) 1) C ψ) E1
          = if (∀ k : K, g k = true) then (1 : ℝ) else 0) →
    Fintype.card K ≤ 2 * Qatlib.Foundations.QueryWordCore.Circuit.QueryCount C

end Qatlib.Concepts.QueryComplexity.DegreeMethod
