/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MeasurementStatistics

/-!
# Observable associated with a finite POVM payoff

This module defines `payoffObservable` as the sum of the POVM effect matrices weighted by a real
payoff function, with each real coefficient cast to a complex scalar. The definition accepts any
finite outcome type and imposes no sign or range restriction on its payoffs.

It supplies the observable representation used by the measurement interfaces for quantum SDP
analysis [BrandaoSvore2017]. Expectation identities and positivity bounds are proved in
`MatrixOptimizationInterfaces`.

## Main statements

* `payoffObservable`: Form the operator `∑ o, (f o : ℂ) • (Λ.mats o).mat` from a finite POVM and
  a real-valued payoff.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open scoped BigOperators

/-- The operator obtained by summing the effects of a finite POVM with coefficients given by a
real-valued payoff function cast to complex scalars. -/
def payoffObservable {O : Type*} [Fintype O] {D : ℕ}
    (Λ : POVM O (Fin D)) (f : O → ℝ) : Operator D :=
  ∑ o, ((f o : ℝ) : ℂ) • (Λ.mats o).mat

end Qatlib.Concepts.SdpDuality.ConeSeparation
