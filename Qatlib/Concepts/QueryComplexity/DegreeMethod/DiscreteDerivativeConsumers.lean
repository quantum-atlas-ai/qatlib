/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.DiscreteNodeDerivative
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveClassicalSimulationBeal

/-!
# Consequences of the sharp polynomial derivative bound

This module packages the chain from a supplied sharp Markov derivative inequality on `[-1, 1]`
to polynomial and adaptive-query bounds. The theorem `bbcmw_chain_of_sharp` first obtains the
discrete-node derivative estimate, then derives `ApproximatePolynomialBlockSensitivity`,
`AdaptiveBlockSensitivityQueryBound`, and `AdaptiveClassicalSimulation`. This follows the
polynomial-method framework of [BealsEtAl2001].

## Main statements

* `bbcmw_chain_of_sharp`: the sharp derivative inequality implies the approximate-polynomial
  block-sensitivity bound, the adaptive block-sensitivity query bound, and adaptive classical
  simulation.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators

/-- The sharp Markov derivative inequality on `[-1, 1]` implies
`ApproximatePolynomialBlockSensitivity`, `AdaptiveBlockSensitivityQueryBound`, and
`AdaptiveClassicalSimulation` through the polynomial-method chain of [BealsEtAl2001]. -/
theorem bbcmw_chain_of_sharp
    (hsharp : ∀ (d : ℕ) (p : Polynomial ℝ) (C : ℝ), p.natDegree ≤ d → 0 ≤ C →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) →
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval x| ≤ (d : ℝ)^2*C) :
    ApproximatePolynomialBlockSensitivity ∧ AdaptiveBlockSensitivityQueryBound ∧
      AdaptiveClassicalSimulation := by
  have hpoly := approximatePolynomialBlockSensitivity_of_discrete
    (discrete_node_derivative_of_sharp hsharp)
  have hquery := adaptiveBlockSensitivityQueryBound_of_polynomial hpoly
  exact ⟨hpoly,hquery,adaptiveClassicalSimulation_of_queryBound hquery⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
