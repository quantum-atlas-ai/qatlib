/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.DiscreteNodeDerivative
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveClassicalSimulationBeal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Matrix
open scoped Classical BigOperators

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
