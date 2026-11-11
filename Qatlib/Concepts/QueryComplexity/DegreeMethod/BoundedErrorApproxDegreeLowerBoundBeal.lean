/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BoundedErrorApproxDegreeLowerBoundStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial

/-!
# Approximate degree lower bounds for bounded-error queries

This module proves `BoundedErrorApproxDegreeQueryLowerBound` by representing circuit acceptance
probabilities with Boolean polynomials. The resulting degree estimate is the standard
bounded-error query lower bound from the polynomial method [BealsEtAl2001].

## Main statements

* `boundedErrorApproxDegreeQueryLowerBound`: any circuit whose acceptance probability
  approximates a Boolean function within one-third has query count at least half its approximate
  degree.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- For a bit oracle circuit whose acceptance probability approximates `f` within one-third on
every input, `approxDegree f ≤ 2 * QueryCount C` [BealsEtAl2001]. -/
theorem boundedErrorApproxDegreeQueryLowerBound : BoundedErrorApproxDegreeQueryLowerBound := by
  intro I W _ _ _ _ C ψ E f hf
  obtain ⟨hd,_,he⟩ := acceptance_boolean_multilinearization_preserves_run C ψ E
  apply le_trans ?_ hd
  unfold approxDegree
  apply csInf_le'
  refine ⟨booleanAcceptancePolynomial C ψ E, ?_, rfl⟩
  intro g
  rw [boolEval, he g]
  exact hf g

end Qatlib.Concepts.QueryComplexity.DegreeMethod
