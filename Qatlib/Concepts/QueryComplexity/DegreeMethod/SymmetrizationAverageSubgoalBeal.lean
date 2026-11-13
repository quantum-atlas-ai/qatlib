/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SymmetrizationAverageSubgoalStat

/-!
# Polynomial representation of Hamming-layer averages

This module proves `symmetrizationAverageSubgoal`: averaging a real multivariate polynomial over
Boolean inputs of each Hamming weight produces values of a univariate polynomial whose degree
does not exceed the original total degree. This is the symmetrization step used in polynomial
query lower bounds [BealsEtAl2001].

## Main statements

* `symmetrizationAverageSubgoal`: Hamming-layer averaging preserves the polynomial degree bound.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- Hamming-layer averages of a real multivariate polynomial are represented by a univariate
polynomial of no greater degree, as used in the polynomial method of [BealsEtAl2001]. -/
theorem symmetrizationAverageSubgoal : SymmetrizationAverageSubgoal := by
  intro I _ _ p
  exact ⟨avgPoly p, fun k hk => layerAverage_eq_avgPoly p k hk, avgPoly_natDegree_le p⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
