/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrExactDegreeSubgoalStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeAndOr

/-!
# Exact polynomial degree lower bound for OR

This module proves `OrExactDegreeSubgoal` using the Boolean OR degree bound. Every real
polynomial representing OR on a nonempty Boolean cube has total degree at least the number of
variables, as used in the polynomial method of [BealsEtAl2001].

## Main statements

* `orExactDegreeSubgoal`: Establishes the packaged exact-degree lower bound for OR.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- Establishes that every real polynomial representing OR on a nonempty Boolean cube has total
degree at least the number of variables [BealsEtAl2001]. -/
theorem orExactDegreeSubgoal : OrExactDegreeSubgoal := by
  intro I _ _ p hn hp
  exact boolean_multilinear_or_totalDegree p hn hp

end Qatlib.Concepts.QueryComplexity.DegreeMethod
