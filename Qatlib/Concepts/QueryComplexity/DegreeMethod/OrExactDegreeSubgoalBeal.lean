/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrExactDegreeSubgoalStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeAndOr
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

theorem orExactDegreeSubgoal : OrExactDegreeSubgoal := by
  intro I _ _ p hn hp
  exact boolean_multilinear_or_totalDegree p hn hp

end Qatlib.Concepts.QueryComplexity.DegreeMethod
