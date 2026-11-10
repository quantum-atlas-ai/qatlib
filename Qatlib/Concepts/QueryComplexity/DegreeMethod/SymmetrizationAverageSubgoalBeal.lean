/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SymmetrizationAverageSubgoalStat
set_option warningAsError false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

theorem symmetrizationAverageSubgoal : SymmetrizationAverageSubgoal := by
  intro I _ _ p
  exact ⟨avgPoly p, fun k hk => layerAverage_eq_avgPoly p k hk, avgPoly_natDegree_le p⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
