/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma45
import Qatlib.Papers.QLattice03.MainResults.Lemma49
import Qatlib.Papers.QLattice03.MainResults.Reductions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

def subsetSum_implies_dcp : Prop :=
  ∀ (S : SubsetSumRoutine), SolvesSubsetSum S → HasDCPSolver 1

end Qatlib.Papers.QLattice03.MainResults
