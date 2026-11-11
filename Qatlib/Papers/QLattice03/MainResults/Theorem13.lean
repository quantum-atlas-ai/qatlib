/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Lemma45
import Qatlib.Papers.QLattice03.MainResults.Lemma49
import Qatlib.Papers.QLattice03.MainResults.Reductions

/-!
# The subset-sum to DCP implication

This module defines `subsetSum_implies_dcp`, the proposition that every correct subset-sum
routine yields a DCP solver indexed by failure parameter 1. It records the implication
associated with Theorem 1.3 of [Regev2004] as a proposition.

## Main statements

* `subsetSum_implies_dcp`: The subset-sum solver implication to be established.

## References

* [Regev, 2004][Regev2004]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

/-- The proposition that any routine satisfying `SolvesSubsetSum` yields `HasDCPSolver 1`,
corresponding to the reduction in [Regev, Theorem 1.3][Regev2004]. -/
def subsetSum_implies_dcp : Prop :=
  ∀ (S : SubsetSumRoutine), SolvesSubsetSum S → HasDCPSolver 1

end Qatlib.Papers.QLattice03.MainResults
