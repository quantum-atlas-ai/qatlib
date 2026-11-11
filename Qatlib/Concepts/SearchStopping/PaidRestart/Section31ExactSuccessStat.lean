/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalStat
import Qatlib.Concepts.SearchStopping.PaidRestart.QuarterDensitySearchAuxiliary

/-!
# Statement of exact quarter-density search

Defines `Section3_1ExactSuccess`, the assertion that a positive marked count equal to one
quarter of the search-space size gives exact one-query search. The conclusion is expressed
through `QuarterDensitySearchClaim`. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Section3_1ExactSuccess`: The proposition that positive marked count `m` with `4 * m =
  Fintype.card I` yields `QuarterDensitySearchClaim I m`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.PaidRestart

/-- The proposition that positive marked count `m` with `4 * m = Fintype.card I` yields
`QuarterDensitySearchClaim I m`. -/
def Section3_1ExactSuccess : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ),
    0 < m → 4 * m = Fintype.card I → QuarterDensitySearchClaim I m

end Qatlib.Concepts.SearchStopping.PaidRestart
