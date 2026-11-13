/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialTargets

/-!
# The combinatorial triangle search specification

`Theorem1` names `theorem1SourceCorrected`, the parameterized combinatorial triangle search
specification. Its guarantees are sound triangle outputs, a finite rejection count bound when a
triangle exists, and a query estimate with explicit capability and logarithmic factors. For
background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `Theorem1`: The corrected capability conditional combinatorial triangle search specification
  `theorem1SourceCorrected`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.MainResults

/-- The corrected capability conditional combinatorial triangle search specification
`theorem1SourceCorrected`. -/
def Theorem1 : Prop := theorem1SourceCorrected

end Qatlib.Concepts.WalkSearch.MainResults
