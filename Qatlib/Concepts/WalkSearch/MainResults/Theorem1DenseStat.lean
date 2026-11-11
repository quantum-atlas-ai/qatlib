/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialTargets

/-!
# The dense triangle search specification

`Theorem1Dense` names `theorem1DenseSourceCorrected`, the dense specialization of the capability
conditional combinatorial triangle search guarantee. It retains the soundness and rejection
count requirements and the explicit logarithmic and fee factors multiplying the `n^(10 / 7)`
cost. For background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `Theorem1Dense`: The dense corrected combinatorial triangle search specification
  `theorem1DenseSourceCorrected`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkSearch.MainResults

/-- The dense corrected combinatorial triangle search specification
`theorem1DenseSourceCorrected`. -/
def Theorem1Dense : Prop := theorem1DenseSourceCorrected

end Qatlib.Concepts.WalkSearch.MainResults
