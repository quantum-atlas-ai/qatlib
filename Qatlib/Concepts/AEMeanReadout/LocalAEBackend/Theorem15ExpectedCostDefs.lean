/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat

/-!
# Total cost of adaptive approximate counting

`basicApproxCountTotalCost` adds the grid sizes of the executed preliminary rounds to the final
estimation grid size. This is the cost ledger for the adaptive approximate counter of
[BrassardEtAl2002].

## Main statements

* `basicApproxCountTotalCost`: the sum of preliminary and final estimation costs.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open scoped Classical

/-- The total grid-size cost of the preliminary rounds before `basicApproxCountStop`, followed
by the final estimation round. -/
noncomputable def basicApproxCountTotalCost (N : ℕ) (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val)) : ℕ :=
  (∑ l : Fin (basicApproxCountLoopCap N),
    if l.val < basicApproxCountStop N ω then 2*2^l.val else 0) +
  basicApproxCountFinalM ε (basicApproxCountStop N ω)

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
