/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Rounded counting at square root precision

This module defines the readout parameters for Corollary 14 of [BrassardEtAl2002]. The grid
`approxCountCor14Grid` is `⌈√N⌉`, and `approxCountCor14Output` rounds the corresponding scaled
amplitude estimate to an integer using `⌊x + 1/2⌋`.

## Main statements

* `approxCountCor14Grid`: the square root counting grid.
* `approxCountCor14Output`: the rounded integer count.

## References

* [Brassard et al., Corollary 14][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- The counting grid size `⌈√N⌉` used in [Brassard et al., Corollary 14][BrassardEtAl2002]. -/
noncomputable def approxCountCor14Grid (N : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (N : ℝ))
/-- The integer count obtained by rounding `N * aeEstimate (approxCountCor14Grid N) z` via `⌊x +
1/2⌋`. -/
noncomputable def approxCountCor14Output (N : ℕ)
    (z : Fin (approxCountCor14Grid N)) : ℤ :=
  ⌊(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (approxCountCor14Grid N) z+1/2⌋

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
