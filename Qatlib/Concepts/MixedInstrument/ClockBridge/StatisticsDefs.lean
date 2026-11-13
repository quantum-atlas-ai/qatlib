/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.StatisticalConfidence

/-!
# Space quantities for confidence budgets

This module defines `confidencePeakSpace` as the maximum of the pilot record count and one main
block size. It defines `nativeSelectorCells` as the product of block size and block count for
comparison with that space quantity. See [Montanaro2015] for the Monte Carlo context.

## Main statements

* `confidencePeakSpace`: records the maximum phase size.
* `nativeSelectorCells`: counts all main-phase selector cells.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The maximum of the pilot record count and the main block size in a confidence budget. -/
def confidencePeakSpace (b : ConfidenceBudget) : ℕ :=
  max b.pilotRecords b.blockSize

/-- The total number of main-phase selector cells, given by block size times block count. -/
def nativeSelectorCells (b : ConfidenceBudget) : ℕ :=
  b.blockSize * b.blockCount

end Qatlib.Concepts.MixedInstrument.ClockBridge
