/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.StatisticalConfidence
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

def confidencePeakSpace (b : ConfidenceBudget) : ℕ :=
  max b.pilotRecords b.blockSize

def nativeSelectorCells (b : ConfidenceBudget) : ℕ :=
  b.blockSize * b.blockCount

end Qatlib.Concepts.MixedInstrument.ClockBridge
