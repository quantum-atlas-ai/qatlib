/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.OneRoundWindowSimulationQuan

/-!
# One-round finite-window simulation

`section6_oneRound_window_simulation` exposes `OneRoundWindowSimulation`, the one-round
simulation property used to connect an ordered local sweep with finite-window QTM evolution. See
[Yao1993].

## Main statements

* `section6_oneRound_window_simulation`: establishes the one-round window simulation contract.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Section6OneRound

open Qatlib.Foundations.StandardDefs.WindowSim

/-- The one-round window simulation property `OneRoundWindowSimulation` holds. This is the
formal endpoint for the ordered sweep in Section 6 of [Yao1993]. -/
theorem section6_oneRound_window_simulation : OneRoundWindowSimulation :=
  oneRoundWindowSimulation

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Section6OneRound
