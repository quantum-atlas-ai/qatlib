/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.OneRoundWindowSimulationQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Section6OneRound

open Qatlib.Foundations.StandardDefs.WindowSim

theorem section6_oneRound_window_simulation : OneRoundWindowSimulation :=
  oneRoundWindowSimulation

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Section6OneRound
