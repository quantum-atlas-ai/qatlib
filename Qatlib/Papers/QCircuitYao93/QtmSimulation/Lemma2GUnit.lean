/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.GUnitExistenceQuan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Lemma2GUnit

open Qatlib.Foundations.StandardDefs.WindowSim

theorem lemma2_g_unit_existence : GUnitExistence :=
  gUnitExistence

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Lemma2GUnit
