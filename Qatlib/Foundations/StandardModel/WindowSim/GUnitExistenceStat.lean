/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

def GUnitExistence : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
      (M : LocalQTM Q A),
    ∃ G : Matrix (GWindow Q A) (GWindow Q A) ℂ,
      G ∈ Matrix.unitaryGroup (GWindow Q A) ℂ ∧
      GUnitFixesH M G ∧ GUnitSteps M G

end Qatlib.Foundations.StandardDefs.WindowSim
