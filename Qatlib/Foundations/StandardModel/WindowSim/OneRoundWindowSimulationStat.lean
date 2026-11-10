/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.QtmSimulationDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.StandardDefs.WindowSim

open Matrix

def OneRoundWindowSimulation : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (A : Type) [Fintype A] [DecidableEq A]
      (M : LocalQTM Q A) (t : ℕ), 0 < t →
    ∀ G : Matrix (GWindow Q A) (GWindow Q A) ℂ,
      GUnitFixesH M G → GUnitSteps M G →
        ∀ c : WindowCfg t Q A,
          0 < c.head.val → c.head.val < 2 * t →
            Run (1 : Matrix (WReg t Q A) (WReg t Q A) ℂ) (kRoundCircuit t G)
                (Qatlib.Foundations.PureStateMath.Ket (windowEncode c))
              = windowEmbed (windowStep M *ᵥ Qatlib.Foundations.PureStateMath.Ket c)

end Qatlib.Foundations.StandardDefs.WindowSim
