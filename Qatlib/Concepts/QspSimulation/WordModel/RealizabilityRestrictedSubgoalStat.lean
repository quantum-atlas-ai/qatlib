/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.QspSimulation.WordModel

def RealizabilityRestrictedSubgoal : Prop :=
  ∃ (phis : List ℝ), phis.length = 2 ∧
    ∀ (x : ℝ), -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 0 = ((2 * x ^ 2 - 1 : ℝ) : ℂ)

end Qatlib.Concepts.QspSimulation.WordModel
