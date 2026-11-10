/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.JacobiAnger

def JacobiAngerCorrectedDegree : Prop :=
  ∀ (τ ε : ℝ), 0 ≤ τ → 0 < ε → ε ≤ 1 →
    4 * τ ^ (lcCorrectedQ τ ε : ℝ) /
        (2 ^ (lcCorrectedQ τ ε : ℝ) * (lcCorrectedQ τ ε).factorial : ℝ) ≤ ε / 8 ∧
    τ + 1 ≤ (lcCorrectedQ τ ε : ℝ)

end Qatlib.Concepts.QspSimulation.JacobiAnger
