/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.Achievability

def AchievableNecessitySourceForm : Prop :=
  ∀ (phis : List ℝ) (θ : ℝ),

    (lcPlusAmp phis θ).re * (lcPlusAmp phis θ).re
      + (lcPlusAmp phis θ).im * (lcPlusAmp phis θ).im ≤ 1 ∧

    lcPlusAmp phis 0 = 1 ∧

    (phis ≠ [] → 0 ≤ θ → θ ≤ 2 * Real.pi → ∃ (psis : List ℝ) (γ₀ γ₁ : ℝ),
      psis.length + 1 = phis.length ∧
      psis = lcHalfDiffs phis.reverse ∧
      lcPlusAmp phis θ = lcRepoAmp γ₀ γ₁ psis (Real.cos (θ/2)))

end Qatlib.Concepts.QspSimulation.Achievability
