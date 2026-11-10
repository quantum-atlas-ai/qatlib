/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.WordModel

def Equation1WordBridge : Prop :=
  ∀ (phis : List ℝ) (θ : ℝ),

    (phis ≠ [] → 0 ≤ θ → θ ≤ 2 * Real.pi →
      ∃ (psis : List ℝ) (γ₀ γ₁ : ℝ),
        psis.length + 1 = phis.length ∧
        (∀ hp : phis ≠ [], γ₀ = -(phis.getLast hp) / 2 ∧ γ₁ = phis.head hp / 2) ∧
        psis = lcHalfDiffs phis.reverse ∧
        lcWord phis θ = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ₀ * lcQspTilde psis (Real.cos (θ/2)) *
          lcSignalStep θ * Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation γ₁) ∧

    (0 ≤ θ → θ ≤ 2 * Real.pi →
      lcSignalStep θ = (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.SignalMatrix (Real.cos (θ/2))).conjTranspose) ∧

    lcWord phis 0 = 1 ∧

    lcWord phis θ ∈ Matrix.unitaryGroup (Fin 2) ℂ

end Qatlib.Concepts.QspSimulation.WordModel
