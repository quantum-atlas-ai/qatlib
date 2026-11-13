/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeStat

/-!
# Source-form QSP necessity statement

This module packages the necessary properties of the amplitude `lcPlusAmp` into a proposition.
It requires a squared-modulus bound of one, normalization at angle zero, and a repository-word
representation for nonempty phase lists on the angle interval from zero to twice pi. This
formulation records the source convention used in the QSP construction of [LowChuang2017].

## Main statements

* `AchievableNecessitySourceForm` specifies the bound and normalization together with a phase
  list equal to `lcHalfDiffs phis.reverse` and satisfying the required length relation.

## References

* [Low and Chuang, 2017][LowChuang2017], *Optimal Hamiltonian Simulation by Quantum Signal
  Processing*.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.Achievability

/-- Specifies that `lcPlusAmp` has squared modulus at most one and equals one at zero angle. For
a nonempty phase list and angle between zero and twice pi, it also requires a representation
by `lcRepoAmp` at the cosine half-angle, using `lcHalfDiffs phis.reverse` and a phase list
whose length is one less than that of `phis`. -/
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
