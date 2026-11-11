/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17Support

/-!
# Specification of the axis-rotation word bridge

`Equation1WordBridge` specifies the conversion of a nonempty axis-rotation word into a QSP word
with reversed phase half-differences and explicit endpoint rotations. It also records the
signal-matrix identity on the angle interval from 0 to 2π, the zero-angle identity, and
unitarity. Background and related constructions are discussed in [LowChuang2017].

## Main statements

* `Equation1WordBridge`: the complete word-convention bridge property.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QspSimulation.WordModel

/-- Specifies the factorization of nonempty axis-rotation words using reversed phase
half-differences and endpoint rotations for angles in [0, 2π]. It also requires the
adjoint-signal identity on that interval, the zero-angle word identity, and unitarity for
all angles. -/
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
