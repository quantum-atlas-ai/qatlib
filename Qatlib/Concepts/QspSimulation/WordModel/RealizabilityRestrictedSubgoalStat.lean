/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

/-!
# Specification of a quadratic QSP realization

`RealizabilityRestrictedSubgoal` asks for a phase list of length two whose upper-left QSP
response equals 2x² − 1 on the real unit interval. This provides a concrete polynomial
realization target. Background and related constructions are discussed in
[GilyenSuLowWiebe2019].

## Main statements

* `RealizabilityRestrictedSubgoal`: the existential quadratic realization property.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.QspSimulation.WordModel

/-- States that a phase list of length two realizes the upper-left QSP response 2x² − 1 on [−1,
1]. -/
def RealizabilityRestrictedSubgoal : Prop :=
  ∃ (phis : List ℝ), phis.length = 2 ∧
    ∀ (x : ℝ), -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 0 = ((2 * x ^ 2 - 1 : ℝ) : ℂ)

end Qatlib.Concepts.QspSimulation.WordModel
