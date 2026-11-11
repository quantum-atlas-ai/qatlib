/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile

/-!
# Statement of stationarity for the restart profile

Defines `Section3RestartStationaritySubgoal`, characterizing stationary points of
`restartExpectedIterations`. For a search angle in `(0, π/2)` and nonzero success amplitude, the
derivative vanishes exactly when `Real.tan ((2 * j₀ + 1) * θ) = 4 * θ * j₀`. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Section3RestartStationaritySubgoal`: The proposition that for `0 < θ < Real.pi / 2` and
  nonzero `Real.sin ((2 * j₀ + 1) * θ)`, the restart-profile derivative vanishes exactly when
  `Real.tan ((2 * j₀ + 1) * θ) = 4 * θ * j₀`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

/-- The proposition that for `0 < θ < Real.pi / 2` and nonzero `Real.sin ((2 * j₀ + 1) * θ)`,
the restart-profile derivative vanishes exactly when `Real.tan ((2 * j₀ + 1) * θ) = 4 * θ *
j₀`. -/
def Section3RestartStationaritySubgoal : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → ∀ j₀ : ℝ,
    Real.sin ((2 * j₀ + 1) * θ) ≠ 0 →
    (deriv (restartExpectedIterations θ) j₀ = 0 ↔
      Real.tan ((2 * j₀ + 1) * θ) = 4 * θ * j₀)

end Qatlib.Concepts.SearchStopping.RestartLaw
