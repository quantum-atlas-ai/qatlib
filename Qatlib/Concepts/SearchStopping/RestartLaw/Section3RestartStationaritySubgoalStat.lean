/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.RestartProfile
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

def Section3RestartStationaritySubgoal : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → ∀ j₀ : ℝ,
    Real.sin ((2 * j₀ + 1) * θ) ≠ 0 →
    (deriv (restartExpectedIterations θ) j₀ = 0 ↔
      Real.tan ((2 * j₀ + 1) * θ) = 4 * θ * j₀)

end Qatlib.Concepts.SearchStopping.RestartLaw
