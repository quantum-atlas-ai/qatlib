/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.TrotterCost
import Qatlib.Papers.QChemistry14.ScalarModels.AveragingCost

/-!
# Combined scalar locality cost bounds

This module combines the scalar simulation and averaging inequalities for nonnegative
coefficient bounds and positive precision. The theorem gives explicit upper bounds proportional
to `M⁵ * log M / ε^(3/2)` and `M⁶ / ε²` for the displayed cost expressions. See
[McCleanEtAl2014].

## Main statements

* `main_result_locality_improves_scaling`: For `M ≥ 1`, nonnegative `β` and `h`, and positive
  `ε`, the displayed simulation and averaging cost expressions are bounded respectively by `2 *
  (β + h)^(3/2) * M⁵ * log M / ε^(3/2)` and `2 * (β + h)² * M⁶ / ε²`.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.MainResult

open Qatlib.Papers.QChemistry14.ScalarModels.TrotterCost
open Qatlib.Papers.QChemistry14.ScalarModels.AveragingCost

/-- For `M ≥ 1`, nonnegative `β` and `h`, and positive `ε`, the displayed simulation and
averaging cost expressions are bounded respectively by `2 * (β + h)^(3/2) * M⁵ * log M /
ε^(3/2)` and `2 * (β + h)² * M⁶ / ε²`. See [McCleanEtAl2014]. -/
theorem main_result_locality_improves_scaling
    (β h M ε : ℝ) (hM : 1 ≤ M) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hε : 0 < ε) :
    ((β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ (3 / 2 : ℝ) * ((M + M ^ 2) * Real.log M)
        / ε ^ (3 / 2 : ℝ)
      ≤ (2 * (β + h) ^ (3 / 2 : ℝ)) * M ^ 5 * Real.log M / ε ^ (3 / 2 : ℝ))
    ∧ ((M + M ^ 2) * (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ 2 / ε ^ 2
      ≤ (2 * (β + h) ^ 2) * M ^ 6 / ε ^ 2) :=
  ⟨trotter_bigO β h M ε hM hβ hh hε,
   averaging_bigO β h M ε hM hβ hh hε⟩

end Qatlib.Papers.QChemistry14.ScalarModels.MainResult
