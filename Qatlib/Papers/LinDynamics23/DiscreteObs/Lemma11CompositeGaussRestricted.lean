/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.CompositeGaussContracts

/-!
# Zero-time composite Gauss error budget

`lemma11CompositeGaussRestricted_zero_time_budget` evaluates the proposed restricted composite
Gauss error budget at time zero. A positive quadrature order makes the time-dependent power
vanish, so the full budget is zero. See [AnChildsLin2026] for the paper context.

## Main statements

* `lemma11CompositeGaussRestricted_zero_time_budget`: For positive quadrature order `Q`, the
  restricted composite Gauss error-budget expression is zero at time zero.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.Kernel

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

/-- For positive quadrature order `Q`, the restricted composite Gauss error-budget expression is
zero at time zero. -/
theorem lemma11CompositeGaussRestricted_zero_time_budget
    (β Λ : ℝ) (K Q M : ℕ) (hQ : 0 < Q) :
    (8 / (3 * highKernelC β)) * K *
      ((2 * K : ℝ) / M) ^ ((2 : ℝ) * Q) *
      (Real.exp 1 * (0 : ℝ) * Λ / 2) ^ ((2 : ℝ) * Q) = 0 := by
  have he : (2 : ℝ) * Q ≠ 0 := ne_of_gt (by positivity)
  simp [Real.zero_rpow he]

end Qatlib.Papers.LinDynamics23.DiscreteObs
