/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs

/-!
# Specification of polynomial readout convergence

This module states `PolyDepthConvergenceRate`, the existence of parameters attaining a target
polynomial readout error with an explicit amplitude-estimation size bound.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `PolyDepthConvergenceRate`: The proposition that every `0 < ε ≤ 1` has valid scale and
  precision parameters with readout window at most `ε` and amplitude-estimation size at most `8
  * π * ε ^ (-(2 * u + 3) / (2 * u + 2))`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout

/-- The proposition that every `0 < ε ≤ 1` has valid scale and precision parameters with readout
window at most `ε` and amplitude-estimation size at most `8 * π * ε ^ (-(2 * u + 3) / (2 * u
+ 2))`. -/
def PolyDepthConvergenceRate : Prop :=
  ∀ (u : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (c : ℝ) (M bits : ℕ), 0 < c ∧ c ≤ 1 ∧ 2 ≤ M ∧
      riskPolyReadoutWindow u c M bits ≤ ε ∧
      (M : ℝ) ≤ 8 * Real.pi * ε ^ (-((2*u+3 : ℝ)/(2*u+2)))

end Qatlib.Concepts.RiskEstimation.PolyReadout
