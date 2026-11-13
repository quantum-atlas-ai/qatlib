/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs

/-!
# Specification of polynomial rotation bias

This module defines `PolyRotationTaylorBias`, the uniform squared-sine payoff error bound for a
truncated polynomial angle on payoffs and scales in the specified intervals.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `PolyRotationTaylorBias`: The proposition that, for `0 < c ≤ 1` and `0 ≤ y ≤ 1`, the
  squared-sine polynomial payoff differs from `c * (y - 1 / 2) + 1 / 2` by at most
  `riskArcsinTail u * c ^ (2 * u + 3) / 2`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

/-- The proposition that, for `0 < c ≤ 1` and `0 ≤ y ≤ 1`, the squared-sine polynomial payoff
differs from `c * (y - 1 / 2) + 1 / 2` by at most `riskArcsinTail u * c ^ (2 * u + 3) / 2`. -/
def PolyRotationTaylorBias : Prop :=
  ∀ (u : ℕ) (c y : ℝ), 0 < c → c ≤ 1 → 0 ≤ y → y ≤ 1 →
    |Real.sin (c*riskSinTaylor u c y + Real.pi/4)^2 - (c*(y-1/2)+1/2)|
      ≤ riskArcsinTail u*c^(2*u+3)/2

end Qatlib.Concepts.RiskEstimation.PolyRotation
