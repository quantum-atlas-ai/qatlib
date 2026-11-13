/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs

/-!
# Specification of the arcsine payoff target

This module defines `PolyRotationTarget`, the identity converting the exact scaled arcsine angle
into an affine payoff probability.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `PolyRotationTarget`: The proposition that `sin (c * riskArcsineTarget c y + π / 4)² = c * (y
  - 1 / 2) + 1 / 2` for `0 < c ≤ 1` and `0 ≤ y ≤ 1`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

/-- The proposition that `sin (c * riskArcsineTarget c y + π / 4)² = c * (y - 1 / 2) + 1 / 2`
for `0 < c ≤ 1` and `0 ≤ y ≤ 1`. -/
def PolyRotationTarget : Prop :=
  ∀ (c y : ℝ), 0 < c → c ≤ 1 → 0 ≤ y → y ≤ 1 →
    Real.sin (c*riskArcsineTarget c y + Real.pi/4)^2 = c*(y-1/2)+1/2

end Qatlib.Concepts.RiskEstimation.PolyRotation
