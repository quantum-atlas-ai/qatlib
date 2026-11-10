/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation

def PolyRotationTaylorBias : Prop :=
  ∀ (u : ℕ) (c y : ℝ), 0 < c → c ≤ 1 → 0 ≤ y → y ≤ 1 →
    |Real.sin (c*riskSinTaylor u c y + Real.pi/4)^2 - (c*(y-1/2)+1/2)|
      ≤ riskArcsinTail u*c^(2*u+3)/2

end Qatlib.Concepts.RiskEstimation.PolyRotation
