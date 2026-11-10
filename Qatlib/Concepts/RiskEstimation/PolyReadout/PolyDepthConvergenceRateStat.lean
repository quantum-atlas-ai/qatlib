/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout

def PolyDepthConvergenceRate : Prop :=
  ∀ (u : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (c : ℝ) (M bits : ℕ), 0 < c ∧ c ≤ 1 ∧ 2 ≤ M ∧
      riskPolyReadoutWindow u c M bits ≤ ε ∧
      (M : ℝ) ≤ 8 * Real.pi * ε ^ (-((2*u+3 : ℝ)/(2*u+2)))

end Qatlib.Concepts.RiskEstimation.PolyReadout
