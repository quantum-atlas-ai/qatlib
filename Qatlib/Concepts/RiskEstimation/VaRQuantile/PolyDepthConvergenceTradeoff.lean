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
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile

open scoped Classical BigOperators

def PolyDepthConvergenceTradeoff : Prop :=
  ∀ (u : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (c : ℝ) (M angleBits bits : ℕ), 0 < c ∧ c ≤ 1 ∧ 2 ≤ M ∧
      (Real.pi/(M : ℝ) + Real.pi^2/(M : ℝ)^2
        + (1/2 : ℝ)^bits + 2*(1/2 : ℝ)^angleBits)/c
        + riskArcsinTail u * c^(2*u+2)/2 ≤ ε ∧
      (M : ℝ) ≤ 8 * Real.pi * ε ^ (-((2*u+3 : ℝ)/(2*u+2)))

end Qatlib.Concepts.RiskEstimation.VaRQuantile
