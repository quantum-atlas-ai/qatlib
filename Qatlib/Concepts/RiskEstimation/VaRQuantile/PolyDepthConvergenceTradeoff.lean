/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs

/-!
# Polynomial risk readout precision tradeoff

`PolyDepthConvergenceTradeoff` specifies the existence of a scale, amplitude-estimation size,
and decoding precisions meeting a prescribed positive error tolerance. The error combines
readout terms with `riskArcsinTail`, and the size bound depends explicitly on the expansion
order. This describes a precision tradeoff for the payoff readout considered in
[WoernerEgger2019].

## Main statements

* `PolyDepthConvergenceTradeoff`: achievable total error and an expansion-order-dependent upper
  bound on the amplitude-estimation size.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PolyReadout

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile

open scoped Classical BigOperators

/-- The specification that each positive tolerance at most one can be met by suitable scaling,
amplitude-estimation size, and bit precisions. The size is bounded by `8 * π *
ε^(-(2*u+3)/(2*u+2))` while the combined readout and arcsine-tail error is at most `ε`. -/
def PolyDepthConvergenceTradeoff : Prop :=
  ∀ (u : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∃ (c : ℝ) (M angleBits bits : ℕ), 0 < c ∧ c ≤ 1 ∧ 2 ≤ M ∧
      (Real.pi/(M : ℝ) + Real.pi^2/(M : ℝ)^2
        + (1/2 : ℝ)^bits + 2*(1/2 : ℝ)^angleBits)/c
        + riskArcsinTail u * c^(2*u+2)/2 ≤ ε ∧
      (M : ℝ) ≤ 8 * Real.pi * ε ^ (-((2*u+3 : ℝ)/(2*u+2)))

end Qatlib.Concepts.RiskEstimation.VaRQuantile
