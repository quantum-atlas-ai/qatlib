/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.TerminalMean

/-!
# Discounted mean of a lognormal terminal level

`discounted_stock_expectation` shows that discounting the mean of `terminalLevel` at its drift
rate recovers the initial level. The result assumes a centered Gaussian input of variance `T ≥
0` and almost-everywhere measurability of that input.

The mathematical background is discussed in [RebentrostGuptBromley2018].

## Main statements

* `discounted_stock_expectation`: the discounted terminal expectation equals `S0`.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.StochasticCalc.LognormalPay

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}

/-- If the input has centered Gaussian law with variance `T ≥ 0`, the expectation of
`terminalLevel S0 r σ` discounted by `exp (-r * T)` equals `S0`. -/
theorem discounted_stock_expectation
    [IsProbabilityMeasure Q] {W : Ω → ℝ} {S0 r σ T : ℝ} (hT : 0 ≤ T)
    (hW : Q.map W = gaussianReal 0 ⟨T, hT⟩)
    (hWm : AEMeasurable W Q := by first | assumption | fun_prop) :
    Real.exp (-(r * T)) * ∫ ω, terminalLevel S0 r σ (W ω) T ∂Q = S0 := by
  rw [terminalLevel_expectation hT hW hWm]
  calc Real.exp (-(r * T)) * (S0 * Real.exp (r * T))
      = S0 * (Real.exp (-(r * T)) * Real.exp (r * T)) := by ring
    _ = S0 * Real.exp (-(r * T) + r * T) := by rw [← Real.exp_add]
    _ = S0 := by
          rw [show -(r * T) + r * T = 0 by ring, Real.exp_zero, mul_one]

end

end Qatlib.Foundations.StochasticCalc.LognormalPay
