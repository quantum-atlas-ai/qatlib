/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.DiscountedMean

/-!
# Gaussian terminal law for geometric Brownian stock

`terminalLaw` is the centered Gaussian law of variance `T`, and `stock` is the corresponding
geometric Brownian terminal level. The expectation identities give mean growth by `exp (r*T)`
and recovery of the initial stock level after discounting. The mathematical context is
[RebentrostGuptBromley2018].

## Main statements

* `native_stock_mean`: For nonnegative maturity, the mean terminal stock level is `S0 * exp
  (r*T)`.
* `native_discounted_mean`: For nonnegative maturity, discounting the expected terminal stock
  level by `exp (-(r*T))` gives `S0`.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QFinanceMC18.GbmDefs
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open Qatlib.Foundations.StochasticCalc.LognormalPay

/-- The centered real Gaussian measure with variance equal to the nonnegative maturity `T`. -/
def terminalLaw (T : ℝ) (hT : 0 ≤ T) : Measure ℝ := gaussianReal 0 ⟨T, hT⟩

instance terminalLaw_probability (T : ℝ) (hT : 0 ≤ T) : IsProbabilityMeasure (terminalLaw T hT) :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 ⟨T, hT⟩))

/-- The geometric Brownian terminal stock level for initial stock `S0`, rate `r`, volatility
`σ`, maturity `T`, and terminal Gaussian value `w`. -/
def stock (S0 r σ T w : ℝ) : ℝ := terminalLevel S0 r σ w T

/-- For nonnegative maturity, the mean terminal stock level is `S0 * exp (r*T)`. See
[RebentrostGuptBromley2018]. -/
theorem native_stock_mean (S0 r σ T : ℝ) (hT : 0 ≤ T) :
    (∫ w, stock S0 r σ T w ∂terminalLaw T hT) = S0 * Real.exp (r*T) := by
  exact terminalLevel_expectation hT (by simp [terminalLaw])

/-- For nonnegative maturity, discounting the expected terminal stock level by `exp (-(r*T))`
gives `S0`. See [RebentrostGuptBromley2018]. -/
theorem native_discounted_mean (S0 r σ T : ℝ) (hT : 0 ≤ T) :
    Real.exp (-(r*T)) * (∫ w, stock S0 r σ T w ∂terminalLaw T hT) = S0 := by
  exact discounted_stock_expectation hT (by simp [terminalLaw])

end
end Qatlib.Papers.QFinanceMC18.GbmDefs
