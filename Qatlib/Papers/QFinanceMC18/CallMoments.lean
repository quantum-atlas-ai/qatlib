/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QFinanceMC18.GbmDefs
import Qatlib.Foundations.StochasticCalc.LognormalPay.SecondMoment

/-!
# European call payoff moments

`payoff` applies the European call payoff to the geometric Brownian terminal stock model. The
module gives its discounted expectation, second moment, variance, and a variance upper bound
under the Gaussian terminal law. The mathematical context is [RebentrostGuptBromley2018].

## Main statements

* `native_call_price`: For positive maturity, initial stock, strike, and volatility, the
  discounted expected call payoff equals the stated Black–Scholes expression.
* `native_variance_bound`: For nonnegative maturity, initial stock, and strike, the call payoff
  variance is bounded by `bsVarianceBound`.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QFinanceMC18.CallMoments
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open Qatlib.Papers.QFinanceMC18.GbmDefs
open Qatlib.Foundations.StochasticCalc.LognormalPay

/-- The European call payoff with strike `K` evaluated at the terminal stock level determined by
`w`. -/
def payoff (S0 K r σ T w : ℝ) : ℝ := callPayoff K (stock S0 r σ T w)

/-- For positive maturity, initial stock, strike, and volatility, the discounted expected call
payoff equals the stated Black–Scholes expression. See [RebentrostGuptBromley2018]. -/
theorem native_call_price {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ) :
    Real.exp (-(r*T)) * (∫ w, payoff S0 K r σ T w ∂terminalLaw T hT.le) =
      S0 * normalCDF (d1 S0 K r σ T) - K * Real.exp (-(r*T)) * normalCDF (d2 S0 K r σ T) := by
  exact blackScholes_call_price hT hS0 hK hσ (by simp [terminalLaw])

/-- For positive maturity, initial stock, strike, and volatility, the undiscounted call payoff
second moment equals the stated expression in `d1`, `d2`, and `d3`. See
[RebentrostGuptBromley2018]. -/
theorem native_second_moment {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ) :
    (∫ w, payoff S0 K r σ T w ^ 2 ∂terminalLaw T hT.le) =
      S0 ^ 2 * Real.exp ((2*r+σ^2)*T) * normalCDF (d3 S0 K r σ T) -
        2*K*S0*Real.exp (r*T) * normalCDF (d1 S0 K r σ T) + K^2 * normalCDF (d2 S0 K r σ T) := by
  exact call_second_moment hT hS0 hK hσ (by simp [terminalLaw])

/-- For positive maturity, initial stock, strike, and volatility, the call payoff variance
equals its explicit second moment minus the square of its explicit mean. See
[RebentrostGuptBromley2018]. -/
theorem native_variance {S0 K r σ T : ℝ}
    (hT : 0 < T) (hS0 : 0 < S0) (hK : 0 < K) (hσ : 0 < σ) :
    variance (payoff S0 K r σ T) (terminalLaw T hT.le) =
      S0 ^ 2 * Real.exp ((2*r+σ^2)*T) * normalCDF (d3 S0 K r σ T) -
        2*K*S0*Real.exp (r*T) * normalCDF (d1 S0 K r σ T) + K^2 * normalCDF (d2 S0 K r σ T) -
        (S0*Real.exp (r*T)*normalCDF (d1 S0 K r σ T) - K*normalCDF (d2 S0 K r σ T))^2 := by
  exact call_variance_exact hT hS0 hK hσ (by simp [terminalLaw])

/-- For nonnegative maturity, initial stock, and strike, the call payoff variance is bounded by
`bsVarianceBound`. See [RebentrostGuptBromley2018]. -/
theorem native_variance_bound {S0 K r σ T : ℝ}
    (hT : 0 ≤ T) (hS0 : 0 ≤ S0) (hK : 0 ≤ K) :
    variance (payoff S0 K r σ T) (terminalLaw T hT) ≤ bsVarianceBound S0 r σ T := by
  exact callPayoff_variance_le hT hS0 hK (by simp [terminalLaw])

end
end Qatlib.Papers.QFinanceMC18.CallMoments
