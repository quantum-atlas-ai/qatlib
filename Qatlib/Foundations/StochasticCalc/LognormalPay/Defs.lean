/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lognormal terminal levels and call payoff parameters

This module defines the exponential terminal level `terminalLevel`, the standard normal
cumulative distribution function `normalCDF`, and the call payoff `callPayoff`. The parameters
`d1`, `d2`, and `d3` are used in formulas for Gaussian call expectations and second moments.

The mathematical background is discussed in [RebentrostGuptBromley2018].

## Main statements

* `terminalLevel`: the exponential model with drift correction by half the squared volatility.
* `d1`, `d2`, `d3`: normal CDF arguments for the call moment formulas.
* `callPayoff`: the positive part of the terminal level minus the strike.

## References

* [Rebentrost et al., 2018][RebentrostGuptBromley2018]
-/

namespace Qatlib.Foundations.StochasticCalc.LognormalPay

set_option autoImplicit false

noncomputable section

open MeasureTheory

/-- The exponential terminal level `S0 * exp (σ * W + (α - σ ^ 2 / 2) * t)`. -/
def terminalLevel (S0 α σ : ℝ) (W t : ℝ) : ℝ :=
  S0 * Real.exp (σ * W + (α - σ ^ 2 / 2) * t)

/-- The standard normal cumulative distribution function, defined by its density integral over
`Set.Iic x`. -/
def normalCDF (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ y in Set.Iic x, Real.exp (-(y ^ 2) / 2)

/-- The Black-Scholes parameter `(log (S0 / K) + (r + σ ^ 2 / 2) * T) / (σ * sqrt T)`. -/
def d1 (S0 K r σ T : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt T)) * (Real.log (S0 / K) + (r + σ ^ 2 / 2) * T)

/-- The Black-Scholes parameter `d1 - σ * sqrt T`. -/
def d2 (S0 K r σ T : ℝ) : ℝ := d1 S0 K r σ T - σ * Real.sqrt T

/-- The second-moment parameter `(log (S0 / K) + (r + 3 * σ ^ 2 / 2) * T) / (σ * sqrt T)`. -/
def d3 (S0 K r σ T : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt T)) * (Real.log (S0 / K) + (r + 3 * σ ^ 2 / 2) * T)

/-- The call payoff `max (S - K) 0` at level `S` and strike `K`. -/
def callPayoff (K S : ℝ) : ℝ := max (S - K) 0

end

end Qatlib.Foundations.StochasticCalc.LognormalPay
