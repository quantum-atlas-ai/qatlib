/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Qatlib.Foundations.StochasticCalc.LognormalPay

set_option autoImplicit false

noncomputable section

open MeasureTheory

def terminalLevel (S0 α σ : ℝ) (W t : ℝ) : ℝ :=
  S0 * Real.exp (σ * W + (α - σ ^ 2 / 2) * t)

def normalCDF (x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ y in Set.Iic x, Real.exp (-(y ^ 2) / 2)

def d1 (S0 K r σ T : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt T)) * (Real.log (S0 / K) + (r + σ ^ 2 / 2) * T)

def d2 (S0 K r σ T : ℝ) : ℝ := d1 S0 K r σ T - σ * Real.sqrt T

def d3 (S0 K r σ T : ℝ) : ℝ :=
  (1 / (σ * Real.sqrt T)) * (Real.log (S0 / K) + (r + 3 * σ ^ 2 / 2) * T)

def callPayoff (K S : ℝ) : ℝ := max (S - K) 0

end

end Qatlib.Foundations.StochasticCalc.LognormalPay
