/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StochasticCalc.LognormalPay.DiscountedMean
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QFinanceMC18.GbmDefs
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open Qatlib.Foundations.StochasticCalc.LognormalPay

def terminalLaw (T : ℝ) (hT : 0 ≤ T) : Measure ℝ := gaussianReal 0 ⟨T, hT⟩

instance terminalLaw_probability (T : ℝ) (hT : 0 ≤ T) : IsProbabilityMeasure (terminalLaw T hT) :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 ⟨T, hT⟩))

def stock (S0 r σ T w : ℝ) : ℝ := terminalLevel S0 r σ w T

theorem native_stock_mean (S0 r σ T : ℝ) (hT : 0 ≤ T) :
    (∫ w, stock S0 r σ T w ∂terminalLaw T hT) = S0 * Real.exp (r*T) := by
  exact terminalLevel_expectation hT (by simp [terminalLaw])

theorem native_discounted_mean (S0 r σ T : ℝ) (hT : 0 ≤ T) :
    Real.exp (-(r*T)) * (∫ w, stock S0 r σ T w ∂terminalLaw T hT) = S0 := by
  exact discounted_stock_expectation hT (by simp [terminalLaw])

end
end Qatlib.Papers.QFinanceMC18.GbmDefs
