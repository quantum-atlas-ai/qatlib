/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductFactorialLowerBoundStat
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# An explicit factorial lower bound

This module proves `multiproductFactorialLowerBound`, supplying the analytic factorial estimate
used in the coefficient analysis. It establishes √(2πn) n^n exp(−n − 1/13) ≤ n! for every
natural number n. See [ChildsWiebe2012] for the multiproduct and linear-combination simulation
framework.

## Main statements

* `multiproductFactorialLowerBound`: Establishes `MultiproductFactorialLowerBound`, the
  inequality √(2πn) n^n exp(−n − 1 / 13) ≤ n! for every natural number n.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Establishes `MultiproductFactorialLowerBound`, the inequality √(2πn) n^n exp(−n − 1 / 13) ≤
n! for every natural number n. See [ChildsWiebe2012]. -/
theorem multiproductFactorialLowerBound : MultiproductFactorialLowerBound := by
  intro n
  have hs := Stirling.le_factorial_stirling n
  have he : Real.exp (-((n : ℝ)+1/13)) ≤ Real.exp (-(n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hid : ((n : ℝ)/Real.exp 1)^n = (n : ℝ)^n*Real.exp (-(n : ℝ)) := by
    rw [div_pow, Real.exp_neg]
    have hp : (Real.exp 1)^n = Real.exp (n : ℝ) := by
      rw [← Real.exp_nat_mul]
      simp
    rw [hp]
    rfl
  rw [hid] at hs
  rw [Real.rpow_natCast]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans (by
    simpa only [mul_assoc] using hs)

end Qatlib.Papers.HamLCUSim12.Multiproduct
