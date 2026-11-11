/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# System-size exponents for low-energy product formulas

This module compares the real exponent `presentWorkExponent` with the general product-formula
and previous low-energy exponents from [HejaziZiniArrazola2024]. It proves both exponent
inequalities for positive order and the resulting comparisons of powers of a system size greater
than one.

## Main statements

* `presentWorkExponent_rational`: Rewrites the new exponent as `(p + 1) / (p ^ 2 + 3 * p + 1)`.
* `source_first_three_exponents`: Computes the first three exponents as `2/5`, `3/11`, and
  `4/19`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false

namespace Qatlib.Papers.LowEnergyProd24.SizeScaling

/-- The system-size exponent `1 / (p + 1 + p / (p + 1))` for the improved low-energy
product-formula estimate [HejaziZiniArrazola2024]. -/
noncomputable def presentWorkExponent (p : ℝ) : ℝ := 1 / (p + 1 + p / (p + 1))

/-- The general product-formula comparison exponent `1 / p`. -/
noncomputable def generalExponent (p : ℝ) : ℝ := 1 / p

/-- The previous low-energy comparison exponent `1 / 2 + 1 / (4 * p + 2)`. -/
noncomputable def previousLowEnergyExponent (p : ℝ) : ℝ := 1 / 2 + 1 / (4 * p + 2)

/-- For every positive real order `p`, the improved system-size exponent is strictly smaller
than `1 / p`. -/
theorem presentWorkExponent_lt_general (p : ℝ) (hp : 0 < p) :
    presentWorkExponent p < generalExponent p := by
  unfold presentWorkExponent generalExponent
  have h1 : (0 : ℝ) < p + 1 := by linarith
  have h2 : (0 : ℝ) < p + 1 + p / (p + 1) := by positivity
  rw [one_div, one_div]
  rw [inv_lt_inv₀ h2 hp]

  have : 0 < p / (p + 1) := div_pos hp h1
  linarith

/-- For every positive real order `p`, the improved system-size exponent is strictly smaller
than the previous low-energy exponent. -/
theorem presentWorkExponent_lt_previous (p : ℝ) (hp : 0 < p) :
    presentWorkExponent p < previousLowEnergyExponent p := by
  unfold presentWorkExponent previousLowEnergyExponent
  have h1 : (0 : ℝ) < p + 1 := by linarith
  have hden1 : (0 : ℝ) < p ^ 2 + 3 * p + 1 := by nlinarith [hp, h1]
  have hden2 : (0 : ℝ) < 2 * p + 1 := by linarith

  have hlhs : 1 / (p + 1 + p / (p + 1)) = (p + 1) / (p ^ 2 + 3 * p + 1) := by
    field_simp
    ring
  have hrhs : 1 / 2 + 1 / (4 * p + 2) = (p + 1) / (2 * p + 1) := by
    field_simp
    ring
  rw [hlhs, hrhs]
  rw [div_lt_div_iff₀ hden1 hden2]
  nlinarith [hp, h1]

/-- For `N > 1` and `p > 0`, the power of `N` with the improved exponent is no larger than
either comparison power. -/
theorem improvedSystemSizeScaling (N p : ℝ) (hN : 1 < N) (hp : 0 < p) :
    N ^ presentWorkExponent p ≤ N ^ generalExponent p ∧
      N ^ presentWorkExponent p ≤ N ^ previousLowEnergyExponent p := by
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le hN.le
      (le_of_lt (presentWorkExponent_lt_general p hp))
  · exact Real.rpow_le_rpow_of_exponent_le hN.le
      (le_of_lt (presentWorkExponent_lt_previous p hp))

/-- For each `N > 1`, both comparisons of system-size powers hold for every positive real order
[HejaziZiniArrazola2024]. -/
theorem improvedSystemSizeScaling_allOrders (N : ℝ) (hN : 1 < N) :
    ∀ p : ℝ, 0 < p →
      N ^ presentWorkExponent p ≤ N ^ generalExponent p ∧
        N ^ presentWorkExponent p ≤ N ^ previousLowEnergyExponent p := by
  intro p hp
  exact improvedSystemSizeScaling N p hN hp

/-- For positive `p`, the improved exponent equals `(p + 1) / (p ^ 2 + 3 * p + 1)`. -/
theorem presentWorkExponent_rational (p : ℝ) (hp : 0 < p) :
    presentWorkExponent p = (p+1)/(p^2+3*p+1) := by
  unfold presentWorkExponent
  field_simp
  ring

/-- The improved system-size exponents at orders one, two, and three are respectively `2/5`,
`3/11`, and `4/19` [HejaziZiniArrazola2024]. -/
theorem source_first_three_exponents :
    presentWorkExponent 1 = (2/5 : ℝ) ∧ presentWorkExponent 2 = (3/11 : ℝ) ∧
      presentWorkExponent 3 = (4/19 : ℝ) := by
  norm_num [presentWorkExponent]

end Qatlib.Papers.LowEnergyProd24.SizeScaling
