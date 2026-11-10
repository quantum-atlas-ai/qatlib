/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false

namespace Qatlib.Papers.LowEnergyProd24.SizeScaling

noncomputable def presentWorkExponent (p : ℝ) : ℝ := 1 / (p + 1 + p / (p + 1))

noncomputable def generalExponent (p : ℝ) : ℝ := 1 / p

noncomputable def previousLowEnergyExponent (p : ℝ) : ℝ := 1 / 2 + 1 / (4 * p + 2)

theorem presentWorkExponent_lt_general (p : ℝ) (hp : 0 < p) :
    presentWorkExponent p < generalExponent p := by
  unfold presentWorkExponent generalExponent
  have h1 : (0 : ℝ) < p + 1 := by linarith
  have h2 : (0 : ℝ) < p + 1 + p / (p + 1) := by positivity
  rw [one_div, one_div]
  rw [inv_lt_inv₀ h2 hp]

  have : 0 < p / (p + 1) := div_pos hp h1
  linarith

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

theorem improvedSystemSizeScaling (N p : ℝ) (hN : 1 < N) (hp : 0 < p) :
    N ^ presentWorkExponent p ≤ N ^ generalExponent p ∧
      N ^ presentWorkExponent p ≤ N ^ previousLowEnergyExponent p := by
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le hN.le
      (le_of_lt (presentWorkExponent_lt_general p hp))
  · exact Real.rpow_le_rpow_of_exponent_le hN.le
      (le_of_lt (presentWorkExponent_lt_previous p hp))

theorem improvedSystemSizeScaling_allOrders (N : ℝ) (hN : 1 < N) :
    ∀ p : ℝ, 0 < p →
      N ^ presentWorkExponent p ≤ N ^ generalExponent p ∧
        N ^ presentWorkExponent p ≤ N ^ previousLowEnergyExponent p := by
  intro p hp
  exact improvedSystemSizeScaling N p hN hp

theorem presentWorkExponent_rational (p : ℝ) (hp : 0 < p) :
    presentWorkExponent p = (p+1)/(p^2+3*p+1) := by
  unfold presentWorkExponent
  field_simp
  ring

theorem source_first_three_exponents :
    presentWorkExponent 1 = (2/5 : ℝ) ∧ presentWorkExponent 2 = (3/11 : ℝ) ∧
      presentWorkExponent 3 = (4/19 : ℝ) := by
  norm_num [presentWorkExponent]

end Qatlib.Papers.LowEnergyProd24.SizeScaling
