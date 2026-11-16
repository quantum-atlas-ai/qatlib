/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section


set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.FullSimulation

/-- The legacy all-positive-input domain includes a zero polylog factor at epsilon=exp 2. -/
theorem budget_factor_zero (p : ℝ) (hp : 0 < p) :
    (Real.log ((1 : ℝ) * 1 * 1 / Real.exp 2) + 2) ^ p = 0 := by
  rw [show (1 : ℝ) * 1 * 1 / Real.exp 2 = Real.exp (-2) by
    simp [Real.exp_neg]]
  rw [Real.log_exp]
  norm_num
  exact Real.zero_rpow (ne_of_gt hp)

/-- The literal Theorem 1 bound cannot dominate a positive count at that allowed input. -/
theorem budget_domain_refuted (N C p : ℝ) (hN : 0 < N) (hp : 0 < p) :
    ¬ N ≤ C * (1 : ℝ) ^ 2 * 1 * 1 *
      Real.exp (1.6 * Real.sqrt (Real.log ((1 : ℝ) * 1 * 1 / Real.exp 2))) *
      (Real.log ((1 : ℝ) * 1 * 1 / Real.exp 2) + 2) ^ p := by
  rw [budget_factor_zero p hp, mul_zero]
  exact not_le.mpr hN

end Qatlib.Papers.HamLCUSim12.FullSimulation
