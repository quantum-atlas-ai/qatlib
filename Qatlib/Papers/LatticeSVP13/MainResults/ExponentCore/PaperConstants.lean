/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore.AsymptoticExponent

set_option backward.isDefEq.respectTransparency false

/-!
# Exponent constants of LatticeSVP13

Laarhoven--Mosca--van de Pol, fixed arXiv:1301.6176v1.

This file records, verbatim, the exponent functions that the paper introduces in
Equations (1)–(7), together with the concrete numerical bounds that Theorems 1
and 2 are evaluated at.  Nothing here is a hypothesis: every numerical bound is
proved from Mathlib's `Real.log_two_gt_d9` and a truncated Taylor series for
`exp` (see `ExponentCore.logb_two_le_of_taylor`).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore

/-! ## The exponent functions of Equations (1)–(7) -/

/-- Equation (1): the Nguyen--Vidick list-size exponent
`c_h(γ) = -log₂ γ - ½ log₂(1 - γ²/4)`. -/
def cH (γ : ℝ) : ℝ := -Real.logb 2 γ - (1 / 2) * Real.logb 2 (1 - γ ^ 2 / 4)

/-- Equation (2): `c_b = log₂ R + 0.401`. -/
def cB (R : ℝ) : ℝ := Real.logb 2 R + 0.401

/-- Equation (3): `c_t = ½ log₂(1 + ξ/(R - 2ξ)) + 0.401`. -/
def cT (ξ R : ℝ) : ℝ := (1 / 2) * Real.logb 2 (1 + ξ / (R - 2 * ξ)) + 0.401

/-- Equation (4): `c_g = ½ log₂(4ξ²/(4ξ² - 1))`. -/
def cG (ξ : ℝ) : ℝ := (1 / 2) * Real.logb 2 (4 * ξ ^ 2 / (4 * ξ ^ 2 - 1))

/-- Equation (7): the quantum time exponent
`t̃ = max(c_g + 3c_t/2, c_g + c_b/2 + c_t/2, c_g + c_b/2)`. -/
def quantumTimeExponent (cb ct cg : ℝ) : ℝ :=
  max (max (cg + 3 * ct / 2) (cg + cb / 2 + ct / 2)) (cg + cb / 2)

/-- Equation (7): the quantum space exponent
`s̃ = max(c_t, c_g + c_b/2)`. -/
def quantumSpaceExponent (cb ct cg : ℝ) : ℝ := max ct (cg + cb / 2)

/-! ## Concrete numerical bounds -/

/-- `log₂(4/3) ≤ 0.416`.

Obtained from `logb_two_le_of_taylor` with the four-term lower bound
`1 + z + z²/2 + z³/6 ≤ exp z` at `z = 0.416 · 0.6931471803`.  This is the single
inequality behind both exponents of Theorem 1, since
`c_h(1) = ½ log₂(4/3)`. -/
theorem logb_two_four_thirds_le : Real.logb 2 (4 / 3) ≤ 0.416 := by
  apply logb_two_le_of_taylor (x := 4 / 3) (y := 0.416)
    (z := 0.416 * 0.6931471803) (n := 4)
  · norm_num
  · norm_num
  · nlinarith [Real.log_two_gt_d9]
  · norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- `c_g(0.9086) ≤ 0.27` at the optimal point of Theorem 2. -/
theorem cG_09086_le : cG 0.9086 ≤ 0.27 := by
  have hlog : Real.logb 2 (4 * (0.9086 : ℝ) ^ 2 / (4 * (0.9086 : ℝ) ^ 2 - 1)) ≤ 0.54 := by
    apply logb_two_le_of_taylor (x := 4 * (0.9086 : ℝ) ^ 2 / (4 * (0.9086 : ℝ) ^ 2 - 1))
      (y := 0.54) (z := 0.54 * 0.6931471803) (n := 5)
    · norm_num
    · norm_num
    · nlinarith [Real.log_two_gt_d9]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold cG
  nlinarith [hlog]

/-- `c_t(0.9086, 3.1376) ≤ 0.80`. -/
theorem cT_09086_31376_le : cT 0.9086 3.1376 ≤ 0.80 := by
  have hlog : Real.logb 2 (1 + (0.9086 : ℝ) / (3.1376 - 2 * 0.9086)) ≤ 0.798 := by
    apply logb_two_le_of_taylor (x := 1 + (0.9086 : ℝ) / (3.1376 - 2 * 0.9086))
      (y := 0.798) (z := 0.798 * 0.6931471803) (n := 4)
    · norm_num
    · norm_num
    · nlinarith [Real.log_two_gt_d9]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold cT
  nlinarith [hlog]

/-- `c_b(3.1376) ≤ 2.08`. -/
theorem cB_31376_le : cB 3.1376 ≤ 2.08 := by
  have hlog : Real.logb 2 (3.1376 : ℝ) ≤ 1.679 := by
    apply logb_two_le_of_taylor (x := 3.1376) (y := 1.679)
      (z := 1.679 * 0.6931471803) (n := 5)
    · norm_num
    · norm_num
    · nlinarith [Real.log_two_gt_d9]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  unfold cB
  nlinarith [hlog]

end Qatlib.Papers.LatticeSVP13.MainResults.ExponentCore
