/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Decay, energy gaps, and bound-state phases

This module records exponential decay and small-parameter energy estimates used to control
bound-state contributions in [Childs2009]. It bounds `boundDecay` and `2 * cosh κ - 2`, and
verifies that the two opposite phases agree at integer multiples of `π`.

## Main statements

* `boundDecay_m4_le`: Quartic distance and decay-rate bounds imply decay at most `exp(-1)`.
* `boundEnergy_gap`: Control the energy gap by an inverse eighth power.
* `boundPhase_two_signs`: The opposite bound-state phases agree at integer multiples of `π`.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.Parameters

open Real

set_option autoImplicit false

/-- The exponential decay factor `exp(-(κ * x))`. -/
noncomputable def boundDecay (κ x : ℝ) : ℝ := Real.exp (-(κ * x))

/-- If `κ * x ≥ 1`, the decay factor is at most `exp(-1)`. -/
theorem boundDecay_le_exp_neg_one {κ x : ℝ} (hx : 1 ≤ κ * x) :
    boundDecay κ x ≤ Real.exp (-1) := by
  unfold boundDecay
  exact Real.exp_le_exp.mpr (by linarith)

/-- For positive `m`, a decay rate at least `1 / m ^ 4` and distance at least `m ^ 4` give decay
at most `exp(-1)` [Childs2009]. -/
theorem boundDecay_m4_le (m κ x : ℝ) (hm : 0 < m) (hκ : 1 / m ^ 4 ≤ κ)
    (hx : m ^ 4 ≤ x) : boundDecay κ x ≤ Real.exp (-1) := by
  apply boundDecay_le_exp_neg_one
  have hm4 : 0 < m ^ 4 := by positivity
  have hprod : (1 / m ^ 4) * m ^ 4 ≤ κ * x :=
    mul_le_mul hκ hx (le_of_lt hm4)
      (le_trans (le_of_lt (div_pos one_pos hm4)) hκ)
  have hone : (1 / m ^ 4) * m ^ 4 = 1 := by
    field_simp
  rwa [hone] at hprod

/-- For `0 ≤ κ ≤ 1`, the quantity `2 * cosh κ - 2` is at most `κ² * exp(1 / 2)` [Childs2009]. -/
theorem two_cosh_sub_two_le_sq {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    2 * Real.cosh κ - 2 ≤ κ ^ 2 * Real.exp (1 / 2) := by
  have hcosh : Real.cosh κ ≤ Real.exp (κ ^ 2 / 2) := Real.cosh_le_exp_half_sq κ
  have ht0 : 0 ≤ κ ^ 2 / 2 := by positivity
  have ht1 : κ ^ 2 / 2 ≤ 1 / 2 := by nlinarith [sq_nonneg κ]
  have hexp : Real.exp (κ ^ 2 / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr ht1
  have hEpos : 0 < Real.exp (κ ^ 2 / 2) := Real.exp_pos _

  have hbase := Real.add_one_le_exp (-(κ ^ 2 / 2))
  have hmul := mul_le_mul_of_nonneg_right hbase (le_of_lt hEpos)
  rw [← Real.exp_add] at hmul
  have harg : -(κ ^ 2 / 2) + κ ^ 2 / 2 = 0 := by ring
  rw [harg, Real.exp_zero] at hmul
  have hkey : Real.exp (κ ^ 2 / 2) - 1 ≤ (κ ^ 2 / 2) * Real.exp (κ ^ 2 / 2) := by
    nlinarith [hmul]
  have hstep : (κ ^ 2 / 2) * Real.exp (κ ^ 2 / 2) ≤
      (κ ^ 2 / 2) * Real.exp (1 / 2) :=
    mul_le_mul_of_nonneg_left hexp ht0
  nlinarith [hcosh, hkey, hstep]

/-- For `m ≥ 1` and `0 ≤ κ ≤ 1 / m ^ 4`, the energy gap `2 * cosh κ - 2` is at most `exp(1 / 2)
/ m ^ 8` [Childs2009]. -/
theorem boundEnergy_gap (m κ : ℝ) (hm : 1 ≤ m) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / m ^ 4) :
    2 * Real.cosh κ - 2 ≤ Real.exp (1 / 2) / m ^ 8 := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hm4 : 1 ≤ m ^ 4 := by
    calc (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ m ^ 4 := by apply pow_le_pow_left₀ (by norm_num) hm 4
  have hinv : 1 / m ^ 4 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hm4
  have hκ1 : κ ≤ 1 := le_trans hκ hinv
  have hmain := two_cosh_sub_two_le_sq hκ0 hκ1
  have hsq : κ ^ 2 ≤ (1 / m ^ 4) ^ 2 := by
    apply pow_le_pow_left₀ hκ0 hκ
  have hm4pos : 0 < m ^ 4 := by positivity
  have hcoef : ((1 / m ^ 4) ^ 2) * Real.exp (1 / 2) = Real.exp (1 / 2) / m ^ 8 := by
    rw [div_pow, one_pow]
    ring
  have hb : κ ^ 2 * Real.exp (1 / 2) ≤ (1 / m ^ 4) ^ 2 * Real.exp (1 / 2) :=
    mul_le_mul_of_nonneg_right hsq (le_of_lt (Real.exp_pos _))
  rw [hcoef] at hb
  linarith [hmain]

/-- The complex phase `exp(2πni)` equals one for every integer `n`. -/
theorem boundPhase_pi_multiple (n : ℤ) :
    Complex.exp (((2 * Real.pi * n : ℝ) : ℂ) * Complex.I) = 1 := by
  have h : ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I = n * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- The complex phases `exp(2πni)` and `exp(-2πni)` agree for every integer `n` [Childs2009]. -/
theorem boundPhase_two_signs (n : ℤ) :
    Complex.exp (((2 * Real.pi * n : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * Real.pi * n) : ℝ) : ℂ) * Complex.I) := by
  rw [boundPhase_pi_multiple n]
  have h : ((↑(-(2 * Real.pi * (n : ℝ)) : ℝ)) : ℂ) * Complex.I =
      ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

end Qatlib.Papers.UniversalWalk08.MainResults.Parameters
