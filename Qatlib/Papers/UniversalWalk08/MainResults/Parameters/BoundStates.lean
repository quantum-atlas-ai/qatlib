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

namespace Qatlib.Papers.UniversalWalk08.MainResults.Parameters

open Real

set_option autoImplicit false

noncomputable def boundDecay (κ x : ℝ) : ℝ := Real.exp (-(κ * x))

theorem boundDecay_le_exp_neg_one {κ x : ℝ} (hx : 1 ≤ κ * x) :
    boundDecay κ x ≤ Real.exp (-1) := by
  unfold boundDecay
  exact Real.exp_le_exp.mpr (by linarith)

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

theorem boundPhase_pi_multiple (n : ℤ) :
    Complex.exp (((2 * Real.pi * n : ℝ) : ℂ) * Complex.I) = 1 := by
  have h : ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I = n * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

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
