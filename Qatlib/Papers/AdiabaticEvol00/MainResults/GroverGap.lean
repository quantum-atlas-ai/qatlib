/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs

/-!
# Exponential runtime ratios from a Grover gap scale

This module defines the explicit gap scale `groverMinGap n = 2 * 2 ^ (-n / 2)` and computes its
square. The theorems `grover_time_exponential` and `grover_time_from_gap` show that an energy
scale at least one and a positive gap bounded by this scale force `4 * E / g ^ 2` to be at least
`2 ^ n`. The mathematical context is [FarhiEtAl2000].

## Main statements

* `groverMinGap_sq`: The square of the defined Grover gap scale equals `4 / 2 ^ n`.
* `grover_time_from_gap`: If `E ≥ 1` and the positive gap `g` is at most `groverMinGap n`, then
  `2 ^ n ≤ 4 * E / g ^ 2`.

## References

* [Farhi et al., 2000][FarhiEtAl2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.GroverGap

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

/-- The explicit Grover gap scale `2 * 2 ^ (-n / 2)`, using real exponentiation [FarhiEtAl2000]. -/
def groverMinGap (n : ℕ) : ℝ := 2 * (2 : ℝ) ^ (-(n : ℝ) / 2)

/-- The defined Grover gap scale is strictly positive for every natural number of bits
[FarhiEtAl2000]. -/
theorem groverMinGap_pos (n : ℕ) : 0 < groverMinGap n := by
  unfold groverMinGap
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)

/-- The real power `2 ^ (-n)` equals the reciprocal of the natural power `2 ^ n`. -/
theorem two_rpow_neg_nat (n : ℕ) : (2 : ℝ) ^ (-(n : ℝ)) = 1 / (2 : ℝ) ^ n := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_natCast]
  rw [one_div]

/-- The square of the defined Grover gap scale equals `4 / 2 ^ n` [FarhiEtAl2000]. -/
theorem groverMinGap_sq (n : ℕ) : (groverMinGap n) ^ 2 = 4 / (2 : ℝ) ^ n := by
  unfold groverMinGap
  rw [mul_pow]
  norm_num
  have hsq : ((2 : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(n : ℝ) / 2)) 2]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hsq, two_rpow_neg_nat]
  ring

/-- If `E ≥ 1`, `g > 0`, and `g ^ 2 ≤ 4 / 2 ^ n`, then `2 ^ n ≤ 4 * E / g ^ 2` [FarhiEtAl2000]. -/
theorem grover_time_exponential {E g : ℝ} {n : ℕ} (hE : 1 ≤ E) (hg : 0 < g)
    (hgap : g ^ 2 ≤ 4 / (2 : ℝ) ^ n) :
    (2 : ℝ) ^ n ≤ 4 * E / g ^ 2 := by
  have h2n : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hg2pos : 0 < g ^ 2 := pow_pos hg 2
  have h4 : (2 : ℝ) ^ n * (4 / (2 : ℝ) ^ n) = 4 := by
    field_simp
  have h1 : (2 : ℝ) ^ n * g ^ 2 ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hgap (le_of_lt h2n)
    rwa [h4] at this
  rw [le_div_iff₀ hg2pos]
  nlinarith [h1, hE]

/-- If `E ≥ 1` and the positive gap `g` is at most `groverMinGap n`, then `2 ^ n ≤ 4 * E / g ^
2` [FarhiEtAl2000]. -/
theorem grover_time_from_gap {E g : ℝ} {n : ℕ} (hE : 1 ≤ E) (hg : 0 < g)
    (hgap : g ≤ groverMinGap n) :
    (2 : ℝ) ^ n ≤ 4 * E / g ^ 2 := by
  apply grover_time_exponential hE hg
  calc g ^ 2 ≤ (groverMinGap n) ^ 2 := by
        have := mul_self_le_mul_self (le_of_lt hg) hgap
        simpa [pow_two] using this
    _ = 4 / (2 : ℝ) ^ n := groverMinGap_sq n

end Qatlib.Papers.AdiabaticEvol00.MainResults.GroverGap
