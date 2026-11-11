/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.StationaryAndFamily
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Positivity and normalization identities for the line walk

This module proves positivity of the stationary curvature factor and of `momentDensity` in the
interior regime. It relates `pSlow` to `momentDensity` and evaluates the elementary
trigonometric normalization integral used with the formulas in [NayakVishwanath2000].

## Main statements

* `pSlow_eq_momentDensity_div`: separates the time factor from the slow probability expression.
* `moment_density_integral`: evaluates the normalized trigonometric integral as one.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real MeasureTheory
open scoped Interval

noncomputable section

/-- The stationary curvature factor is positive when `α² < 1/2`. -/
theorem omegaSecondAtStationary_pos {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    0 < omegaSecondAtStationary α := by
  unfold omegaSecondAtStationary
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 1 - 2 * α ^ 2 := by nlinarith
  exact mul_pos h1 (Real.sqrt_pos.2 h2)

/-- The slow probability expression equals `momentDensity α` divided by time. See
[NayakVishwanath2000]. -/
theorem pSlow_eq_momentDensity_div (α : ℝ) (t : ℕ) :
    pSlow α t = momentDensity α / (t : ℝ) := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    simp [pSlow, momentDensity]
  · have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp ht
    unfold pSlow momentDensity
    field_simp

/-- The moment density is positive under `α² < 1/2` and `α < 1`. -/
theorem momentDensity_pos {α : ℝ} (hα : α ^ 2 < 1 / 2) (hα1 : α < 1) :
    0 < momentDensity α := by
  unfold momentDensity
  apply div_pos (by linarith)
  exact mul_pos Real.pi_pos (abs_pos.mpr (ne_of_gt (omegaSecondAtStationary_pos hα)))

/-- Replacing `k` by `π - k` negates `cos k / √(1 + cos² k)`. -/
lemma cos_div_sqrt_pi_sub (k : ℝ) :
    Real.cos (Real.pi - k) / Real.sqrt (1 + Real.cos (Real.pi - k) ^ 2)
      = -(Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) := by
  rw [Real.cos_pi_sub]
  have h : 1 + (-Real.cos k) ^ 2 = 1 + Real.cos k ^ 2 := by ring
  rw [h, neg_div]

/-- The integral of `cos k / √(1 + cos² k)` over `[0, π]` is zero. -/
theorem integral_cos_div_sqrt_zero :
    (∫ k in (0 : ℝ)..Real.pi,
        Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) = 0 := by
  have hsub : (∫ k in (0 : ℝ)..Real.pi,
        Real.cos (Real.pi - k) / Real.sqrt (1 + Real.cos (Real.pi - k) ^ 2))
      = ∫ k in (0 : ℝ)..Real.pi,
        Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => Real.cos x / Real.sqrt (1 + Real.cos x ^ 2)) Real.pi
      (a := (0 : ℝ)) (b := Real.pi)
    simpa using this
  have hpt : (fun k : ℝ =>
        Real.cos (Real.pi - k) / Real.sqrt (1 + Real.cos (Real.pi - k) ^ 2))
      = fun k : ℝ => -(Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) := by
    funext k
    exact cos_div_sqrt_pi_sub k
  rw [hpt, intervalIntegral.integral_neg] at hsub
  linarith

/-- The integral of `1 + cos k / √(1 + cos² k)` over `[0, π]`, divided by `π`, equals one. See
[NayakVishwanath2000]. -/
theorem moment_density_integral :
    (1 / Real.pi) *
        (∫ k in (0 : ℝ)..Real.pi,
          (1 + Real.cos k / Real.sqrt (1 + Real.cos k ^ 2))) = 1 := by
  have hcont1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) Real.pi :=
    intervalIntegrable_const
  have hcont2 : IntervalIntegrable
      (fun k : ℝ => Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)) volume (0 : ℝ) Real.pi := by
    apply Continuous.intervalIntegrable
    refine Continuous.div (by fun_prop) ?_ ?_
    · exact Real.continuous_sqrt.comp (by fun_prop)
    · intro k
      exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [sq_nonneg (Real.cos k)]))
  have hsplit : (∫ k in (0 : ℝ)..Real.pi,
        (1 + Real.cos k / Real.sqrt (1 + Real.cos k ^ 2)))
      = (∫ _k in (0 : ℝ)..Real.pi, (1 : ℝ))
        + ∫ k in (0 : ℝ)..Real.pi, Real.cos k / Real.sqrt (1 + Real.cos k ^ 2) := by
    rw [intervalIntegral.integral_add hcont1 hcont2]
  rw [hsplit, integral_cos_div_sqrt_zero]
  have hconst : (∫ _k in (0 : ℝ)..Real.pi, (1 : ℝ)) = Real.pi := by
    simp
  rw [hconst]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

end

end Qatlib.Papers.QWalkLine00.MainResults
