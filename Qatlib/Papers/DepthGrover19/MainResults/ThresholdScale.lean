/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Qatlib.Papers.DepthGrover19.MainResults.SourceDepthOptimization

@[expose] public section

/-!
# Scaling of the two-depth comparison threshold

The threshold in Eq. (46) compares consecutive diffusion depths.
Linear depth makes the numerator's depth difference constant and
keeps one factor of n in the denominator. The exact positive gap
proportional to the inverse square root of database size contributes
the square-root factor in Eq. (47).
-/

set_option autoImplicit false

open Qatlib.Papers.DepthGrover19.MainResults

namespace Qatlib.Papers.DepthGrover19.MainResults

/-- The comparison threshold of Eq. (46) has the scale of Eq. (47)
for linear diffusion depth and a positive gap proportional to the
inverse square root of database size. -/
theorem sandwich_threshold_isBigO (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (P : ℕ → ℝ) (hP : ∀ n, 0 ≤ P n ∧ P n ≤ 1) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ =>
        2 * (c * (n : ℝ) - c * ((n - 1 : ℕ) : ℝ)) * P n /
          (3 * (c * (n : ℝ)) * (c' * (Real.sqrt (dbSize n))⁻¹)))
      (fun n : ℕ => (n : ℝ)⁻¹ * Real.sqrt (dbSize n)) := by
  refine Asymptotics.IsBigO.of_bound (2 / (3 * c')) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  rw [sandwich_threshold_eq c c' hc hc' P n hn]
  have hconst : 0 ≤ (2 : ℝ) / (3 * c') := by positivity
  have hscale : 0 ≤ (n : ℝ)⁻¹ * Real.sqrt (dbSize n) := by positivity
  have hform : Real.sqrt (dbSize n) / (n : ℝ) =
      (n : ℝ)⁻¹ * Real.sqrt (dbSize n) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hform]
  simp only [Real.norm_eq_abs, abs_of_nonneg hscale,
    abs_of_nonneg (mul_nonneg (mul_nonneg hconst (hP n).1) hscale)]
  have hp := mul_le_mul_of_nonneg_left (hP n).2 hconst
  rw [mul_one] at hp
  exact mul_le_mul_of_nonneg_right hp hscale

end Qatlib.Papers.DepthGrover19.MainResults
