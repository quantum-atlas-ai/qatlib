/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LocAdiabSrch01.MainResults.Optimality.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Leading coefficient of the local adiabatic search lower bound

Normalizing Eq. (38) by the square root of the input size gives a factor of
one minus the reciprocal of the input size. This establishes the leading
coefficient used in the large-size statement of Eq. (39).
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Qatlib.Papers.LocAdiabSrch01.MainResults

/-- For positive input size the normalized Eq. (38) expression equals its
leading coefficient times the finite-size factor. -/
private theorem lower_bound_ratio_eq (ε N : ℝ) (hN : 0 < N) :
    (ε * (N - 1) / (4 * Real.sqrt N)) / Real.sqrt N = (ε / 4) * (1 - N⁻¹) := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  calc
    _ = ε * (N - 1) / (4 * Real.sqrt N ^ 2) := by field_simp
    _ = _ := by rw [Real.sq_sqrt hN.le]; field_simp

/-- The normalized finite lower-bound expression tends to the leading coefficient in Eq. (39). -/
theorem source_lower_bound_ratio_tendsto (ε : ℝ) :
    Tendsto (fun N : ℝ => (ε * (N - 1) / (4 * Real.sqrt N)) / Real.sqrt N)
      atTop (𝓝 (ε / 4)) := by
  have h : Tendsto (fun N : ℝ => (1 : ℝ) - N⁻¹) atTop (𝓝 1) := by
    have hinv : Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa using tendsto_const_nhds.sub hinv
  have hmul := h.const_mul (ε / 4)
  rw [mul_one] at hmul
  apply hmul.congr'
  exact (eventually_gt_atTop 0).mono fun N hN => (lower_bound_ratio_eq ε N hN).symm

/-- At finite positive size the lower-bound expression is strictly below its leading term
when the error parameter is positive. -/
theorem source_lower_bound_lt_leading {ε N : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    ε * (N - 1) / (4 * Real.sqrt N) < (ε / 4) * Real.sqrt N := by
  have hs := Real.sqrt_pos.mpr hN
  rw [← div_lt_div_iff_of_pos_right hs, lower_bound_ratio_eq ε N hN,
    mul_div_cancel_right₀ _ hs.ne']
  exact mul_lt_of_lt_one_right (by positivity) (sub_lt_self _ (inv_pos.mpr hN))

end Qatlib.Papers.LocAdiabSrch01.MainResults
