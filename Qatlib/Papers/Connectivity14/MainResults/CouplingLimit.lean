/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Connectivity14.MainResults.SimplexComplete
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The first-stage critical coupling and its leading term

Rationalizing the square root in the supplement's exact coupling gives a
ratio whose limit is one. This relates that exact coupling to the leading
`2 / M` used in the main text.
-/

set_option autoImplicit false

namespace Qatlib.Papers.Connectivity14.MainResults

open Qatlib.Papers.Connectivity14.MainResults
open Filter
open scoped Topology

/-- For positive size, rationalizing the supplementary critical coupling gives the
ratio of that coupling to the main text's leading term. -/
theorem gammaC1_ratio (M : ℝ) (hM : 0 < M) :
    gammaC1 M / (2 / M) = 2 / (Real.sqrt (1 + 8 / M) + 1) := by
  have hM0 := hM.ne'
  have hroot : Real.sqrt (M * (M + 8)) = M * Real.sqrt (1 + 8 / M) := by
    calc
      _ = Real.sqrt (M ^ 2 * (1 + 8 / M)) := by
        congr 1
        field_simp
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM.le]
  have hArg : 0 ≤ 1 + 8 / M := by positivity
  have hprod : M * ((Real.sqrt (1 + 8 / M)) ^ 2 - 1) = 8 := by
    rw [Real.sq_sqrt hArg, add_sub_cancel_left]
    field_simp
  calc
    gammaC1 M / (2 / M) = M * (Real.sqrt (1 + 8 / M) - 1) / 4 := by
      rw [gammaC1, hroot]
      field_simp
      ring
    _ = 2 / (Real.sqrt (1 + 8 / M) + 1) := by
      apply (eq_div_iff (by positivity)).mpr
      calc
        _ = M * ((Real.sqrt (1 + 8 / M)) ^ 2 - 1) / 4 := by ring
        _ = 2 := by rw [hprod]; norm_num

/-- The exact first-stage critical coupling is asymptotically equivalent to `2/M`. -/
theorem gammaC1_asymp :
    Asymptotics.IsEquivalent atTop gammaC1 (fun M : ℝ => 2 / M) := by
  have hpos : ∀ᶠ M : ℝ in atTop, 0 < M := eventually_gt_atTop 0
  rw [Asymptotics.isEquivalent_iff_tendsto_one
    (hpos.mono fun M hM => div_ne_zero (by norm_num) hM.ne')]
  have hzero : Tendsto (fun M : ℝ => 8 / M) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero : Tendsto (fun M : ℝ => M⁻¹) atTop
      (𝓝 0)).const_mul (8 : ℝ)
  have hsqrt : Tendsto (fun M : ℝ => Real.sqrt (1 + 8 / M) + 1) atTop (𝓝 2) := by
    have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
    simpa [one_add_one_eq_two] using (hsum.sqrt).add_const (1 : ℝ)
  have hlim : Tendsto (fun M : ℝ => 2 / (Real.sqrt (1 + 8 / M) + 1)) atTop (𝓝 1) := by
    have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hquot := htwo.div hsqrt (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at hquot
    exact hquot
  exact hlim.congr' (hpos.mono fun M hM => (gammaC1_ratio M hM).symm)

end Qatlib.Papers.Connectivity14.MainResults
