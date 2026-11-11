/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.GammaModulus
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Conditional limit for the square-root-schedule complement

This module records the leading-term change of variables and a conditional limit for the
displayed square-root-schedule formulas of [KadowakiNishimori1998]. It rewrites `1 / (256γ²)`
after substituting `γ = c² / (2h)`.

Assuming that the displayed weight is asymptotically equivalent to `h² / (64c⁴)`, the
corresponding displayed complement tends to one as `c` tends to infinity.

## Main statements

* `sqrtSchedule_leading_eq`: rewrites the leading term in `h` and `c`.
* `sqrtSchedule_formula_tendsto_one_of_asymptotic`: obtains convergence of the complement from
  the supplied equivalent.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Filter
open scoped Topology

/-- For positive `h` and `c`, substituting `γ = c ^ 2 / (2h)` into `1 / (256γ ^ 2)` gives `h ^ 2
/ (64c ^ 4)` [KadowakiNishimori1998]. -/
theorem sqrtSchedule_leading_eq (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    1 / (256 * (c ^ 2 / (2 * h)) ^ 2) = h ^ 2 / (64 * c ^ 4) := by
  field_simp
  ring

/-- The displayed square-root-schedule complement equals one minus its displayed weight. -/
theorem sqrtSchedule_displayed_complement_eq (γ : ℝ) :
    sqrtScheduleDisplayedComplement γ = 1 - sqrtScheduleDisplayedWeight γ := rfl

/-- If the displayed weight at `γ = c ^ 2 / (2h)` is asymptotically equivalent to `h ^ 2 / (64c
^ 4)`, then the corresponding complement tends to one as `c` tends to infinity
[KadowakiNishimori1998]. -/
theorem sqrtSchedule_formula_tendsto_one_of_asymptotic (h : ℝ)
    (ha : Asymptotics.IsEquivalent atTop
      (fun c : ℝ => sqrtScheduleDisplayedWeight (c ^ 2 / (2 * h)))
      (fun c : ℝ => h ^ 2 / (64 * c ^ 4))) :
    Tendsto (fun c : ℝ => sqrtScheduleDisplayedComplement (c ^ 2 / (2 * h))) atTop (𝓝 1) := by
  have hzero : Tendsto (fun c : ℝ => h ^ 2 / (64 * c ^ 4)) atTop (𝓝 0) := by
    have hp : Tendsto (fun c : ℝ => c ^ 4) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
    have hinv : Tendsto (fun c : ℝ => (c ^ 4)⁻¹) atTop (𝓝 0) := hp.inv_tendsto_atTop
    have hmul : Tendsto (fun c : ℝ => (h ^ 2 / 64) * (c ^ 4)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul (h ^ 2 / 64)
    refine Tendsto.congr' ?_ hmul
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    field_simp
  have hexc : Tendsto (fun c : ℝ => sqrtScheduleDisplayedWeight (c ^ 2 / (2 * h)))
      atTop (𝓝 0) :=
    ha.symm.tendsto_nhds hzero
  have hmain := (tendsto_const_nhds (x := (1 : ℝ))).sub hexc
  rw [sub_zero] at hmain
  simpa [sqrtScheduleDisplayedComplement] using hmain

end Qatlib.Papers.TITCMTReport98.MainResults
