/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.Defs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Filter
open scoped Topology

theorem landauZener_displayed_complement_eq (h c : ℝ) :
    landauZenerDisplayedComplement h c = 1 - ‖landauZenerDisplayedAmplitude h c‖ ^ 2 := rfl

theorem landauZener_displayed_complement_le_one (h c : ℝ) :
    landauZenerDisplayedComplement h c ≤ 1 := by
  unfold landauZenerDisplayedComplement
  have : (0 : ℝ) ≤ ‖landauZenerDisplayedAmplitude h c‖ ^ 2 := sq_nonneg _
  linarith

theorem landauZener_formula_tendsto_one_of_asymptotic (h : ℝ)
    (ha : Asymptotics.IsEquivalent atTop
      (fun x : ℝ => ‖landauZenerDisplayedAmplitude h (h ^ 2 / x)‖ ^ 2)
      (fun x : ℝ => 9 / (16 * x ^ 2))) :
    Tendsto (fun x : ℝ => landauZenerDisplayedComplement h (h ^ 2 / x)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun x : ℝ => (9 : ℝ) / (16 * x ^ 2)) atTop (𝓝 0) := by
    have hp : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    have hinv : Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (𝓝 0) := hp.inv_tendsto_atTop
    have hmul : Tendsto (fun x : ℝ => ((9 : ℝ) / 16) * (x ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul ((9 : ℝ) / 16)
    refine Tendsto.congr' ?_ hmul
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have hexc : Tendsto (fun x : ℝ => ‖landauZenerDisplayedAmplitude h (h ^ 2 / x)‖ ^ 2)
      atTop (𝓝 0) :=
    ha.symm.tendsto_nhds hzero
  have hmain := (tendsto_const_nhds (x := (1 : ℝ))).sub hexc
  rw [sub_zero] at hmain
  simpa [landauZenerDisplayedComplement] using hmain

end Qatlib.Papers.TITCMTReport98.MainResults
