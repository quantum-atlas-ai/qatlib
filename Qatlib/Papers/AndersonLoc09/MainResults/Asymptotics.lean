/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AndersonLoc09.MainResults.MainResult
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

open Real Filter
open scoped Topology

theorem lambdaStar_pos (N f2 : ℝ) (hN : 0 < N) (hf2 : 0 < f2) :
    0 < lambdaStar N f2 := by
  unfold lambdaStar
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (Real.rpow_pos_of_pos hf2 _)) (Real.rpow_pos_of_pos hN _)

theorem lambdaStar_tendsto_zero (f2 : ℝ) :
    Tendsto (fun N : ℝ => lambdaStar N f2) atTop (𝓝 0) := by
  have h := Filter.Tendsto.const_mul (Real.sqrt 2 * Real.rpow f2 (-(1 / 4)))
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 8 by norm_num))
  simpa [lambdaStar, mul_assoc, mul_zero] using h

theorem N0_pos (A f2 : ℝ) (hA : 0 < A) (hf2 : 0 < f2) : 0 < N0 A f2 := by
  unfold N0
  positivity

theorem vAlpha_pos (α : ℝ) (hα : 0 < α) : 0 < vAlpha α := by
  unfold vAlpha
  have h : Real.exp (-3 * α) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  nlinarith

theorem vAlpha_lt_fourNinths (α : ℝ) : vAlpha α < 4 / 9 := by
  unfold vAlpha
  have h : 0 < Real.exp (-3 * α) := Real.exp_pos _
  nlinarith

theorem vAlpha_monotone : Monotone vAlpha := by
  intro a b hab
  unfold vAlpha
  have h : Real.exp (-3 * b) ≤ Real.exp (-3 * a) := Real.exp_le_exp.mpr (by nlinarith)
  nlinarith

theorem vAlpha_tendsto : Tendsto vAlpha atTop (𝓝 (4 / 9)) := by
  have hexp : Tendsto (fun a : ℝ => Real.exp (-3 * a)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 by norm_num))
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := Filter.Tendsto.const_mul (4 / 9 : ℝ) (hone.sub hexp)
  have h' : Tendsto (fun a : ℝ => (4 / 9) * (1 - Real.exp (-3 * a))) atTop (𝓝 (4 / 9)) := by
    simpa [mul_zero, sub_zero] using h
  have hv : vAlpha = fun a : ℝ => (4 / 9) * (1 - Real.exp (-3 * a)) := rfl
  rw [hv]
  exact h'

theorem gap_ultra_small_vAlpha (N0 α : ℝ) (hN0 : 0 < N0) (hα : 0 < α) :
    ∃ N1 : ℝ, 0 < N1 ∧ ∀ N : ℝ, N1 ≤ N →
      gapFormula (vAlpha α * N) N N0 ≤ Real.exp (-N) :=
  gap_ultra_small N0 (vAlpha α) hN0 (vAlpha_pos α hα)

end Qatlib.Papers.AndersonLoc09.MainResults
