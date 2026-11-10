/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ClockBounds
import Mathlib.Analysis.Asymptotics.Defs

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

theorem tiedGroup_sqrt_step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b - a) / (b * Real.sqrt a) ≤
      2 * (1 / Real.sqrt a - 1 / Real.sqrt b) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have ha2 := Real.sq_sqrt ha.le
  have hb2 := Real.sq_sqrt hb.le
  apply (div_le_iff₀ (by positivity : 0 < b * Real.sqrt a)).2
  have heq : (2 * (1 / Real.sqrt a - 1 / Real.sqrt b)) * (b * Real.sqrt a) =
      2 * b - 2 * Real.sqrt a * Real.sqrt b := by
    field_simp
    nlinarith [congrArg (fun z : ℝ => Real.sqrt a * z) hb2]
  rw [heq]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]

theorem tiedGroup_log_step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have heq : (b - a) / b = 1 - a / b := by field_simp
  rw [heq]
  linarith

theorem log_sq_le_sixteen_sqrt (N : ℕ) (hN : 0 < N) :
    (Real.log (N : ℝ)) ^ 2 ≤ 16 * Real.sqrt (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hn
  have hss : 0 < Real.sqrt (Real.sqrt (N : ℝ)) := Real.sqrt_pos.2 hs
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hb := Real.log_le_sub_one_of_pos hss
  rw [Real.log_sqrt hs.le, Real.log_sqrt hn.le] at hb
  have hbound : Real.log (N : ℝ) ≤ 4 * Real.sqrt (Real.sqrt (N : ℝ)) := by linarith
  have hsq := mul_self_le_mul_self hlog hbound
  have hr := Real.sq_sqrt hs.le
  nlinarith

theorem sourceTimeout_le_sqrt (N : ℕ) (hN : 0 < N) :
    sourceTimeout N ≤
      ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) * Real.sqrt N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := div_le_div_of_nonneg_right (log_sq_le_sixteen_sqrt N hN)
    (sq_nonneg (Real.log 2))
  unfold sourceTimeout binaryLog
  rw [div_pow]
  calc
    _ ≤ (45 / 2 : ℝ) * Real.sqrt N +
        (7 / 5 : ℝ) * (16 * Real.sqrt N / (Real.log 2) ^ 2) := by nlinarith
    _ = _ := by ring

theorem sourceTimeout_isBigO_sqrt :
    Asymptotics.IsBigO Filter.atTop sourceTimeout (fun N : ℕ => Real.sqrt (N : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound
    ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hnonneg : 0 ≤ sourceTimeout N := by unfold sourceTimeout; positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (Real.sqrt_nonneg (N : ℝ))] using sourceTimeout_le_sqrt N hN

end Qatlib.Concepts.AmplitudeSearch.Amplification
