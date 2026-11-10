/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Real

theorem lam_le_exp_of_power_bound {lam tau T : ℝ} (hlam0 : 0 < lam) (htau : 0 < tau)
    (hT : 0 < T) (htauT : tau ≤ 2 * Real.exp 1 * T)
    (hpow : ∀ t : ℕ, 1 ≤ t → lam ^ t ≤ 2 * Real.exp (-(t / tau))) :
    lam ≤ Real.exp (-(1 / (2 * Real.exp 1 * T))) := by
  by_contra hcon
  push_neg at hcon
  have hden : (0 : ℝ) < 2 * Real.exp 1 * T := by positivity
  set c : ℝ := Real.log lam + 1 / (2 * Real.exp 1 * T) with hc
  have hcpos : 0 < c := by
    have hlt : Real.log (Real.exp (-(1 / (2 * Real.exp 1 * T)))) < Real.log lam :=
      Real.log_lt_log (Real.exp_pos _) hcon
    rw [Real.log_exp] at hlt
    rw [hc]
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨t, ht⟩ := exists_nat_gt (Real.log 2 / c)
  have htpos : 0 < t := by
    have : (0 : ℝ) < Real.log 2 / c := div_pos hlog2 hcpos
    have htR : (0 : ℝ) < (t : ℝ) := lt_trans this ht
    exact_mod_cast htR
  have ht1 : 1 ≤ t := Nat.succ_le_of_lt htpos
  have htc : Real.log 2 < (t : ℝ) * c := by
    rw [div_lt_iff₀ hcpos] at ht
    simpa [mul_comm] using ht
  have hexp2 : 2 < Real.exp ((t : ℝ) * c) := by
    have := (Real.log_lt_iff_lt_exp (x := 2) (y := (t : ℝ) * c) (by norm_num)).mp htc
    simpa using this
  have hloglam : Real.log lam = c - 1 / (2 * Real.exp 1 * T) := by
    rw [hc]; ring
  have hpoweq : lam ^ t = Real.exp ((t : ℝ) * c - (t : ℝ) / (2 * Real.exp 1 * T)) := by
    have harg : (t : ℝ) * c - (t : ℝ) / (2 * Real.exp 1 * T) =
        (t : ℝ) * Real.log lam := by
      rw [hloglam]; ring
    rw [harg, Real.exp_nat_mul, Real.exp_log hlam0]
  have hEpos : (0 : ℝ) < Real.exp (-((t : ℝ) / (2 * Real.exp 1 * T))) := Real.exp_pos _
  have hFle : Real.exp (-((t : ℝ) / tau)) ≤
      Real.exp (-((t : ℝ) / (2 * Real.exp 1 * T))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_left (by positivity) htau

    exact htauT
  have hmain : 2 * Real.exp (-((t : ℝ) / tau)) < lam ^ t := by
    rw [hpoweq, Real.exp_sub]
    have hcalc : Real.exp ((t : ℝ) * c) / Real.exp ((t : ℝ) / (2 * Real.exp 1 * T))
        = Real.exp ((t : ℝ) * c) *
            Real.exp (-((t : ℝ) / (2 * Real.exp 1 * T))) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    rw [hcalc]
    have h2 : 2 * Real.exp (-((t : ℝ) / (2 * Real.exp 1 * T))) <
        Real.exp ((t : ℝ) * c) *
          Real.exp (-((t : ℝ) / (2 * Real.exp 1 * T))) := by
      exact mul_lt_mul_of_pos_right hexp2 hEpos
    have h3 : 2 * Real.exp (-((t : ℝ) / tau)) ≤
        2 * Real.exp (-((t : ℝ) / (2 * Real.exp 1 * T))) := by
      exact mul_le_mul_of_nonneg_left hFle (by norm_num)
    linarith
  exact absurd (hpow t ht1) (not_le.mpr hmain)

end Qatlib.Papers.GrpCommTest05.MainResults
