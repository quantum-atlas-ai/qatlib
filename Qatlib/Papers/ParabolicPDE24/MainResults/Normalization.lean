/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ParabolicPDE24.MainResults

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalizedState (x : E) : E := (‖x‖ : ℝ)⁻¹ • x

theorem norm_normalizedState (x : E) (hx : x ≠ 0) : ‖normalizedState x‖ = 1 := by
  have h : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  rw [normalizedState, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg x)]
  exact inv_mul_cancel₀ (ne_of_gt h)

theorem abs_inv_sub_inv_mul_le (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    |α⁻¹ - β⁻¹| * β ≤ |β - α| / α := by
  have h : |α⁻¹ - β⁻¹| * β = |β - α| / α := by
    rw [inv_sub_inv (ne_of_gt hα) (ne_of_gt hβ)]
    rw [abs_div, abs_mul, abs_of_pos hα, abs_of_pos hβ]
    field_simp [ne_of_gt hα, ne_of_gt hβ]
  exact le_of_eq h

theorem norm_normalizedState_sub_le (a b : E) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖normalizedState a - normalizedState b‖ ≤ 2 * ‖a - b‖ / ‖a‖ := by
  have ha' : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hb' : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hdecomp : normalizedState a - normalizedState b =
      (‖a‖ : ℝ)⁻¹ • (a - b) + ((‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹) • b := by
    rw [normalizedState, normalizedState, smul_sub, sub_smul]
    abel
  have h1 : ‖(‖a‖ : ℝ)⁻¹ • (a - b)‖ = (‖a‖ : ℝ)⁻¹ * ‖a - b‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg a)]
  have h2 : ‖((‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹) • b‖ =
      |(‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹| * ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  rw [hdecomp]
  calc ‖(‖a‖ : ℝ)⁻¹ • (a - b) + ((‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹) • b‖
      ≤ ‖(‖a‖ : ℝ)⁻¹ • (a - b)‖ + ‖((‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹) • b‖ :=
        norm_add_le _ _
    _ = (‖a‖ : ℝ)⁻¹ * ‖a - b‖ +
          |(‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹| * ‖b‖ := by rw [h1, h2]
    _ ≤ (‖a‖ : ℝ)⁻¹ * ‖a - b‖ + ‖a - b‖ / ‖a‖ := by
        have hbd : |(‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹| * ‖b‖ ≤
            |‖b‖ - ‖a‖| / ‖a‖ := abs_inv_sub_inv_mul_le ‖a‖ ‖b‖ ha' hb'
        have habs : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
          have h := abs_norm_sub_norm_le b a
          rwa [norm_sub_rev] at h
        have hfin : |(‖a‖ : ℝ)⁻¹ - (‖b‖ : ℝ)⁻¹| * ‖b‖ ≤ ‖a - b‖ / ‖a‖ :=
          hbd.trans (div_le_div_of_nonneg_right habs ha'.le)
        linarith
    _ = 2 * ‖a - b‖ / ‖a‖ := by
        field_simp [ne_of_gt ha']
        ring

theorem conditional_normalized_budget
    (k ε C : ℝ) (_hk : 0 < k) (hε : 0 < ε) (hC : 0 ≤ C)
    (u ũ : ℝ → E) {t : ℝ}
    (h_err : ‖ũ t - u t‖ ≤ C * ε ^ 2 * Real.exp (-2 * k * t))
    (h_lower : Real.exp (-2 * k * t) ≤ ‖ũ t‖)
    (hu : u t ≠ 0) (hũ : ũ t ≠ 0) :
    ‖normalizedState (ũ t) - normalizedState (u t)‖ ≤ 2 * C * ε ^ 2 := by
  have hexp_pos : (0 : ℝ) < Real.exp (-2 * k * t) := Real.exp_pos _
  have hratio : ‖ũ t - u t‖ / ‖ũ t‖ ≤ C * ε ^ 2 := by
    have hinv : 1 / ‖ũ t‖ ≤ 1 / Real.exp (-2 * k * t) :=
      one_div_le_one_div_of_le hexp_pos h_lower
    have hA : 0 ≤ C * ε ^ 2 * Real.exp (-2 * k * t) :=
      mul_nonneg (mul_nonneg hC (sq_nonneg ε)) hexp_pos.le
    calc ‖ũ t - u t‖ / ‖ũ t‖ = ‖ũ t - u t‖ * (1 / ‖ũ t‖) := by ring
      _ ≤ (C * ε ^ 2 * Real.exp (-2 * k * t)) *
            (1 / Real.exp (-2 * k * t)) :=
          mul_le_mul h_err hinv (by positivity) hA
      _ = C * ε ^ 2 := by
          field_simp [Real.exp_ne_zero]
  calc ‖normalizedState (ũ t) - normalizedState (u t)‖
      ≤ 2 * ‖ũ t - u t‖ / ‖ũ t‖ :=
        norm_normalizedState_sub_le (ũ t) (u t) hũ hu
    _ = 2 * (‖ũ t - u t‖ / ‖ũ t‖) := by ring
    _ ≤ 2 * (C * ε ^ 2) := by linarith
    _ = 2 * C * ε ^ 2 := by ring

theorem conditional_target_precision
    (k ε C δ : ℝ) (hk : 0 < k) (hε : 0 < ε) (hC : 0 < C) (hδ : 0 < δ)
    (u ũ : ℝ → E) {t : ℝ}
    (h_err : ‖ũ t - u t‖ ≤ C * ε ^ 2 * Real.exp (-2 * k * t))
    (h_lower : Real.exp (-2 * k * t) ≤ ‖ũ t‖)
    (hu : u t ≠ 0) (hũ : ũ t ≠ 0)
    (hεδ : ε ≤ Real.sqrt (δ / (2 * C))) :
    ‖normalizedState (ũ t) - normalizedState (u t)‖ ≤ δ := by
  have hdist := conditional_normalized_budget k ε C hk hε hC.le u ũ h_err h_lower hu hũ
  have h2C : (0 : ℝ) < 2 * C := by positivity
  have hsq : ε ^ 2 ≤ δ / (2 * C) := by
    have h := pow_le_pow_left₀ hε.le hεδ 2
    rwa [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ δ / (2 * C))] at h
  calc ‖normalizedState (ũ t) - normalizedState (u t)‖ ≤ 2 * C * ε ^ 2 := hdist
    _ ≤ 2 * C * (δ / (2 * C)) := by gcongr
    _ = δ := by field_simp

end Qatlib.Papers.ParabolicPDE24.MainResults
