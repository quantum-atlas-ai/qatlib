/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QLinearSolver24.MainResults.Definitions
public import Qatlib.Papers.QLinearSolver24.MainResults.TheoremOneCorollaryOne
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.TheoremOneCorollaryOne
open Qatlib.Papers.QLinearSolver24.MainResults

/-- The inverse hyperbolic cosine is at most the logarithm of twice its positive argument. -/
theorem arcosh_inv_upper (η : ℝ) (hη : 0 < η) :
    Real.arcosh η⁻¹ ≤ Real.log (2 / η) := by
  have hi : 0 < η⁻¹ := inv_pos.mpr hη
  have hs : Real.sqrt ((η⁻¹) ^ 2 - 1) ≤ η⁻¹ := by
    apply (Real.sqrt_le_left hi.le).mpr
    linarith
  unfold Real.arcosh
  apply Real.log_le_log (by positivity)
  rw [div_eq_mul_inv]
  linarith

/-- The rational filter parameter has an exact logarithmic inverse-cosh expression. -/
theorem filter_arcosh_log (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Real.arcosh ((1 + x ^ 2) / (1 - x ^ 2)) =
      Real.log ((1 + x) / (1 - x)) := by
  have hd : 0 < 1 - x ^ 2 := by nlinarith
  have hc : 1 ≤ (1 + x ^ 2) / (1 - x ^ 2) := by
    rw [le_div_iff₀ hd]
    nlinarith
  have hs : Real.sqrt (((1 + x ^ 2) / (1 - x ^ 2)) ^ 2 - 1) =
      2 * x / (1 - x ^ 2) := by
    have hrad : 0 ≤ ((1 + x ^ 2) / (1 - x ^ 2)) ^ 2 - 1 := by nlinarith
    apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).mpr
    field_simp
    ring
  unfold Real.arcosh
  rw [hs]
  congr 1
  field_simp
  ring

/-- The inverse-cosh filter denominator is bounded below by twice the reciprocal condition number. -/
theorem filter_arcosh_lower (κ : ℝ) (hκ : 1 < κ) :
    2 / κ ≤ Real.arcosh ((1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ))) := by
  have hk : 0 < κ := by linarith
  have hx0 : 0 < κ⁻¹ := inv_pos.mpr hk
  have hx1 : κ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
  have hz : κ ^ (-2 : ℤ) = (κ⁻¹) ^ 2 := by simp
  rw [hz, filter_arcosh_log κ⁻¹ hx0 hx1]
  have hseries := Real.sum_range_le_log_div hx0.le hx1 1
  norm_num at hseries
  simpa only [div_eq_mul_inv] using (show 2 * κ⁻¹ ≤
    Real.log ((1 + κ⁻¹) / (1 - κ⁻¹)) by linarith)

/-
/-- The exact Algorithm 1 degree is bounded by the logarithmic condition-number envelope. -/
theorem theorem1_query_degree (κ η : ℝ) (hκ : 1 < κ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (algorithm1Degree κ η : ℝ)
      ≤ (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ) := by
  have hk : 0 < κ := by linarith
  have hden := filter_arcosh_lower κ hκ
  have hden0 : 0 < Real.arcosh ((1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ))) :=
    lt_of_lt_of_le (by positivity : 0 < 2 / κ) hden
  have hlog : 0 ≤ Real.log (2 / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη0]
    linarith
  have hratio : Real.arcosh η⁻¹ /
      Real.arcosh ((1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ))) ≤
      κ / 2 * Real.log (2 / η) := by
    calc _ ≤ Real.log (2 / η) /
        Real.arcosh ((1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ))) :=
        div_le_div_of_nonneg_right (arcosh_inv_upper η hη0) hden0.le
      _ ≤ Real.log (2 / η) / (2 / κ) :=
        div_le_div_of_nonneg_left hlog (by positivity) hden
      _ = κ / 2 * Real.log (2 / η) := by field_simp
  unfold algorithm1Degree
  exact_mod_cast Nat.ceil_mono hratio
-/

end Qatlib.Papers.QLinearSolver24.MainResults.TheoremOneCorollaryOne
