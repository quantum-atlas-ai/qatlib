/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QImagingLimit06.MainResults

def fisherInformation (IF : ℝ) : ℝ := IF

noncomputable def cramerRaoResolution (IF : ℝ) : ℝ := 1 / Real.sqrt IF

theorem cramerRao_bound {IF Var pmin : ℝ} (hIF : 0 < IF)
    (hVar : 1 / IF ≤ Var) (hpmin : pmin = Real.sqrt Var) :
    cramerRaoResolution IF ≤ pmin := by
  have hsqrtIF : 0 < Real.sqrt IF := Real.sqrt_pos.mpr hIF
  have hVarpos : 0 < Var := lt_of_lt_of_le (by positivity) hVar
  have hsq : (1 / Real.sqrt IF) ^ 2 = 1 / IF := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hIF)]
  have hle : 1 / Real.sqrt IF ≤ Real.sqrt Var := by
    rw [Real.le_sqrt (by positivity) (le_of_lt hVarpos), hsq]
    exact hVar
  calc cramerRaoResolution IF = 1 / Real.sqrt IF := rfl
    _ ≤ Real.sqrt Var := hle
    _ = pmin := hpmin.symm

theorem sqrt_four : Real.sqrt 4 = (2 : ℝ) := by
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

theorem resolution_intensity_fisher {N a : ℝ} (hN : 0 < N) (ha : 0 < a) :
    cramerRaoResolution ((4 * N) / a ^ 2) = a / (2 * Real.sqrt N) := by
  have h4N : (0 : ℝ) ≤ 4 * N := by positivity
  have hsqrt : Real.sqrt ((4 * N) / a ^ 2) = 2 * Real.sqrt N / a := by
    rw [Real.sqrt_div h4N, Real.sqrt_sq (le_of_lt ha)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) N, sqrt_four]
  unfold cramerRaoResolution
  rw [hsqrt]
  have hden : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have ha' : a ≠ 0 := ha.ne'
  field_simp

theorem resolution_gauss_fisher {N b σ : ℝ} (hN : 0 < N) (hb : 0 < b)
    (hσ : 0 < σ) :
    cramerRaoResolution ((4 * N) / (b ^ 2 * σ ^ 2)) =
      b * σ / (2 * Real.sqrt N) := by
  have h4N : (0 : ℝ) ≤ 4 * N := by positivity
  have hsq : b ^ 2 * σ ^ 2 = (b * σ) ^ 2 := by ring
  have hsqrt : Real.sqrt ((4 * N) / (b ^ 2 * σ ^ 2)) =
      2 * Real.sqrt N / (b * σ) := by
    rw [Real.sqrt_div h4N, hsq, Real.sqrt_sq (by positivity)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) N, sqrt_four]
  unfold cramerRaoResolution
  rw [hsqrt]
  have hden : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hbσ : b * σ ≠ 0 := (mul_pos hb hσ).ne'
  field_simp

theorem pmin_of_snr_one {N c p : ℝ} (hN : 0 < N) (hc : 0 < c) (hp : 0 < p)
    (hSNR : 4 * N * p ^ 2 / c ^ 2 = 1) : p = c / (2 * Real.sqrt N) := by
  have hp2 : p ^ 2 = c ^ 2 / (4 * N) := by
    field_simp at hSNR ⊢
    linarith
  have hroot : Real.sqrt (c ^ 2 / (4 * N)) = p := by
    rw [← Real.sqrt_sq (le_of_lt hp), hp2]
  have hval : Real.sqrt (c ^ 2 / (4 * N)) = c / (2 * Real.sqrt N) := by
    rw [Real.sqrt_div (sq_nonneg c) (4 * N), Real.sqrt_sq (le_of_lt hc),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) N, sqrt_four]
  rw [← hroot, hval]

end Qatlib.Papers.QImagingLimit06.MainResults
