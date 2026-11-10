/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.IntegralBound
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Topology Interval

namespace TauCeti.Contour

private theorem norm_inv_two_pi_I : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
  rw [norm_inv, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I from
      by push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

private theorem windingNumber_eq_zero_of_far {γ : ℝ → ℂ} {a b R : ℝ} {w : ℂ}
    (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hint : ∃ n : ℤ, windingNumber γ a b w = n)
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hw : R + (∫ t in Ι a b, ‖deriv γ t‖) / (2 * Real.pi) < ‖w‖) :
    windingNumber γ a b w = 0 := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD_nonneg : 0 ≤ ∫ t in Ι a b, ‖deriv γ t‖ := integral_nonneg fun _ => norm_nonneg _
  have hwR : R < ‖w‖ :=
    lt_of_le_of_lt (le_add_of_nonneg_right (div_nonneg hD_nonneg h2pi_pos.le)) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_off : ∀ t ∈ uIcc a b, γ t ≠ w := fun t ht heq => by
    have h := hR t ht; rw [heq] at h; linarith
  obtain ⟨n, hn⟩ := hint
  have h_norm_wind : ‖windingNumber γ a b w‖
      ≤ (2 * Real.pi)⁻¹ * ((∫ t in Ι a b, ‖deriv γ t‖) / (‖w‖ - R)) := by
    rw [windingNumber_eq_integral_of_avoidance hγ_cont h_off
        (intervalIntegrable_inv_sub_mul_deriv hγ_cont h_off hderiv_int),
      norm_mul, norm_inv_two_pi_I]
    gcongr
    simpa only [smul_eq_mul] using norm_integral_inv_sub_smul_le hderiv_int
      (fun t ht ↦ hR t (uIoc_subset_uIcc ht)) hwR
  have h_lt_one : (2 * Real.pi)⁻¹ * ((∫ t in Ι a b, ‖deriv γ t‖) / (‖w‖ - R)) < 1 := by
    have key : (∫ t in Ι a b, ‖deriv γ t‖) / (2 * Real.pi) < ‖w‖ - R := by
      rw [lt_sub_iff_add_lt]; linarith
    rw [inv_mul_eq_div, div_div, div_lt_one (mul_pos hpos h2pi_pos)]
    exact (div_lt_iff₀ h2pi_pos).mp key
  have h_abs : |(n : ℝ)| < 1 := by
    have h := lt_of_le_of_lt h_norm_wind h_lt_one
    rwa [hn, Complex.norm_intCast] at h
  rw [hn, show n = 0 from Int.abs_lt_one_iff.mp (by exact_mod_cast h_abs), Int.cast_zero]

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.ContinuousOn.windingNumber_eventually_zero_cocompact_of_integer
    {γ : ℝ → ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hint : ∀ w, w ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b w = n) :
    ∀ᶠ w in Filter.cocompact ℂ,
      w ∉ γ '' uIcc a b ∧ windingNumber γ a b w = 0 := by
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hγ_cont
  have hD_nonneg : 0 ≤ ∫ t in Ι a b, ‖deriv γ t‖ := integral_nonneg fun _ => norm_nonneg _
  set RR : ℝ := R + (∫ t in Ι a b, ‖deriv γ t‖) / (2 * Real.pi) with hRR_def
  have hR_le_RR : R ≤ RR := le_add_of_nonneg_right (div_nonneg hD_nonneg (by positivity))
  have h_mem : {w : ℂ | RR < ‖w‖} ∈ Filter.cocompact ℂ := by
    rw [Filter.mem_cocompact]
    exact ⟨Metric.closedBall 0 RR, isCompact_closedBall 0 RR, fun w hw => by
      simpa [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hw⟩
  filter_upwards [h_mem] with w (hw : RR < ‖w‖)
  have hoff : ∀ t ∈ uIcc a b, γ t ≠ w := by
    intro t ht heq
    have h := hR t ht
    rw [heq] at h
    linarith [lt_of_le_of_lt hR_le_RR hw]
  have hwtrace : w ∉ γ '' uIcc a b := by
    simpa only [mem_image, not_exists, not_and] using hoff
  exact ⟨hwtrace, windingNumber_eq_zero_of_far hγ_cont hderiv_int
    (hint w hwtrace) hR (hRR_def ▸ hw)⟩

theorem windingNumber_eventually_zero_cocompact {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ uIcc a b, γ t ≠ w) ∧ windingNumber γ a b w = 0 := by
  have hac := ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hγ_cont hP
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) hderiv_int
  simpa only [mem_image, not_exists, not_and] using
    (ContinuousOn.windingNumber_eventually_zero_cocompact_of_integer hγ_cont hderiv_int
      (fun _ hz ↦ AbsolutelyContinuousOnInterval.exists_int_windingNumber hac hclosed hz))

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
