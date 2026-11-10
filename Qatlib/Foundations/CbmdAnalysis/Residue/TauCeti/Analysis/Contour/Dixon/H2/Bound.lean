/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.IntegralBound
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set Filter

open scoped Real Interval Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}

theorem dixonH2_norm_le {R M : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM : ∀ t ∈ uIcc a b, ‖f (γ t) * deriv γ t‖ ≤ M)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ a b w‖ ≤ M / (‖w‖ - R) * |b - a| := by
  rw [dixonH2_def]
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM a Set.left_mem_uIcc)
  have h_ptwise : ∀ t ∈ Set.uIoc a b,
      ‖f (γ t) / (γ t - w) * deriv γ t‖ ≤ M / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht_ui
    have h_dist_lb : ‖w‖ - R ≤ ‖γ t - w‖ := by
      linarith [norm_sub_norm_le w (γ t), norm_sub_rev w (γ t), hR t ht]
    rw [show f (γ t) / (γ t - w) * deriv γ t = f (γ t) * deriv γ t / (γ t - w) by ring, norm_div]
    gcongr
    exact hM t ht
  exact intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise

private theorem tendsto_zero_cocompact_of_norm_le_div {F : ℂ → ℂ} {R C : ℝ}
    (hbound : ∀ w : ℂ, R < ‖w‖ → ‖F w‖ ≤ C / (‖w‖ - R)) :
    Tendsto F (cocompact ℂ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  filter_upwards [(isCompact_closedBall (0 : ℂ)
      (max R (R + C / ε))).compl_mem_cocompact] with w hw
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
  have hRw : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  calc ‖F w‖ ≤ C / (‖w‖ - R) := hbound w hRw
    _ < ε := by
        rw [div_lt_iff₀ hpos]
        have h2 : C / ε < ‖w‖ - R := by
          linarith [lt_of_le_of_lt (le_max_right _ _) hw]
        rw [div_lt_iff₀ hε] at h2
        linarith [mul_comm ε (‖w‖ - R)]

theorem dixonH2_tendsto_zero {R M : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM : ∀ t ∈ uIcc a b, ‖f (γ t) * deriv γ t‖ ≤ M) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) := by
  refine tendsto_zero_cocompact_of_norm_le_div (R := R) (C := M * |b - a|) fun w hw ↦ ?_
  rw [← div_mul_eq_mul_div]
  exact dixonH2_norm_le hR hM hw

theorem dixonH2_norm_le_of_integrable {R : ℝ} (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R)
    (hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b) {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ a b w‖ ≤ (∫ t in Ι a b, ‖f (γ t) * deriv γ t‖) / (‖w‖ - R) := by
  have hcongr : (∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t)
      = ∫ t in a..b, (γ t - w)⁻¹ • (f (γ t) * deriv γ t) :=
    intervalIntegral.integral_congr fun t _ ↦ by rw [smul_eq_mul]; ring
  rw [dixonH2_def, hcongr]
  exact norm_integral_inv_sub_smul_le hg hR hw

theorem dixonH2_tendsto_zero_of_integrable {R : ℝ} (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R)
    (hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) :=
  tendsto_zero_cocompact_of_norm_le_div fun _ hw ↦ dixonH2_norm_le_of_integrable hR hg hw

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
