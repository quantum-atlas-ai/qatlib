/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.DSlope.Continuous
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Differentiability of the first Dixon component

This module proves that the divided-difference integral `dixonH1` is holomorphic on the
function's open domain. Measurability and uniform derivative estimates justify differentiation
under the integral, supplying a step of the Dixon contour argument supporting [WangEtAl2026].

## Main statements

* `dslope_deriv_product_norm_bound`: domination of the differentiated integrand.
* `differentiableOn_dixonH1`: holomorphicity of the first Dixon component.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Interval Topology

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w₀ : ℂ}

/-- For holomorphic `f`, differentiating the divided difference in its first argument agrees
with differentiating the swapped divided difference. -/
private theorem dslope_first_arg_hasDerivAt (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {c w : ℂ}
    (hc : c ∈ U) (hw : w ∈ U) :
    HasDerivAt (fun w' ↦ dslope f w' c) (deriv (dslope f c) w) w :=
  (((Complex.differentiableOn_dslope (hU.mem_nhds hc)).mpr hf w hw).differentiableAt
    (hU.mem_nhds hw)).hasDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ dslope_comm f _ _)

/-- A holomorphic divided difference composed with a continuous curve in its domain is
continuous in the curve parameter. -/
private theorem dslope_comp_curve_continuousOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) {w : ℂ} (hw : w ∈ U) :
    ContinuousOn (fun t ↦ dslope f w (γ t)) (uIcc a b) :=
  ((continuousOn_dslope (hU.mem_nhds hw)).mpr
    ⟨hf.continuousOn, hf.differentiableAt (hU.mem_nhds hw)⟩).comp hγ_cont hγU

/-- A continuous scalar factor times the ordinary derivative of a complex curve is almost
everywhere strongly measurable on the integration interval. -/
private theorem factor_mul_deriv_aestronglyMeasurable {g : ℝ → ℂ} (hg : ContinuousOn g (uIcc a b)) :
    AEStronglyMeasurable (fun t ↦ g t * deriv γ t) (volume.restrict (Ι a b)) :=
  ((hg.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc).mul
    (stronglyMeasurable_deriv γ).aestronglyMeasurable

/-- An open neighborhood of `w₀` contains `w₀ + s n` for a sequence of nonzero increments
tending to zero. -/
private theorem exists_seq_ne_add_mem_tendsto (hU : IsOpen U) (hw₀ : w₀ ∈ U) :
    ∃ s : ℕ → ℂ, (∀ n, s n ≠ 0) ∧ (∀ n, w₀ + s n ∈ U) ∧
      Filter.Tendsto s Filter.atTop (𝓝 0) := by
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  refine ⟨fun n ↦ ((ρ / 2 / ((n : ℝ) + 1) : ℝ) : ℂ), fun n ↦ ?_, fun n ↦ ?_, ?_⟩
  · simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  · refine hρ_sub ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith [div_le_self (a := ρ / 2) (by linarith)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) ≤ (n : ℝ) + 1)]
  · have h_real : Filter.Tendsto (fun n : ℕ ↦ ρ / 2 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop).const_mul
          (ρ / 2)
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h_real
    rwa [Complex.ofReal_zero] at h

/-- The divided-difference difference quotient times the curve derivative is almost everywhere
strongly measurable under the holomorphicity and curve continuity assumptions. -/
private theorem dslope_diffquot_aestronglyMeasurable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hw₀ : w₀ ∈ U) {s : ℂ}
    (hs : w₀ + s ∈ U) :
    AEStronglyMeasurable
      (fun t ↦ (dslope f (γ t) (w₀ + s) - dslope f (γ t) w₀) / s * deriv γ t)
      (volume.restrict (Ι a b)) := by
  refine factor_mul_deriv_aestronglyMeasurable (ContinuousOn.div_const (ContinuousOn.sub ?_ ?_) _)
  · exact (continuousOn_dslope_first_arg (hU.mem_nhds hs) hf.continuousOn
      (hf.differentiableAt (hU.mem_nhds hs))).comp hγ_cont hγU
  · exact (continuousOn_dslope_first_arg (hU.mem_nhds hw₀) hf.continuousOn
      (hf.differentiableAt (hU.mem_nhds hw₀))).comp hγ_cont hγU

/-- The derivative of the divided difference times the curve derivative is almost everywhere
strongly measurable under the holomorphicity and curve continuity assumptions. -/
private theorem dslope_deriv_mul_deriv_aestronglyMeasurable (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hw₀ : w₀ ∈ U) :
    AEStronglyMeasurable (fun t ↦ deriv (dslope f (γ t)) w₀ * deriv γ t)
      (volume.restrict (Ι a b)) := by
  obtain ⟨s, hs_ne, hs_mem, hs_tendsto⟩ := exists_seq_ne_add_mem_tendsto hU hw₀
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n ↦ dslope_diffquot_aestronglyMeasurable hU hf hγ_cont hγU hw₀ (hs_mem n)) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht_uIcc : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht
  have h_diff : DifferentiableAt ℂ (dslope f (γ t)) w₀ :=
    ((Complex.differentiableOn_dslope (hU.mem_nhds (hγU t ht_uIcc))).mpr hf w₀ hw₀).differentiableAt
      (hU.mem_nhds hw₀)
  have hy : Filter.Tendsto (fun n ↦ w₀ + s n) Filter.atTop (𝓝[≠] w₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using hs_tendsto.const_add w₀,
      Filter.Eventually.of_forall fun n h ↦ hs_ne n (add_left_cancel (h.trans (add_zero w₀).symm))⟩
  have h_q_eq : ∀ n, (dslope f (γ t) (w₀ + s n) - dslope f (γ t) w₀) / s n * deriv γ t =
      slope (dslope f (γ t)) w₀ (w₀ + s n) * deriv γ t := fun n ↦ by
    have hsub : w₀ + s n - w₀ = s n := by ring
    rw [slope_def_field, hsub]
  simp_rw [h_q_eq]
  exact (h_diff.hasDerivAt.tendsto_slope.comp hy).mul_const _

/-- A uniform derivative bound for divided differences gives the product bound `C * ‖deriv γ t‖`
on a smaller ball. -/
private theorem dslope_deriv_product_norm_bound {C δ : ℝ}
    (h_dslope_bd : ∀ c ∈ γ '' uIcc a b, ∀ w ∈ Metric.ball w₀ δ, ‖deriv (dslope f c) w‖ ≤ C)
    {ε : ℝ} (hball : Metric.ball w₀ ε ⊆ Metric.ball w₀ δ) :
    ∀ᵐ t, t ∈ Ι a b → ∀ w ∈ Metric.ball w₀ ε,
      ‖deriv (dslope f (γ t)) w * deriv γ t‖ ≤ C * ‖deriv γ t‖ := by
  refine Filter.Eventually.of_forall fun t ht w hw ↦ ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (h_dslope_bd (γ t) ⟨t, Set.uIoc_subset_uIcc ht, rfl⟩ w (hball hw)) (norm_nonneg _)

/-- The integral defining `dixonH1` is complex differentiable at each point of the open
holomorphic domain when the curve derivative is integrable. -/
private theorem differentiableAt_dixonH1_integral (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hw₀ : w₀ ∈ U) :
    DifferentiableAt ℂ (fun w ↦ ∫ t in a..b, dslope f w (γ t) * deriv γ t) w₀ := by
  have hK_compact : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ_cont
  have hK_sub : γ '' uIcc a b ⊆ U := fun _ ⟨t, ht, hz⟩ ↦ hz ▸ hγU t ht
  obtain ⟨C, _, δ, hδ_pos, h_dslope_bd⟩ :=
    deriv_dslope_bounded_on_compact hU hf hK_compact hK_sub hw₀
  obtain ⟨εU, hεU_pos, hεU_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  have hε_pos : 0 < min δ εU := lt_min hδ_pos hεU_pos
  have hball_U : Metric.ball w₀ (min δ εU) ⊆ U :=
    (Metric.ball_subset_ball (min_le_right δ εU)).trans hεU_sub
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w t ↦ dslope f w (γ t) * deriv γ t)
    (F' := fun w t ↦ deriv (dslope f (γ t)) w * deriv γ t)
    (bound := fun t ↦ C * ‖deriv γ t‖) (Metric.ball_mem_nhds w₀ hε_pos) ?_
    (hderiv_int.continuousOn_mul (dslope_comp_curve_continuousOn hU hf hγ_cont hγU hw₀))
    (dslope_deriv_mul_deriv_aestronglyMeasurable hU hf hγ_cont hγU hw₀)
    (dslope_deriv_product_norm_bound h_dslope_bd (Metric.ball_subset_ball (min_le_left δ εU)))
    (hderiv_int.norm.const_mul C) ?_).2.differentiableAt
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    exact factor_mul_deriv_aestronglyMeasurable
      (dslope_comp_curve_continuousOn hU hf hγ_cont hγU (hball_U hw))
  · refine Filter.Eventually.of_forall fun t ht w hw ↦ ?_
    exact (dslope_first_arg_hasDerivAt hU hf (hγU t (Set.uIoc_subset_uIcc ht))
      (hball_U hw)).mul_const (deriv γ t)

/-- The divided-difference component `dixonH1` is holomorphic on the open domain containing the
continuous curve, assuming its derivative is interval integrable. -/
theorem differentiableOn_dixonH1 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    DifferentiableOn ℂ (dixonH1 f γ a b) U := by
  have h_eq : dixonH1 f γ a b = fun w ↦ ∫ t in a..b, dslope f w (γ t) * deriv γ t :=
    funext fun w ↦ dixonH1_def f γ a b w
  rw [h_eq]
  exact fun w₀ hw₀ ↦ (differentiableAt_dixonH1_integral hU hf hγ_cont hγU hderiv_int
    hw₀).differentiableWithinAt

end

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
