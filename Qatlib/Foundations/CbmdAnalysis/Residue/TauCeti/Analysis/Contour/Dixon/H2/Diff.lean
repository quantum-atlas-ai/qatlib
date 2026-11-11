/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.Distance
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Differentiating the second Dixon component

This module differentiates the Cauchy integral component `dixonH2` with respect to a pole
outside the curve trace. Kernel continuity and measurability lemmas support the
squared-denominator derivative formula used in the contour calculus for [WangEtAl2026].

## Main statements

* `h2_pole_hasDerivAt`: the reciprocal-kernel derivative.
* `hasDerivAt_dixonH2`: differentiation of the Cauchy integral.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- The derivative with respect to `w` of `(z - w)⁻¹ * c` is `(z - w)⁻² * c` when `z ≠ w`. -/
private theorem h2_pole_hasDerivAt (c z w : ℂ) (hne : z - w ≠ 0) :
    HasDerivAt (fun w' ↦ (z - w')⁻¹ * c) ((z - w)⁻¹ ^ 2 * c) w :=
  ((((hasDerivAt_id' w).const_sub z).inv hne).congr_deriv (by rw [inv_pow]; ring)).mul_const c

/-- The reciprocal Cauchy kernel along a continuous curve is continuous when its pole is
avoided. -/
private theorem h2_kernel_continuousOn (hγ_cont : ContinuousOn γ (uIcc a b)) {w' : ℂ}
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w') : ContinuousOn (fun t ↦ (γ t - w')⁻¹) (uIcc a b) :=
  (hγ_cont.sub continuousOn_const).inv₀ fun t ht ↦ sub_ne_zero.mpr (hoff t ht)

/-- Multiplying the contour numerator by a continuous scalar factor preserves almost everywhere
strong measurability on the integration interval. -/
private theorem h2_factor_mul_num_aestronglyMeasurable {g : ℝ → ℂ} (hg : ContinuousOn g (uIcc a b))
    (hnum : AEStronglyMeasurable (fun t ↦ f (γ t) * deriv γ t) (volume.restrict (Ι a b))) :
    AEStronglyMeasurable (fun t ↦ g t * (f (γ t) * deriv γ t)) (volume.restrict (Ι a b)) :=
  ((hg.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc).mul hnum

/-- Away from the curve, the derivative of `dixonH2` is the contour integral with denominator
`(γ t - w)²`, assuming continuity and integrability of the original Cauchy integrand. -/
theorem hasDerivAt_dixonH2 (hγ_cont : ContinuousOn γ (uIcc a b))
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b) :
    HasDerivAt (dixonH2 f γ a b) (∫ t in a..b, f (γ t) / (γ t - w) ^ 2 * deriv γ t) w := by
  obtain ⟨ε, hε_pos, h_dist_lb⟩ := exists_ball_dist_curve_lower_bound hγ_cont hoff
  have avoid : ∀ w' ∈ Metric.ball w ε, ∀ t ∈ uIcc a b, γ t ≠ w' := fun w' hw' t ht ↦
    sub_ne_zero.mp (norm_pos_iff.mp (hε_pos.trans_le (h_dist_lb w' hw' t ht)))

  have h_factor_cont : ContinuousOn (fun t ↦ γ t - w) (uIcc a b) := hγ_cont.sub continuousOn_const
  have h_num_int : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
    (intervalIntegrable_congr fun t ht ↦ by
      have hne : γ t - w ≠ 0 := sub_ne_zero.mpr (hoff t (uIoc_subset_uIcc ht))
      field_simp).mp (h_cauchy_int.continuousOn_mul h_factor_cont)
  have hnum := (intervalIntegrable_iff.mp h_num_int).aestronglyMeasurable
  have h_eq : dixonH2 f γ a b = fun w' ↦ ∫ t in a..b, (γ t - w')⁻¹ * (f (γ t) * deriv γ t) := by
    funext w'
    rw [dixonH2_def]
    exact intervalIntegral.integral_congr fun t _ ↦ by ring
  have h_deriv : ∫ t in a..b, f (γ t) / (γ t - w) ^ 2 * deriv γ t =
      ∫ t in a..b, (γ t - w)⁻¹ ^ 2 * (f (γ t) * deriv γ t) :=
    intervalIntegral.integral_congr fun t _ ↦ by rw [div_eq_mul_inv, ← inv_pow]; ring
  rw [h_eq, h_deriv]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w' t ↦ (γ t - w')⁻¹ * (f (γ t) * deriv γ t))
    (F' := fun w' t ↦ (γ t - w')⁻¹ ^ 2 * (f (γ t) * deriv γ t))
    (bound := fun t ↦ ε⁻¹ ^ 2 * ‖f (γ t) * deriv γ t‖)
    (Metric.ball_mem_nhds w hε_pos) ?_
    (h_num_int.continuousOn_mul (h2_kernel_continuousOn hγ_cont hoff))
    (h2_factor_mul_num_aestronglyMeasurable ((h2_kernel_continuousOn hγ_cont hoff).pow 2) hnum)
    (Filter.Eventually.of_forall fun t ht w' hw' ↦ by
      rw [norm_mul, norm_pow, norm_inv]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
          (inv_le_inv₀ (hε_pos.trans_le (h_dist_lb w' hw' t (uIoc_subset_uIcc ht)))
            hε_pos |>.mpr (h_dist_lb w' hw' t (uIoc_subset_uIcc ht))) 2)
        (norm_nonneg _))
    (h_num_int.norm.const_mul (ε⁻¹ ^ 2))
    (Filter.Eventually.of_forall fun t ht w' hw' ↦ h2_pole_hasDerivAt (f (γ t) * deriv γ t) (γ t)
      w' (sub_ne_zero.mpr (avoid w' hw' t (uIoc_subset_uIcc ht))))).2
  filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
  exact h2_factor_mul_num_aestronglyMeasurable (h2_kernel_continuousOn hγ_cont (avoid w' hw')) hnum

end

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
