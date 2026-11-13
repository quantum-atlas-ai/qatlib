/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.H1Diff
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.H2.Diff
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.LocallyConstant

/-!
# Holomorphicity of the Dixon function

This module combines the differentiability of the Dixon components with local vanishing of
winding numbers to prove that `dixonFunction` is entire. The null-homology form applies to
closed curves differentiable outside a countable set and supports the contour calculus for
[WangEtAl2026].

## Main statements

* `cauchy_integrand_intervalIntegrable`: integrability away from the pole.
* `differentiable_dixonFunction`: entirety under null-homology.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Interval Topology

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ} {w : ℂ}

/-- The Cauchy contour integrand is interval integrable when the curve and function are
continuous, the derivative is integrable, and the pole is avoided. -/
theorem cauchy_integrand_intervalIntegrable (hf : ContinuousOn f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b :=
  hderiv_int.continuousOn_mul (((hf.comp hγ_cont hγU).div
    (hγ_cont.sub continuousOn_const) fun t ht ↦ sub_ne_zero.mpr (hoff t ht)))

/-- At an avoided point with winding number zero, the Dixon function equals `dixonH2` under the
stated continuity and integrability assumptions. -/
theorem dixonFunction_eq_dixonH2_of_windingNumber_zero (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hwn : windingNumber γ a b w = 0) :
    dixonFunction f U γ a b w = dixonH2 f γ a b w := by
  by_cases hw : w ∈ U
  · rw [dixonFunction_eq_dixonH1 hw, dixonH1_eq_dixonH2_sub_windingNumber_mul_f hγ_cont hoff
      h_cauchy_int (intervalIntegrable_inv_sub_mul_deriv hγ_cont hoff hderiv_int), hwn]
    ring
  · rw [dixonFunction_eq_dixonH2 hw]

/-- The Dixon function is entire when every point outside the holomorphic domain has a
neighborhood avoiding the curve with winding number zero. -/
private theorem differentiable_dixonFunction_of_windingNumber_zero_near (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (h_local : ∀ w ∉ U, ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0) :
    Differentiable ℂ (dixonFunction f U γ a b) := by
  intro w
  by_cases hw : w ∈ U
  · refine ((differentiableOn_dixonH1 hU hf hγ_cont hγU hderiv_int).differentiableAt
      (hU.mem_nhds hw)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hw] with w' hw' using dixonFunction_eq_dixonH1 hw'
  · have hoff : ∀ t ∈ uIcc a b, γ t ≠ w := fun t ht heq ↦ hw (heq ▸ hγU t ht)
    obtain ⟨ε, hε_pos, h_ball⟩ := h_local w hw
    refine (hasDerivAt_dixonH2 hγ_cont hoff
      (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int
        hoff)).differentiableAt.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
    obtain ⟨hoff', hwz'⟩ := h_ball w' hw'
    exact dixonFunction_eq_dixonH2_of_windingNumber_zero hγ_cont hderiv_int
      (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int hoff') hoff' hwz'

/-- The Dixon function is entire for a closed curve null-homologous in the holomorphic domain,
assuming an integrable derivative and differentiability outside a countable exceptional set. -/
theorem differentiable_dixonFunction (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) :
    Differentiable ℂ (dixonFunction f U γ a b) :=
  differentiable_dixonFunction_of_windingNumber_zero_near hU hf hγ_cont hγU hderiv_int
    fun w hw ↦ exists_ball_windingNumber_zero hclosed hP hγ_cont hγ_diff hderiv_int
      (fun t ht heq ↦ hw (heq ▸ hγU t ht)) ((isNullHomologous_iff.mp h_null) w hw)

end

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
