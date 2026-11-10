/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.FunctionDiff
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.H2.Bound
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Vanishing
import Mathlib.Analysis.Complex.Liouville
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set Filter

open scoped Real Interval Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}

private theorem dixonFunction_eventually_eq_dixonH2 (hf : ContinuousOn f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t) :
    dixonFunction f U γ a b =ᶠ[cocompact ℂ] dixonH2 f γ a b := by
  filter_upwards [windingNumber_eventually_zero_cocompact hclosed hP hγ_cont hγ_diff hderiv_int]
    with w ⟨hoff, hwn⟩
  exact dixonFunction_eq_dixonH2_of_windingNumber_zero hγ_cont hderiv_int
    (cauchy_integrand_intervalIntegrable hf hγ_cont hγU hderiv_int hoff) hoff hwn

private theorem dixonFunction_tendsto_zero (hf : ContinuousOn f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t) :
    Tendsto (dixonFunction f U γ a b) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hγ_cont
  have hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
    hderiv_int.continuousOn_mul (hf.comp hγ_cont hγU)
  exact (dixonH2_tendsto_zero_of_integrable (fun t ht ↦ hR t (uIoc_subset_uIcc ht)) hg).congr'
    (dixonFunction_eventually_eq_dixonH2 hf hγ_cont hγU hderiv_int hclosed hP hγ_diff).symm

theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (w : ℂ) : dixonFunction f U γ a b w = 0 := by
  have h_entire :=
    differentiable_dixonFunction hU hf hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null
  exact h_entire.apply_eq_of_tendsto_cocompact w
    (dixonFunction_tendsto_zero hf.continuousOn hγ_cont hγU hderiv_int hclosed hP hγ_diff)

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
