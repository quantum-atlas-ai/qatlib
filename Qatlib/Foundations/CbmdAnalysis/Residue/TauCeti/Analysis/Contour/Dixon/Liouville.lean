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

/-!
# Vanishing of the Dixon function

This module shows that `dixonFunction` agrees with its decaying Cauchy component near infinity.
Combining decay with holomorphicity and Liouville's theorem proves its vanishing for
null-homologous closed curves, completing a step toward the contour identities supporting
[WangEtAl2026].

## Main statements

* `dixonFunction_tendsto_zero`: decay of the Dixon function at infinity.
* `dixonFunction_eq_zero`: vanishing under null-homology.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set Filter

open scoped Real Interval Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}

/-- For a closed continuous curve with integrable derivative and a countable differentiability
exceptional set, the Dixon function equals `dixonH2` outside a compact set. -/
private theorem dixonFunction_eventually_eq_dixonH2 (hf : ContinuousOn f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t) :
    dixonFunction f U γ a b =ᶠ[cocompact ℂ] dixonH2 f γ a b := by
  filter_upwards [windingNumber_eventually_zero_cocompact hclosed hP hγ_cont hγ_diff hderiv_int]
    with w ⟨hoff, hwn⟩
  exact dixonFunction_eq_dixonH2_of_windingNumber_zero hγ_cont hderiv_int
    (cauchy_integrand_intervalIntegrable hf hγ_cont hγU hderiv_int hoff) hoff hwn

/-- Under curve continuity, closure, and derivative integrability, the Dixon function tends to
zero at infinity when the function is continuous on the domain containing the curve. -/
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

/-- The Dixon function vanishes everywhere for a holomorphic function and a closed
null-homologous curve satisfying the stated regularity and integrability assumptions. -/
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
