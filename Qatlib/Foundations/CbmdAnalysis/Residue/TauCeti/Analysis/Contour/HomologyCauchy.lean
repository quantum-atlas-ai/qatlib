/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Cauchy.IntegralFormula
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.Distance
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.FunctionDiff
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Liouville

/-!
# Cauchy's theorem for null-homologous curves

This module derives the winding-number Cauchy integral formula and the vanishing contour
integral theorem from the Dixon function. Its final `homologyCauchyTheorem` applies to closed
piecewise C¹ curves null-homologous in an open holomorphic domain, supplying a foundation for
the residue calculus supporting [WangEtAl2026].

## Main statements

* `dixonH2_eq_windingNumber_mul_f_of_nullHomologous`: the winding-number integral formula.
* `homologyCauchyTheorem`: Cauchy's theorem for piecewise C¹ curves.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- For a holomorphic function and a closed null-homologous curve, the Cauchy integral component
equals `2πi` times the winding number and function value at any avoided point in the domain. -/
theorem dixonH2_eq_windingNumber_mul_f_of_nullHomologous {f : ℂ → ℂ} {U : Set ℂ}
    {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ} {w : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (hwU : w ∈ U) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w :=
  dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero hγ_cont hwU hoff
    (dixonFunction_eq_zero hU hf hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null w)
    (cauchy_integrand_intervalIntegrable hf.continuousOn hγ_cont hγU hderiv_int hoff)
    (intervalIntegrable_inv_sub_mul_deriv hγ_cont hoff hderiv_int)

/-- The contour integral of a holomorphic function vanishes along a closed null-homologous curve
with integrable derivative and countably many possible differentiability exceptions, given
an avoided point in the domain. -/
theorem homologyCauchyTheorem_of_point_off_curve {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {P : Set ℝ} {w₀ : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (hw₀U : w₀ ∈ U) (hw₀off : ∀ t ∈ uIcc a b, γ t ≠ w₀) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have hg : DifferentiableOn ℂ (fun z ↦ (z - w₀) * f z) U := by
    fun_prop
  have h_int_mul : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
    hderiv_int.continuousOn_mul (hf.continuousOn.comp hγ_cont hγU)
  have h_int : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b := by
    rw [intervalIntegrable_iff] at h_int_mul ⊢
    exact h_int_mul.congr_fun (fun t _ ↦ by rw [smul_eq_mul, mul_comm]) measurableSet_uIoc
  exact intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero hγ_cont w₀ hw₀U hw₀off
    (dixonFunction_eq_zero hU hg hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null w₀)
    h_int (intervalIntegrable_inv_sub_mul_deriv hγ_cont hw₀off hderiv_int)

/-- The integral of a holomorphic function along a closed piecewise C¹ curve null-homologous in
its open domain is zero. -/
theorem homologyCauchyTheorem {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω) (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_pc1 : IsPiecewiseC1On γ a b) (hγ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hclosed : γ a = γ b)
    (hf : DifferentiableOn ℂ f Ω) (hnull : IsNullHomologous γ a b Ω) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ_pc1.exists_countable_differentiableAt

  have : PathConnectedSpace ℂ := IsTopologicalAddGroup.pathConnectedSpace
  obtain ⟨w₀, hw₀Ω, hw₀off⟩ := exists_mem_off_curve hΩ hγ_pc1.continuousOn hγ
  exact homologyCauchyTheorem_of_point_off_curve hΩ hf hγ_pc1.continuousOn hγ
    hγ_pc1.intervalIntegrable_deriv hclosed hP hγ_diff hnull hw₀Ω hw₀off

end TauCeti.Contour

end

end Qatlib.Foundations.CbmdAnalysis.Residue
