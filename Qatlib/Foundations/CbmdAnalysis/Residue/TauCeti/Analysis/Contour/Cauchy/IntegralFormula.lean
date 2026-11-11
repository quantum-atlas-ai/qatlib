/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Dixon.Def

/-!
# Cauchy formulas from the Dixon function

This module extracts Cauchy integral identities from the vanishing of `dixonFunction`. It
identifies `dixonH2` with a winding-number multiple of the function value and derives a
zero-integral criterion, forming part of the contour calculus supporting [WangEtAl2026].

## Main statements

* `dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero`: the winding-number Cauchy formula.
* `intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero`: a vanishing contour integral
  criterion.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- If the Dixon function vanishes at `w`, its Cauchy integral component equals `2πi *
windingNumber γ a b w * f w`, under the stated integrability and avoidance assumptions. -/
theorem dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {w : ℂ} (h_cont : ContinuousOn γ (uIcc a b)) (hw : w ∈ U)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (h_zero_at : dixonFunction f U γ a b w = 0)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w := by
  rw [dixonFunction_eq_dixonH1 hw] at h_zero_at
  have h_identity := dixonH1_eq_dixonH2_sub_windingNumber_mul_f h_cont hoff h_cauchy_int h_base_int
  rw [h_zero_at] at h_identity
  exact sub_eq_zero.mp h_identity.symm

/-- The contour integral of `f` vanishes when the Dixon function for `(z - w₀) * f z` vanishes
at an avoided point `w₀` and the relevant integrands are integrable. -/
theorem intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero {f : ℂ → ℂ} {U : Set ℂ}
    {γ : ℝ → ℂ} {a b : ℝ} (h_cont : ContinuousOn γ (uIcc a b)) (w₀ : ℂ) (hw₀_in_U : w₀ ∈ U)
    (hw₀_off : ∀ t ∈ uIcc a b, γ t ≠ w₀)
    (h_zero_at : dixonFunction (fun z ↦ (z - w₀) * f z) U γ a b w₀ = 0)
    (h_int : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w₀)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have key : ∀ t ∈ uIcc a b,
      (γ t - w₀) * f (γ t) / (γ t - w₀) * deriv γ t = deriv γ t • f (γ t) := fun t ht ↦ by
    rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr (hw₀_off t ht)), smul_eq_mul, mul_comm]
  have h_cif := dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero
    (f := fun z ↦ (z - w₀) * f z) h_cont hw₀_in_U hw₀_off h_zero_at
    (h_int.congr fun t ht ↦ (key t (uIoc_subset_uIcc ht)).symm) h_base_int
  simp only [sub_self, zero_mul, mul_zero] at h_cif
  rw [dixonH2_def] at h_cif
  rw [← h_cif]
  exact intervalIntegral.integral_congr fun t ht ↦ (key t ht).symm

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
