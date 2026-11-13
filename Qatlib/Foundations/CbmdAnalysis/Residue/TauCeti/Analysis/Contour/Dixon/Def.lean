/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.Calculus.DSlope

/-!
# Identities for the Dixon contour function

This module relates the two components `dixonH1` and `dixonH2` through a winding-number
correction and identifies the branches of `dixonFunction`. These algebraic contour identities
support the Cauchy and residue arguments used for [WangEtAl2026].

## Main statements

* `dixonH1_eq_dixonH2_sub_windingNumber_mul_f`: the winding-number relation between the
  components.
* `dixonFunction_eq_dixonH1`: the branch on the domain.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

noncomputable irreducible_def dixonH1 (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in a..b, dslope f w (γ t) * deriv γ t

noncomputable irreducible_def dixonH2 (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t

open Classical in

noncomputable irreducible_def dixonFunction (f : ℂ → ℂ) (U : Set ℂ) (γ : ℝ → ℂ) (a b : ℝ)
    (w : ℂ) : ℂ :=
  if w ∈ U then dixonH1 f γ a b w else dixonH2 f γ a b w

/-- Away from `w`, the divided-difference contour integrand is the difference of the Cauchy
integrands with numerators `f (γ t)` and `f w`. -/
private theorem dslope_integrand_eq {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∀ t ∈ uIcc a b, dslope f w (γ t) * deriv γ t =
      f (γ t) / (γ t - w) * deriv γ t - f w / (γ t - w) * deriv γ t := fun t ht ↦ by
  rw [dslope_of_ne _ (hoff t ht), slope_def_field]; ring

/-- Factors the constant value `f w` out of the reciprocal-kernel contour integrand. -/
private theorem fw_div_eq (f : ℂ → ℂ) (γ : ℝ → ℂ) (w : ℂ) :
    (fun t ↦ f w / (γ t - w) * deriv γ t) = fun t ↦ f w * ((γ t - w)⁻¹ * deriv γ t) := by
  funext t; rw [div_eq_mul_inv, mul_assoc]

/-- The divided-difference integral `dixonH1` equals `dixonH2` minus `2πi` times the winding
number and `f w`, under avoidance and integrability assumptions. -/
theorem dixonH1_eq_dixonH2_sub_windingNumber_mul_f {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (h_cont : ContinuousOn γ (uIcc a b)) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    dixonH1 f γ a b w =
      dixonH2 f γ a b w - 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w := by
  have hw_int : ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t =
      2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w := by
    rw [windingNumber_eq_integral_of_avoidance h_cont hoff h_base_int, ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  have h_fw_div_int : IntervalIntegrable (fun t ↦ f w / (γ t - w) * deriv γ t) volume a b :=
    (fw_div_eq f γ w) ▸ (h_base_int.const_mul (f w))
  rw [dixonH1_def, dixonH2_def, intervalIntegral.integral_congr (dslope_integrand_eq hoff),
    intervalIntegral.integral_sub h_cauchy_int h_fw_div_int, fw_div_eq,
    intervalIntegral.integral_const_mul, hw_int]
  ring

/-- Inside `U`, the Dixon function equals its divided-difference component `dixonH1`. -/
@[simp]
theorem dixonFunction_eq_dixonH1 {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hw : w ∈ U) : dixonFunction f U γ a b w = dixonH1 f γ a b w := by
  rw [dixonFunction_def, if_pos hw]

/-- Outside `U`, the Dixon function equals its Cauchy integral component `dixonH2`. -/
@[simp]
theorem dixonFunction_eq_dixonH2 {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hw : w ∉ U) : dixonFunction f U γ a b w = dixonH2 f γ a b w := by
  rw [dixonFunction_def, if_neg hw]

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
