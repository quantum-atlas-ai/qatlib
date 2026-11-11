/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic

/-!
# Principal-value winding numbers and null homology

Defines `windingNumber` by a normalized Cauchy principal value and `IsNullHomologous` by
vanishing winding numbers outside a set. The module proves curve congruence rules and the
ordinary integral formula under avoidance and integrability hypotheses.

These definitions supply scalar contour tools for the analysis associated with [WangEtAl2026].

## Main statements

* `windingNumber`: The complex winding number defined as the Cauchy principal value of `(z -
  z₀)⁻¹` along the curve, divided by `2πi`.
* `IsNullHomologous`: Null homology in `Ω`, expressed as vanishing winding number at every point
  outside `Ω`.
* `windingNumber_eq_integral_of_avoidance`: For a continuous curve avoiding `z₀`, an
  interval-integrable logarithmic derivative computes the winding number by the ordinary
  integral divided by `2πi`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

open Filter Topology MeasureTheory

namespace TauCeti.Contour

/-- The complex winding number defined as the Cauchy principal value of `(z - z₀)⁻¹` along the
curve, divided by `2πi`. -/
def windingNumber (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀

/-- Unfolds the winding number as a normalized Cauchy principal value. -/
theorem windingNumber_eq_cauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    windingNumber γ a b z₀ =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀ :=
  (rfl)

/-- Computes the winding number from a specified Cauchy principal value. -/
theorem windingNumber_eq_of_hasCauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀ L) :
    windingNumber γ a b z₀ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L := by
  rw [windingNumber_eq_cauchyPVAt, h.cauchyPVAt_eq]

/-- The winding number over an interval with equal endpoints is zero. -/
@[simp]
theorem windingNumber_same (γ : ℝ → ℂ) (a : ℝ) (z₀ : ℂ) :
    windingNumber γ a a z₀ = 0 := by
  rw [windingNumber_eq_cauchyPVAt, cauchyPVAt_same, mul_zero]

/-- The winding number of a constant curve is zero. -/
@[simp]
theorem windingNumber_const (x : ℂ) (a b : ℝ) (z : ℂ) :
    windingNumber (fun _ : ℝ => x) a b z = 0 := by
  have hpv :
      HasCauchyPVAt (fun _ : ℝ => x) a b (fun w => (w - z)⁻¹) z 0 := by
    refine HasCauchyPVAt.intro ?_ ?_
    · filter_upwards with ε
      simp only [deriv_const, mul_zero, ite_self]
      exact IntervalIntegrable.zero
    · simpa only [deriv_const, mul_zero, ite_self, intervalIntegral.integral_zero] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
  rw [windingNumber_eq_of_hasCauchyPVAt hpv, mul_zero]

/-- The winding number is unchanged when curves agree almost everywhere and their derivatives
agree almost everywhere away from the reference point. -/
theorem windingNumber_congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_eq : γ₁ =ᵐ[volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    windingNumber γ₁ a b z₀ = windingNumber γ₂ a b z₀ := by
  rw [windingNumber_eq_cauchyPVAt, windingNumber_eq_cauchyPVAt,
    cauchyPVAt_congr_curve_ae h_eq h_deriv]

/-- Curves equal on the open interval between the endpoints have the same winding number. -/
theorem windingNumber_congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    windingNumber γ₁ a b z₀ = windingNumber γ₂ a b z₀ := by
  rw [windingNumber_eq_cauchyPVAt, windingNumber_eq_cauchyPVAt, cauchyPVAt_congr_curve h_eq]

/-- The winding number is zero when the two integration endpoints coincide. -/
theorem windingNumber_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (z₀ : ℂ) :
    windingNumber γ a b z₀ = 0 := by
  subst hab
  exact windingNumber_same γ a z₀

/-- Null homology in `Ω`, expressed as vanishing winding number at every point outside `Ω`. -/
def IsNullHomologous (γ : ℝ → ℂ) (a b : ℝ) (Ω : Set ℂ) : Prop :=
  ∀ w ∉ Ω, windingNumber γ a b w = 0

/-- Characterizes null homology by vanishing winding numbers outside the set. -/
theorem isNullHomologous_iff {γ : ℝ → ℂ} {a b : ℝ} {Ω : Set ℂ} :
    IsNullHomologous γ a b Ω ↔ ∀ w ∉ Ω, windingNumber γ a b w = 0 :=
  Iff.rfl

/-- For a continuous curve avoiding `w` with interval-integrable derivative, the logarithmic
derivative about `w` is interval integrable. -/
theorem intervalIntegrable_inv_sub_mul_deriv {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b)) (hoff : ∀ t ∈ Set.uIcc a b, γ t ≠ w)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b :=
  hderiv_int.continuousOn_mul ((hγ_cont.sub continuousOn_const).inv₀
    fun t ht ↦ sub_ne_zero.mpr (hoff t ht))

/-- For a continuous curve avoiding `z₀`, an interval-integrable logarithmic derivative computes
the winding number by the ordinary integral divided by `2πi`. -/
theorem windingNumber_eq_integral_of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b)) (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => (γ t - z₀)⁻¹ * deriv γ t) volume a b) :
    windingNumber γ a b z₀
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t :=
  windingNumber_eq_of_hasCauchyPVAt (HasCauchyPVAt.of_avoidance h_cont h_avoid hf_int)

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
