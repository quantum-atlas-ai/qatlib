/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ResolventHomotopy

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! A computational anchor need not belong to the numerical range. Actual
support-plane margins give the whole scalar-anchor homotopy a uniform gap. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc
open Matrix Set
open scoped Matrix.Norms.L2Operator

/-- Construction for halfplane Value in the support anchor separation model. -/
def halfplaneValue (normal center z : ℂ) : ℝ := (star normal*(z-center)).re

/-- The identity or estimate `halfplaneValue_convex` holds with the displayed separation, geometry and norm hypotheses. -/
theorem halfplaneValue_convex (normal center z w : ℂ) (s : ℝ) :
    halfplaneValue normal center ((1-s) • z+s • w) =
      (1-s)*halfplaneValue normal center z+s*halfplaneValue normal center w := by
  simp only [halfplaneValue, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The identity or estimate `halfplaneValue_separation` holds with the displayed separation, geometry and norm hypotheses. -/
theorem halfplaneValue_separation (normal center z w : ℂ) (bound δ : ℝ)
    (hnormal : ‖normal‖ ≤ 1) (hfacet : halfplaneValue normal center z = bound)
    (hw : halfplaneValue normal center w ≤ bound-δ) : δ ≤ ‖z-w‖ := by
  have he : halfplaneValue normal center z-halfplaneValue normal center w =
      (star normal*(z-w)).re := by
    simp only [halfplaneValue, mul_sub, Complex.sub_re]
    ring
  have hl : δ ≤ (star normal*(z-w)).re := by
    rw [← he, hfacet]
    linarith
  have hn : ‖star normal*(z-w)‖ ≤ ‖z-w‖ := by
    rw [norm_mul, norm_star]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hnormal (norm_nonneg (z-w))
  exact hl.trans ((Complex.re_le_norm _).trans hn)

/-- The identity or estimate `halfplaneValue_panel_affine` holds with the displayed separation, geometry and norm hypotheses. -/
theorem halfplaneValue_panel_affine (normal center z₀ u : ℂ) (a h t : ℝ) :
    halfplaneValue normal center (contourPanel z₀ u a h t) =
      halfplaneValue normal center (contourPanel z₀ u a h a)+(t-a)*(star normal*u).re := by
  simp only [halfplaneValue, contourPanel, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- The identity or estimate `halfplaneValue_panel_of_endpoints` holds with the displayed separation, geometry and norm hypotheses. -/
theorem halfplaneValue_panel_of_endpoints (normal center z₀ u : ℂ) (a h bound : ℝ)
    (hh : 0 < h)
    (hstart : halfplaneValue normal center (contourPanel z₀ u a h a) = bound)
    (hend : halfplaneValue normal center (contourPanel z₀ u a h (a+h)) = bound)
    (t : ℝ) : halfplaneValue normal center (contourPanel z₀ u a h t) = bound := by
  have he := halfplaneValue_panel_affine normal center z₀ u a h (a+h)
  rw [hstart, hend] at he
  have hm : h*(star normal*u).re = 0 := by nlinarith
  have hs : (star normal*u).re = 0 := (mul_eq_zero.mp hm).resolve_left hh.ne'
  rw [halfplaneValue_panel_affine, hstart, hs, mul_zero, add_zero]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The identity or estimate `scalarAnchorHomotopy_support_bound` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalarAnchorHomotopy_support_bound (A : Matrix I I ℂ) (q normal center : ℂ)
    (bound δA δq : ℝ)
    (hA : ∀ w ∈ matrixNumericalRange A, halfplaneValue normal center w ≤ bound-δA)
    (hq : halfplaneValue normal center q ≤ bound-δq)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A q s),
      halfplaneValue normal center w ≤ bound-min δA δq := by
  rintro w ⟨x, hx, rfl⟩
  let v := inner ℂ x ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) A) x)
  have hv : v ∈ matrixNumericalRange A := ⟨x, hx, rfl⟩
  have ha : halfplaneValue normal center v ≤ bound-min δA δq :=
    (hA v hv).trans (by linarith [min_le_left δA δq])
  have hq' : halfplaneValue normal center q ≤ bound-min δA δq :=
    hq.trans (by linarith [min_le_right δA δq])
  rw [scalarAnchorHomotopy_rayleigh A q s x hx, halfplaneValue_convex]
  calc
    _ ≤ (1-s)*(bound-min δA δq)+s*(bound-min δA δq) :=
      add_le_add (mul_le_mul_of_nonneg_left hq' (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left ha hs.1)
    _ = bound-min δA δq := by ring

/-- The identity or estimate `scalarAnchorHomotopy_halfplane_separation` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalarAnchorHomotopy_halfplane_separation (A : Matrix I I ℂ)
    (q normal center z : ℂ) (bound δA δq : ℝ)
    (hA : ∀ w ∈ matrixNumericalRange A, halfplaneValue normal center w ≤ bound-δA)
    (hq : halfplaneValue normal center q ≤ bound-δq)
    (hnormal : ‖normal‖ ≤ 1) (hfacet : halfplaneValue normal center z = bound)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A q s), min δA δq ≤ ‖z-w‖ := by
  intro w hw
  have hb := scalarAnchorHomotopy_support_bound A q normal center bound δA δq hA hq s hs w hw
  exact halfplaneValue_separation normal center z w bound (min δA δq) hnormal hfacet hb

/-- Every actual panel stays separated from every intermediate matrix's
numerical range. Only support truth for A and finite anchor/facet data enter. -/
theorem scalarAnchorHomotopy_separation_from_support
    {K J : Type} (A : Matrix I I ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ u : J → ℂ) (a h : J → ℝ) (δA δq : ℝ)
    (hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (hnormal : ∀ k, ‖normal k‖ ≤ 1)
    (hfacet : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      halfplaneValue (normal (facet j)) center (contourPanel (z₀ j) (u j) (a j) (h j) t) = bound (facet j)) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A q s),
        min δA δq ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖ := by
  intro s hs j t ht
  exact scalarAnchorHomotopy_halfplane_separation A q (normal (facet j)) center _ _ δA δq
    (hA (facet j)) (hq (facet j)) (hnormal (facet j)) (hfacet j t ht) s hs

/-- The identity or estimate `scalarAnchorHomotopy_separation_from_support_endpoints` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalarAnchorHomotopy_separation_from_support_endpoints
    {K J : Type} (A : Matrix I I ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ u : J → ℂ) (a h : J → ℝ) (δA δq : ℝ)
    (hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (hnormal : ∀ k, ‖normal k‖ ≤ 1) (hh : ∀ j, 0 < h j)
    (hstart : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j)) = bound (facet j))
    (hend : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j)) = bound (facet j)) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A q s),
        min δA δq ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖ := by
  apply scalarAnchorHomotopy_separation_from_support A q center normal bound facet z₀ u a h δA δq hA hq hnormal
  intro j t _
  exact halfplaneValue_panel_of_endpoints (normal (facet j)) center (z₀ j) (u j)
    (a j) (h j) (bound (facet j)) (hh j) (hstart j) (hend j) t

end Qatlib.Concepts.MatrixContour.ContourCalc
