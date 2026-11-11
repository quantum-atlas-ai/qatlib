/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.SupportAnchorSeparation
import Qatlib.Papers.CrouzeixLS26.LayerDilation.PolygonGaussWinding

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Concepts.MatrixContour.ContourCalc.PolygonWinding
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.PolygonWinding
open Qatlib.Papers.CrouzeixLS26.LayerDilation
open Qatlib.Papers.CrouzeixLS26.LayerDilation.ContourGaussActualTable


/-! Finite support-plane margins connect a computational anchor outside W(A)
to the original polynomial contour and its same positive Gauss witnesses.
The small auxiliary anchor margin is not used in the quadrature error. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.LayerDilation
open Matrix Set MeasureTheory PolygonWinding
open scoped BigOperators Matrix.Norms.L2Operator

/-- The identity or estimate `support_panels_polynomial_normalized` holds with the displayed separation, geometry and norm hypotheses. -/
theorem support_panels_polynomial_normalized
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (δA δq : ℝ) (hδA : 0 < δA) (hδq : 0 < δq)
    (hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (hnormal : ∀ k, ‖normal k‖ ≤ 1) (hh : ∀ j, 0 < h j)
    (hfacetStart : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j)) = bound (facet j))
    (hfacetEnd : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j)) = bound (facet j))
    (rotation : ℂ) (hrotation : rotation ≠ 0)
    (hstart : ∀ j, (panelStart q rotation (z₀ j) (u j) (a j) (h j)).im ≠ 0)
    (hsafe : ∀ j, (panelStart q rotation (z₀ j) (u j) (a j) (h j)).im*
        (panelEnd q rotation (z₀ j) (u j) (a j) (h j)).im < 0 →
      crossingReal (panelStart q rotation (z₀ j) (u j) (a j) (h j))
        (panelEnd q rotation (z₀ j) (u j) (a j) (h j)) ≠ 0)
    (hcount : (∑ j, panelSign q rotation (z₀ j) (u j) (a j) (h j) : ℤ) = 1) :
    (∑ j, (u j/(2*(Real.pi : ℂ)*Complex.I)) • (∫ t in (a j)..(a j+h j),
      p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) = Polynomial.aeval A p := by
  have hsep := scalarAnchorHomotopy_separation_from_support_endpoints A q center normal bound facet
    z₀ u a h δA δq hA hq hnormal hh hfacetStart hfacetEnd
  have havoid : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      contourPanel (z₀ j) (u j) (a j) (h j) t ≠ q := by
    intro j t _ he
    have hf := halfplaneValue_panel_of_endpoints (normal (facet j)) center (z₀ j) (u j)
      (a j) (h j) (bound (facet j)) (hh j) (hfacetStart j) (hfacetEnd j) t
    rw [he] at hf
    linarith [hq (facet j)]
  have hw := panelScalarWinding_eq_crossing_sum q rotation z₀ u a h next hclosed hrotation hstart hsafe
  rw [hcount, Int.cast_one, mul_one] at hw
  have hκ : (2*(Real.pi : ℂ)*Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact closed_panels_polynomial_normalized_of_uniform_separation A p q z₀ u a h next hclosed
    (min δA δq) (lt_min hδA hδq) (fun j => (hh j).le) hsep havoid
    (2*(Real.pi : ℂ)*Complex.I) hκ hw

/-- One real Gauss table is fixed before the unknown matrix and even before
its index type or the complex contour geometry. Finite arithmetic generation
and its bit-cost remain separate from this quantifier-order result. The
quadrature uses the original margin δA; the anchor may lie outside W(A). -/
theorem uniform_support_polygon_gauss
    {J : Type} [Fintype J] [DecidableEq J] (Q : ℕ) (a h : J → ℝ)
    (hQ : 1 ≤ Q) (hh : ∀ j, 0 < h j) :
    ∃ node weight : J → Fin Q → ℝ,
      (∀ j k, node j k ∈ Icc (a j) (a j+h j)) ∧
      (∀ j k, 0 < weight j k) ∧ (∀ j, ∑ k, weight j k = h j) ∧
      ∀ (I K : Type) [Fintype I] [DecidableEq I] [Fintype K]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ u : J → ℂ) (next : Equiv.Perm J)
    (_hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (δA δq : ℝ) (_hδA : 0 < δA) (_hδq : 0 < δq)
    (_hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (_hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (_hnormal : ∀ k, ‖normal k‖ ≤ 1)
    (_hfacetStart : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j)) = bound (facet j))
    (_hfacetEnd : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j)) = bound (facet j))
    (rotation : ℂ) (_hrotation : rotation ≠ 0)
    (_hstart : ∀ j, (panelStart q rotation (z₀ j) (u j) (a j) (h j)).im ≠ 0)
    (_hsafe : ∀ j, (panelStart q rotation (z₀ j) (u j) (a j) (h j)).im*
        (panelEnd q rotation (z₀ j) (u j) (a j) (h j)).im < 0 →
      crossingReal (panelStart q rotation (z₀ j) (u j) (a j) (h j))
        (panelEnd q rotation (z₀ j) (u j) (a j) (h j)) ≠ 0)
    (_hcount : (∑ j, panelSign q rotation (z₀ j) (u j) (a j) (h j) : ℤ) = 1)
    (M : ℝ) (d m : ℕ) (_hsmall : ∀ j, h j ≤ δA/4) (_hu : ∀ j, ‖u j‖ ≤ 1)
    (_hp : p.natDegree ≤ d) (_hM : 0 ≤ M) (_hdegree : d+m ≤ 2*Q-1)
    (_hpbound : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ‖p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t)‖ ≤ M),
      ‖(∑ j, ∑ k, (((u j/(2*(Real.pi : ℂ)*Complex.I)) * (weight j k : ℂ)) *
          p.eval (contourPanel (z₀ j) (u j) (a j) (h j) (node j k))) •
            matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) (node j k))) -
        Polynomial.aeval A p‖ ≤
      ∑ j, ‖u j/(2*(Real.pi : ℂ)*Complex.I)‖*(2*h j*(M*δA⁻¹*(1/8 : ℝ)^(m+1))) := by
  obtain ⟨node, weight, hn, hw, hs, hall⟩ := ContourGaussActualTable.uniform_actual_gauss_table Q a h hQ hh
  refine ⟨node, weight, hn, hw, hs, ?_⟩
  intro I K _ _ _ A p q center normal bound facet z₀ u next hclosed δA δq hδA hδq
    hA hq hnormal hfacetStart hfacetEnd rotation hrotation hstart hsafe hcount M d m
    hsmall hu hp hM hdegree hpbound
  have hsep : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, δA ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖ := by
    intro j t _ w hw
    exact halfplaneValue_separation (normal (facet j)) center _ w (bound (facet j)) δA
      (hnormal (facet j))
      (halfplaneValue_panel_of_endpoints (normal (facet j)) center (z₀ j) (u j) (a j) (h j)
        (bound (facet j)) (hh j) (hfacetStart j) (hfacetEnd j) t) (hA (facet j) w hw)
  have he := hall I A p z₀ u (fun j => u j/(2*(Real.pi : ℂ)*Complex.I))
    δA M d m hδA hsmall hu hp hM hdegree hsep hpbound
  have hi := support_panels_polynomial_normalized A p q center normal bound facet z₀ u a h next
    hclosed δA δq hδA hδq hA hq hnormal hh hfacetStart hfacetEnd rotation hrotation hstart hsafe hcount
  rw [hi] at he
  exact he


/-- Original per-input interface, retained as a specialization. -/
theorem actual_support_polygon_gauss
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (δA δq : ℝ) (hδA : 0 < δA) (hδq : 0 < δq)
    (hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (hnormal : ∀ k, ‖normal k‖ ≤ 1) (hh : ∀ j, 0 < h j)
    (hfacetStart : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j)) = bound (facet j))
    (hfacetEnd : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j)) = bound (facet j))
    (rotation : ℂ) (hrotation : rotation ≠ 0)
    (hstart : ∀ j, (panelStart q rotation (z₀ j) (u j) (a j) (h j)).im ≠ 0)
    (hsafe : ∀ j, (panelStart q rotation (z₀ j) (u j) (a j) (h j)).im*
        (panelEnd q rotation (z₀ j) (u j) (a j) (h j)).im < 0 →
      crossingReal (panelStart q rotation (z₀ j) (u j) (a j) (h j))
        (panelEnd q rotation (z₀ j) (u j) (a j) (h j)) ≠ 0)
    (hcount : (∑ j, panelSign q rotation (z₀ j) (u j) (a j) (h j) : ℤ) = 1)
    (M : ℝ) (d m Q : ℕ) (hsmall : ∀ j, h j ≤ δA/4) (hu : ∀ j, ‖u j‖ ≤ 1)
    (hp : p.natDegree ≤ d) (hM : 0 ≤ M) (hQ : 1 ≤ Q) (hdegree : d+m ≤ 2*Q-1)
    (hpbound : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ‖p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t)‖ ≤ M) :
    ∃ node weight : J → Fin Q → ℝ,
      (∀ j k, node j k ∈ Icc (a j) (a j+h j)) ∧
      (∀ j k, 0 < weight j k) ∧ (∀ j, ∑ k, weight j k = h j) ∧
      ‖(∑ j, ∑ k, (((u j/(2*(Real.pi : ℂ)*Complex.I)) * (weight j k : ℂ)) *
          p.eval (contourPanel (z₀ j) (u j) (a j) (h j) (node j k))) •
            matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) (node j k))) -
        Polynomial.aeval A p‖ ≤
      ∑ j, ‖u j/(2*(Real.pi : ℂ)*Complex.I)‖*(2*h j*(M*δA⁻¹*(1/8 : ℝ)^(m+1))) := by
  obtain ⟨node, weight, hn, hw, hs, hall⟩ := uniform_support_polygon_gauss Q a h hQ hh
  exact ⟨node, weight, hn, hw, hs,
    hall I K A p q center normal bound facet z₀ u next hclosed δA δq hδA hδq hA hq hnormal
      hfacetStart hfacetEnd rotation hrotation hstart hsafe hcount M d m hsmall hu hp hM hdegree hpbound⟩

end Qatlib.Papers.CrouzeixLS26.LayerDilation
