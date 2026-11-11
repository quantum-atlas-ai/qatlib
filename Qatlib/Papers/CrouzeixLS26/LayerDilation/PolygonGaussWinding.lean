/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.PolygonWindingPanels
import Qatlib.Papers.CrouzeixLS26.LayerDilation.PolygonGaussPolynomial

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


/-! Finite endpoint crossing checks replace the scalar integral oracle in
the original polynomial's positive panel-Gauss consumer. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.LayerDilation
open Matrix Set MeasureTheory PolygonWinding
open scoped BigOperators Matrix.Norms.L2Operator

/-- The identity or estimate `actual_polygon_gauss_of_crossings` holds with the displayed separation, geometry and norm hypotheses. -/
theorem actual_polygon_gauss_of_crossings
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (c : ℂ) (hc : c ∈ matrixNumericalRange A)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r M : ℝ) (d m Q : ℕ) (hr : 0 < r) (hh : ∀ j, 0 < h j)
    (hsmall : ∀ j, h j ≤ r/4) (hu : ∀ j, ‖u j‖ ≤ 1)
    (hp : p.natDegree ≤ d) (hM : 0 ≤ M) (hQ : 1 ≤ Q) (hdegree : d+m ≤ 2*Q-1)
    (hsep : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖)
    (hpbound : ∀ j t, t ∈ Icc (a j) (a j+h j) →
      ‖p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t)‖ ≤ M)
    (rotation : ℂ) (hrotation : rotation ≠ 0)
    (hstart : ∀ j, (panelStart c rotation (z₀ j) (u j) (a j) (h j)).im ≠ 0)
    (hsafe : ∀ j, (panelStart c rotation (z₀ j) (u j) (a j) (h j)).im*
        (panelEnd c rotation (z₀ j) (u j) (a j) (h j)).im < 0 →
      crossingReal (panelStart c rotation (z₀ j) (u j) (a j) (h j))
        (panelEnd c rotation (z₀ j) (u j) (a j) (h j)) ≠ 0)
    (hcount : (∑ j, panelSign c rotation (z₀ j) (u j) (a j) (h j) : ℤ) = 1) :
    ∃ node weight : J → Fin Q → ℝ,
      (∀ j q, node j q ∈ Icc (a j) (a j+h j)) ∧
      (∀ j q, 0 < weight j q) ∧ (∀ j, ∑ q, weight j q = h j) ∧
      ‖(∑ j, ∑ q, (((u j/(2*(Real.pi : ℂ)*Complex.I)) * (weight j q : ℂ)) *
          p.eval (contourPanel (z₀ j) (u j) (a j) (h j) (node j q))) •
            matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) (node j q))) -
        Polynomial.aeval A p‖ ≤
      ∑ j, ‖u j/(2*(Real.pi : ℂ)*Complex.I)‖*(2*h j*(M*r⁻¹*(1/8 : ℝ)^(m+1))) := by
  have hw := panelScalarWinding_eq_crossing_sum c rotation z₀ u a h next hclosed hrotation hstart hsafe
  rw [hcount, Int.cast_one, mul_one] at hw
  have hκ : (2*(Real.pi : ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact actual_polygon_gauss_polynomial A p c hc z₀ u a h next hclosed r M d m Q hr hh hsmall hu
    hp hM hQ hdegree hsep hpbound (2*(Real.pi : ℂ)*Complex.I) hκ hw

end Qatlib.Papers.CrouzeixLS26.LayerDilation
