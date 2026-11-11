/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.PolygonResolventPrincipal
import Qatlib.Papers.CrouzeixLS26.LayerDilation.PanelGaussTable

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Papers.CrouzeixLS26.LayerDilation
open Qatlib.Papers.CrouzeixLS26.LayerDilation.ContourGaussActualTable


/-! The common positive panel-Gauss witnesses target the actual matrix polynomial.
Only the scalar geometric winding normalization remains a certificate input. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.LayerDilation
open Matrix Set MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

/-- The same actual positive Gauss witnesses and original canonical
resolvents approximate `aeval A p`, without a supplied matrix Cauchy formula
or integral-to-target error premise. -/
theorem actual_polygon_gauss_polynomial
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
    (κ : ℂ) (hκ : κ ≠ 0) (hwinding : panelScalarWinding c z₀ u a h = κ) :
    ∃ node weight : J → Fin Q → ℝ,
      (∀ j q, node j q ∈ Icc (a j) (a j+h j)) ∧
      (∀ j q, 0 < weight j q) ∧ (∀ j, ∑ q, weight j q = h j) ∧
      ‖(∑ j, ∑ q, (((u j/κ) * (weight j q : ℂ)) *
          p.eval (contourPanel (z₀ j) (u j) (a j) (h j) (node j q))) •
            matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) (node j q))) -
        Polynomial.aeval A p‖ ≤
      ∑ j, ‖u j/κ‖*(2*h j*(M*r⁻¹*(1/8 : ℝ)^(m+1))) := by
  obtain ⟨node, weight, hn, hw, hs, he⟩ := ContourGaussActualTable.actual_gauss_table
    A p z₀ u (fun j => u j/κ) a h r M d m Q hr hh hsmall hu hp hM hQ hdegree hsep hpbound
  have hi := closed_panels_polynomial_normalized A p c hc z₀ u a h next hclosed r hr
    (fun j => (hh j).le) hsep κ hκ hwinding
  rw [hi] at he
  exact ⟨node, weight, hn, hw, hs, he⟩

end Qatlib.Papers.CrouzeixLS26.LayerDilation
