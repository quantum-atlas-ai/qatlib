/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.PolynomialPanelGauss
import Qatlib.Papers.CrouzeixLS26.LayerDilation.BanachGaussExistence

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Papers.CrouzeixLS26.LayerDilation


/-!
# Polynomial-times-resolvent quadrature on a straight panel

The finite local approximation is expanded into an actual vector coefficient
array.  One positive Gauss rule integrates that array exactly and controls the
actual resolvent integrand by the separation-derived geometric remainder.
The panel uses real parameter measure `dt`; a contour `dz` factor is separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Qatlib.Papers.CrouzeixLS26.LayerDilation
open Qatlib Polynomial MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

/-- Typeclass instance for polynomial Actual ENormed Add Monoid in the actual polynomial panel gauss model. -/
noncomputable local instance polynomialActualENormedAddMonoid {I : Type} [Fintype I] [DecidableEq I] :
    ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- Nodes and weights are fixed from Q,a,h before the index type, unknown
matrix, polynomial, direction, spectral certificates or coefficient array.
They remain mathematical real witnesses, not a finite-precision generator. -/
theorem uniform_polynomial_panel_gauss (Q : ℕ) (a h : ℝ) (hQ : 1 ≤ Q) (hh : 0 < h) :
    ∃ node weight : Fin Q → ℝ,
      (∀ q, node q ∈ Icc a (a+h)) ∧ (∀ q, 0 < weight q) ∧ (∑ q, weight q) = h ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
        (p : Polynomial ℂ) (z₀ u : ℂ) (r M : ℝ) (d m : ℕ),
        0 < r → h ≤ r/4 → ‖u‖ ≤ 1 → p.natDegree ≤ d → 0 ≤ M → d+m ≤ 2*Q-1 →
        (∀ t ∈ Icc a (a+h), ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel z₀ u a h t-w‖) →
        (∀ t ∈ Icc a (a+h), ‖p.eval (contourPanel z₀ u a h t)‖ ≤ M) →
        (∫ t in a..a+h, p.eval (contourPanel z₀ u a h t) •
          localResolventPolynomial A z₀ m (contourPanel z₀ u a h t)) =
          ∑ q, weight q • (p.eval (contourPanel z₀ u a h (node q)) •
            localResolventPolynomial A z₀ m (contourPanel z₀ u a h (node q))) ∧
        ‖(∫ t in a..a+h, p.eval (contourPanel z₀ u a h t) •
            matrixResolvent A (contourPanel z₀ u a h t)) -
          ∑ q, weight q • (p.eval (contourPanel z₀ u a h (node q)) •
            matrixResolvent A (contourPanel z₀ u a h (node q)))‖ ≤
          2*h*(M*r⁻¹*(1/8 : ℝ)^(m+1)) := by
  obtain ⟨node, weight, hn, hw, hs, hexact, herror⟩ := banach_gauss_stability Q a h hQ hh
  refine ⟨node, weight, hn, hw, hs, ?_⟩
  intro I _ _ A p z₀ u r M d m hr hsmall hu hp hM hdegree hsep hpbound
  obtain ⟨c, hcoeff, hf, hE, hbound⟩ :=
    polynomial_panel_approximation_data A p z₀ u a h r M d m hr hh hsmall hu hp hM hsep hpbound
  constructor
  · simpa only [hcoeff] using hexact (Matrix I I ℂ) (d+m) c hdegree
  · exact herror (Matrix I I ℂ) _ (d+m) c _ hf hdegree hE hbound

/-- G21: one actual positive Gauss rule integrates the literal local polynomial
and bounds the actual polynomial-times-resolvent panel integral. -/
theorem polynomial_panel_gauss
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (p : Polynomial ℂ) (z₀ u : ℂ) (a h r M : ℝ) (d m Q : ℕ)
    (hr : 0 < r) (hh : 0 < h) (hsmall : h ≤ r / 4) (hu : ‖u‖ ≤ 1)
    (hp : p.natDegree ≤ d) (hM : 0 ≤ M) (hQ : 1 ≤ Q) (hdegree : d + m ≤ 2 * Q - 1)
    (hsep : ∀ t ∈ Icc a (a + h), ∀ w ∈ matrixNumericalRange A,
      r ≤ ‖contourPanel z₀ u a h t - w‖)
    (hpbound : ∀ t ∈ Icc a (a + h), ‖p.eval (contourPanel z₀ u a h t)‖ ≤ M) :
    ∃ node weight : Fin Q → ℝ,
      (∀ q, node q ∈ Icc a (a + h)) ∧ (∀ q, 0 < weight q) ∧
      (∑ q, weight q) = h ∧
      (∫ t in a..a + h,
        p.eval (contourPanel z₀ u a h t) •
          localResolventPolynomial A z₀ m (contourPanel z₀ u a h t)) =
        ∑ q, weight q •
          (p.eval (contourPanel z₀ u a h (node q)) •
            localResolventPolynomial A z₀ m (contourPanel z₀ u a h (node q))) ∧
      ‖(∫ t in a..a + h,
          p.eval (contourPanel z₀ u a h t) • matrixResolvent A (contourPanel z₀ u a h t)) -
        ∑ q, weight q •
          (p.eval (contourPanel z₀ u a h (node q)) •
            matrixResolvent A (contourPanel z₀ u a h (node q)))‖ ≤
        2 * h * (M * r⁻¹ * (1 / 8 : ℝ) ^ (m + 1)) := by
  obtain ⟨node, weight, hn, hw, hs, hall⟩ := uniform_polynomial_panel_gauss Q a h hQ hh
  obtain ⟨hexact, herror⟩ := hall I A p z₀ u r M d m hr hsmall hu hp hM hdegree hsep hpbound
  exact ⟨node, weight, hn, hw, hs, hexact, herror⟩

end Qatlib.Papers.CrouzeixLS26.LayerDilation
