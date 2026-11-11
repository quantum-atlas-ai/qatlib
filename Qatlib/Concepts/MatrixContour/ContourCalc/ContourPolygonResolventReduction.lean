/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
import Qatlib.Concepts.MatrixContour.ContourCalc.PolynomialPanelGauss

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Foundations.OpCalculus.ContourCalc

/-! Exact reduction of the polynomial contour integrand to its resolvent
principal term. This does not prove the resolvent winding integral. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction

open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable local instance {I : Type} [Fintype I] [DecidableEq I] :
    ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `numerator_division` holds with the displayed separation, geometry and norm hypotheses. -/
theorem numerator_division {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) (r : ℝ)
    (hr : 0 < r) (hz : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z-w‖) :
    (∑ n ∈ terms, c n • (z • (1 : Matrix I I ℂ)) ^ n) * matrixResolvent A z =
      (∑ n ∈ terms, c n • A ^ n) * matrixResolvent A z +
        polynomialRemainder A terms c z := by
  have h := polynomial_resolvent_division A z r hr hz terms c
  unfold polynomialRemainder
  simp only [smul_sub, Finset.sum_sub_distrib, sub_mul] at h
  have hh := sub_eq_iff_eq_add.mp h
  simpa only [add_comm] using hh

/-- The entire numerator may be replaced by the constant matrix polynomial
inside the closed polygon integral. The only remaining principal term is
`p(A) * R(z)`; no resolvent winding integral is assumed or proved here. -/
theorem closed_polygon_numerator_reduction {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖) :
    (∑ j, ∫ t : ℝ in (a j)..(a j+h j),
      u j • ((∑ n ∈ terms, c n •
        (contourPanel (z₀ j) (u j) (a j) (h j) t • (1 : Matrix I I ℂ)) ^ n) *
          matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
    ∑ j, ∫ t : ℝ in (a j)..(a j+h j),
      u j • ((∑ n ∈ terms, c n • A ^ n) *
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) := by
  have hint : ∀ j, IntervalIntegrable (fun t : ℝ =>
      u j • ((∑ n ∈ terms, c n • A ^ n) *
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) volume (a j) (a j+h j) := by
    intro j
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [hh j])
    have hc : ContinuousOn
        (fun t => matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))
        (Set.Icc (a j) (a j+h j)) :=
      (matrixResolvent_continuousOn_of_separation A r hr).comp
        (contourPanel_continuous (z₀ j) (u j) (a j) (h j)).continuousOn (hsep j)
    have hU : ContinuousOn (fun _ : ℝ => u j) (Set.Icc (a j) (a j+h j)) := continuousOn_const
    have hA : ContinuousOn (fun _ : ℝ => (∑ n ∈ terms, c n • A ^ n))
        (Set.Icc (a j) (a j+h j)) := continuousOn_const
    simpa only [Pi.smul_def',Pi.mul_apply] using hU.smul (hA.mul hc)
  have hrem := closed_panels_remainder_integral_zero A terms c z₀ u a h next hclosed
  have hp : ∀ j, Continuous (fun t : ℝ =>
      u j • polynomialRemainder A terms c (contourPanel (z₀ j) (u j) (a j) (h j) t)) := by
    intro j
    have hU : Continuous (fun _ : ℝ => u j) := continuous_const
    simpa only [Pi.smul_def',Function.comp_def] using
      hU.smul ((polynomial_remainder_differentiable A terms c).continuous.comp
        (contourPanel_continuous (z₀ j) (u j) (a j) (h j)))
  have heq : ∀ j,
      (∫ t : ℝ in (a j)..(a j+h j),
        u j • ((∑ n ∈ terms, c n •
          (contourPanel (z₀ j) (u j) (a j) (h j) t • (1 : Matrix I I ℂ)) ^ n) *
            matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      (∫ t : ℝ in (a j)..(a j+h j),
        u j • ((∑ n ∈ terms, c n • A ^ n) *
          matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) +
      (∫ t : ℝ in (a j)..(a j+h j),
        u j • polynomialRemainder A terms c (contourPanel (z₀ j) (u j) (a j) (h j) t)) := by
    intro j
    rw [← intervalIntegral.integral_add (hint j) ((hp j).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (a j) (a j+h j) := by
      simpa [Set.uIcc_of_le (show a j ≤ a j+h j by linarith [hh j])] using ht
    dsimp only
    rw [numerator_division A terms c _ r hr (hsep j t ht'), smul_add]
  simp_rw [heq, Finset.sum_add_distrib]
  rw [hrem, add_zero]

end Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
