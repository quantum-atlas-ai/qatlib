/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Foundations.OpCalculus.ContourCalc

/-! Closed finite polygon integral for the genuine polynomial remainder.
The resolvent winding term and Cauchy formula are not proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive

open scoped BigOperators Matrix.Norms.L2Operator

/-- The identity or estimate `segment_integral_primitive` holds with the displayed separation, geometry and norm hypotheses. -/
theorem segment_integral_primitive {I : Type} [Fintype I] [DecidableEq I]
    (f G : ℂ → Matrix I I ℂ) (hG : ∀ z, HasDerivAt G (f z) z)
    (hf : Continuous f) (a b : ℂ) :
    (∫ t : ℝ in (0 : ℝ)..1, (b-a) • f (a + (t : ℂ)*(b-a))) = G b - G a := by
  let path : ℝ → ℂ := fun t => a + (t : ℂ)*(b-a)
  have hp : ∀ t : ℝ, HasDerivAt path (b-a) t := by
    intro t
    dsimp [path]
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (b-a)).const_add a)
  have hpath : Continuous path :=
    (show Differentiable ℝ path from fun t => (hp t).differentiableAt).continuous
  have hi : Continuous (fun t : ℝ => (b-a) • f (path t)) :=
    by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun t _ => (hG (path t)).scomp t (hp t)) (hi.intervalIntegrable 0 1)
  simpa [path, Function.comp_def] using he

/-- The identity or estimate `polygon_remainder_integral_zero` holds with the displayed separation, geometry and norm hypotheses. -/
theorem polygon_remainder_integral_zero {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ)
    (v : J → ℂ) (next : Equiv.Perm J) :
    (∑ j, ∫ t : ℝ in (0 : ℝ)..1,
      (v (next j)-v j) • polynomialRemainder A terms c
        (v j + (t : ℂ)*(v (next j)-v j))) = 0 := by
  obtain ⟨G, hG⟩ := polynomial_remainder_has_primitive A terms c
  have hc : Continuous (polynomialRemainder A terms c) :=
    (polynomial_remainder_differentiable A terms c).continuous
  simp_rw [segment_integral_primitive _ G hG hc]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ j, G (v (next j))) = ∑ j, G (v j) :=
    Equiv.sum_comp next (fun j => G (v j))
  rw [hsum, sub_self]

/-- The same fundamental theorem in the actual `contourPanel` parameter,
including its direction factor and arbitrary real interval orientation. -/
theorem panel_integral_primitive {I : Type} [Fintype I] [DecidableEq I]
    (f G : ℂ → Matrix I I ℂ) (hG : ∀ z, HasDerivAt G (f z) z)
    (hf : Continuous f) (z₀ u : ℂ) (a h : ℝ) :
    (∫ t : ℝ in a..(a+h), u • f (contourPanel z₀ u a h t)) =
      G (contourPanel z₀ u a h (a+h)) - G (contourPanel z₀ u a h a) := by
  let path : ℝ → ℂ := contourPanel z₀ u a h
  have hp : ∀ t : ℝ, HasDerivAt path u t := by
    intro t
    have hh := (((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const
      ((a+h/2 : ℝ) : ℂ)).mul_const u).const_add z₀
    convert hh using 1
    · ext x
      simp [path, contourPanel]
    · simp
  have hpath : Continuous path :=
    (show Differentiable ℝ path from fun t => (hp t).differentiableAt).continuous
  have hi : Continuous (fun t : ℝ => u • f (path t)) :=
    by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := a+h)
    (fun t _ => (hG (path t)).scomp t (hp t)) (hi.intervalIntegrable a (a+h))
  simpa [path, Function.comp_def] using he

/-- The identity or estimate `closed_panels_remainder_integral_zero` holds with the displayed separation, geometry and norm hypotheses. -/
theorem closed_panels_remainder_integral_zero {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix I I ℂ) (terms : Finset ℕ) (c : ℕ → ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j))) :
    (∑ j, ∫ t : ℝ in (a j)..(a j+h j),
      u j • polynomialRemainder A terms c (contourPanel (z₀ j) (u j) (a j) (h j) t)) = 0 := by
  obtain ⟨G, hG⟩ := polynomial_remainder_has_primitive A terms c
  have hc : Continuous (polynomialRemainder A terms c) :=
    (polynomial_remainder_differentiable A terms c).continuous
  simp_rw [panel_integral_primitive _ G hG hc, hclosed]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ j, G (contourPanel (z₀ (next j)) (u (next j)) (a (next j))
      (h (next j)) (a (next j)))) =
      ∑ j, G (contourPanel (z₀ j) (u j) (a j) (h j) (a j)) :=
    Equiv.sum_comp next (fun j => G (contourPanel (z₀ j) (u j) (a j) (h j) (a j)))
  rw [hsum, sub_self]

end Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
