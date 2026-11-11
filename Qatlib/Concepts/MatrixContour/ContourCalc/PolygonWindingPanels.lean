/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.PolygonWindingEdges
import Qatlib.Concepts.MatrixContour.ContourCalc.PolygonResolventPrincipal

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.PolygonWinding


/-! Actual affine-panel winding from finite branch data at its real endpoints.
The common nonzero multiplier is fixed across every panel. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc.PolygonWinding
open Matrix Complex Set MeasureTheory
open scoped BigOperators

/-- Construction for panel Start in the polygon winding panels model. -/
def panelStart (c rotation z₀ u : ℂ) (a h : ℝ) : ℂ :=
  (contourPanel z₀ u a h a-c)*rotation

/-- Construction for panel End in the polygon winding panels model. -/
def panelEnd (c rotation z₀ u : ℂ) (a h : ℝ) : ℂ :=
  (contourPanel z₀ u a h (a+h)-c)*rotation

/-- Construction for panel Sign in the polygon winding panels model. -/
def panelSign (c rotation z₀ u : ℂ) (a h : ℝ) : ℤ :=
  crossingSign (panelStart c rotation z₀ u a h) (panelEnd c rotation z₀ u a h)

/-- The identity or estimate `panel_integral_crossing` holds with the displayed separation, geometry and norm hypotheses. -/
theorem panel_integral_crossing (c rotation z₀ u : ℂ) (a h : ℝ) (hr : rotation ≠ 0)
    (hstart : (panelStart c rotation z₀ u a h).im ≠ 0)
    (hend : (panelEnd c rotation z₀ u a h).im ≠ 0)
    (hsafe : (panelStart c rotation z₀ u a h).im*(panelEnd c rotation z₀ u a h).im < 0 →
      crossingReal (panelStart c rotation z₀ u a h) (panelEnd c rotation z₀ u a h) ≠ 0) :
    (∫ t in a..(a+h), u/(contourPanel z₀ u a h t-c)) =
      Complex.log (panelEnd c rotation z₀ u a h)-Complex.log (panelStart c rotation z₀ u a h)+
        (2*(Real.pi : ℂ)*Complex.I)*(panelSign c rotation z₀ u a h : ℂ) := by
  let v₀ := panelStart c rotation z₀ u a h
  let v₁ := panelEnd c rotation z₀ u a h
  have hp (t : ℝ) : edgePath v₀ v₁ t =
      (contourPanel z₀ u a h (h*t+a)-c)*rotation := by
    unfold edgePath v₀ v₁ panelStart panelEnd contourPanel
    push_cast
    ring
  have hd : v₁-v₀ = ((h : ℂ)*u)*rotation := by
    unfold v₀ v₁ panelStart panelEnd contourPanel
    push_cast
    ring
  have hi : (∫ t in (0 : ℝ)..1, (v₁-v₀)/edgePath v₀ v₁ t) =
      ∫ t in a..(a+h), u/(contourPanel z₀ u a h t-c) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (h : ℂ)*(u/(contourPanel z₀ u a h (h*t+a)-c)) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [hd, hp, mul_div_mul_right _ _ hr, mul_div_assoc]
      _ = (h : ℂ)*(∫ t in (0 : ℝ)..1, u/(contourPanel z₀ u a h (h*t+a)-c)) :=
        intervalIntegral.integral_const_mul _ _
      _ = h • (∫ t in (0 : ℝ)..1, u/(contourPanel z₀ u a h (h*t+a)-c)) := by
        rw [Complex.real_smul]
      _ = _ := by
        have he := intervalIntegral.smul_integral_comp_mul_add
          (a := (0 : ℝ)) (b := (1 : ℝ)) (fun t => u/(contourPanel z₀ u a h t-c)) h a
        simpa only [mul_zero, zero_add, mul_one, add_comm h a] using he
  have he := edge_integral_crossing v₀ v₁ hstart hend hsafe
  rw [hi] at he
  exact he

/-- The identity or estimate `panelScalarWinding_eq_crossing_sum` holds with the displayed separation, geometry and norm hypotheses. -/
theorem panelScalarWinding_eq_crossing_sum {J : Type} [Fintype J] [DecidableEq J]
    (c rotation : ℂ) (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (hr : rotation ≠ 0)
    (hstart : ∀ j, (panelStart c rotation (z₀ j) (u j) (a j) (h j)).im ≠ 0)
    (hsafe : ∀ j, (panelStart c rotation (z₀ j) (u j) (a j) (h j)).im*
        (panelEnd c rotation (z₀ j) (u j) (a j) (h j)).im < 0 →
      crossingReal (panelStart c rotation (z₀ j) (u j) (a j) (h j))
        (panelEnd c rotation (z₀ j) (u j) (a j) (h j)) ≠ 0) :
    panelScalarWinding c z₀ u a h = (2*(Real.pi : ℂ)*Complex.I)*
      ((∑ j, panelSign c rotation (z₀ j) (u j) (a j) (h j) : ℤ) : ℂ) := by
  have hend (j : J) : (panelEnd c rotation (z₀ j) (u j) (a j) (h j)).im ≠ 0 := by
    simpa only [panelEnd, panelStart, hclosed j] using hstart (next j)
  unfold panelScalarWinding
  simp_rw [panel_integral_crossing c rotation _ _ _ _ hr (hstart _) (hend _) (hsafe _)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he (j : J) : panelEnd c rotation (z₀ j) (u j) (a j) (h j) =
      panelStart c rotation (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) := by
    unfold panelEnd panelStart
    rw [hclosed]
  simp_rw [he]
  rw [Equiv.sum_comp next (fun j => Complex.log (panelStart c rotation (z₀ j) (u j) (a j) (h j))),
    sub_self, zero_add, ← Finset.mul_sum, ← Int.cast_sum]

end Qatlib.Concepts.MatrixContour.ContourCalc.PolygonWinding
