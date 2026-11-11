/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourHomotopyIntegral
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Foundations.OpCalculus.ContourCalc


/-! The actual matrix resolvent principal term reduces to a scalar winding
integral at one anchor in the actual numerical range. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) :=
  NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `scalar_matrixResolvent_eq` holds with the displayed separation, geometry and norm hypotheses. -/
theorem scalar_matrixResolvent_eq (c z : ℂ) (hz : z ≠ c) :
    matrixResolvent (c • (1 : Matrix I I ℂ)) z = (z-c)⁻¹ • 1 := by
  apply matrixPseudoinverse_eq_of_twoSidedInverse
  · change (z • (1 : Matrix I I ℂ)-c • 1)*((z-c)⁻¹ • 1) = 1
    rw [← sub_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_smul]
  · change ((z-c)⁻¹ • (1 : Matrix I I ℂ))*(z • 1-c • 1) = 1
    rw [← sub_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hz), one_smul]

/-- Construction for panel Scalar Winding in the polygon resolvent principal model. -/
def panelScalarWinding (c : ℂ) (z₀ u : J → ℂ) (a h : J → ℝ) : ℂ :=
  ∑ j, ∫ t in (a j)..(a j+h j), u j/(contourPanel (z₀ j) (u j) (a j) (h j) t-c)

/-- The principal-term identity follows from actual separation and closure.
Its scalar winding factor is not assumed to be one or 2*pi*i. -/
theorem closed_panels_resolvent_scalar_winding_of_uniform_separation
    (A : Matrix I I ℂ) (c : ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A c s), r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖)
    (havoid : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) → contourPanel (z₀ j) (u j) (a j) (h j) t ≠ c) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) =
      panelScalarWinding c z₀ u a h • (1 : Matrix I I ℂ) := by
  rw [closed_panels_resolvent_homotopy_of_uniform_separation A c z₀ u a h next hclosed r hr hh hsep,
    panelScalarWinding, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← intervalIntegral.integral_smul_const]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (a j) (a j+h j) := by
    simpa only [Set.uIcc_of_le (show a j ≤ a j+h j by linarith [hh j])] using ht
  have hz := havoid j t ht'
  dsimp only
  rw [scalar_matrixResolvent_eq c _ hz, smul_smul, div_eq_mul_inv]

/-- Original range-anchor interface, with its full type preserved. -/
theorem closed_panels_resolvent_scalar_winding
    (A : Matrix I I ℂ) (c : ℂ) (hc : c ∈ matrixNumericalRange A)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) =
      panelScalarWinding c z₀ u a h • (1 : Matrix I I ℂ) := by
  apply closed_panels_resolvent_scalar_winding_of_uniform_separation A c z₀ u a h next hclosed r hr hh
  · intro v hv j t ht
    exact scalarAnchorHomotopy_separation A c _ hc v hv r (hsep j t ht)
  · intro j t ht he
    have hb := hsep j t ht c hc
    rw [he, sub_self, norm_zero] at hb
    exact (not_le.mpr hr) hb

/-- Actual polynomial functional calculus, with the geometric scalar winding
factor retained explicitly. The polynomial target is not an input integral. -/
private theorem polynomial_integral_of_principal
    (A : Matrix I I ℂ) (p : Polynomial ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖)
    (κ : ℂ) (hprincipal : (∑ j, ∫ t in (a j)..(a j+h j),
      u j • matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) = κ • (1 : Matrix I I ℂ)) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • (p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      κ • Polynomial.aeval A p := by
  have hP : Polynomial.aeval A p =
      ∑ n ∈ Finset.range (p.natDegree+1), p.coeff n • A^n := Polynomial.aeval_eq_sum_range A
  have hz (z : ℂ) : (∑ n ∈ Finset.range (p.natDegree+1),
      p.coeff n • (z • (1 : Matrix I I ℂ))^n) = p.eval z • 1 := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro n _
    rw [_root_.smul_pow, one_pow, smul_smul]
  have hred := ContourPolygonResolventReduction.closed_polygon_numerator_reduction
    A (Finset.range (p.natDegree+1)) p.coeff z₀ u a h next hclosed r hr hh hsep
  simp only [hz, ← hP, Matrix.smul_mul, Matrix.one_mul] at hred
  have hfactor (j : J) :
      (∫ t in (a j)..(a j+h j), u j • (Polynomial.aeval A p *
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      Polynomial.aeval A p * (∫ t in (a j)..(a j+h j), u j •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) := by
    have hR : ContinuousOn
        (fun t => matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))
        (Set.Icc (a j) (a j+h j)) :=
      (matrixResolvent_continuousOn_of_separation A r hr).comp
        (contourPanel_continuous (z₀ j) (u j) (a j) (h j)).continuousOn (hsep j)
    have hint : IntervalIntegrable (fun t => u j •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) volume (a j) (a j+h j) :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith [hh j])
        ((continuousOn_const (c := u j)).smul hR)
    simpa only [ContinuousLinearMap.mul_apply', Matrix.mul_smul] using
      (ContinuousLinearMap.mul ℂ (Matrix I I ℂ) (Polynomial.aeval A p)).intervalIntegral_comp_comm hint
  calc
    _ = ∑ j, ∫ t in (a j)..(a j+h j), u j • (Polynomial.aeval A p *
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) := hred
    _ = ∑ j, Polynomial.aeval A p * (∫ t in (a j)..(a j+h j), u j •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) :=
      Finset.sum_congr rfl (fun j _ => hfactor j)
    _ = Polynomial.aeval A p * (∑ j, ∫ t in (a j)..(a j+h j), u j •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t)) :=
      (Finset.mul_sum _ _ _).symm
    _ = Polynomial.aeval A p * (κ • (1 : Matrix I I ℂ)) := by
      rw [hprincipal]
    _ = κ • Polynomial.aeval A p := by
      rw [Matrix.mul_smul, Matrix.mul_one]

/-- The identity or estimate `closed_panels_polynomial_scalar_winding` holds with the displayed separation, geometry and norm hypotheses. -/
theorem closed_panels_polynomial_scalar_winding
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (c : ℂ) (hc : c ∈ matrixNumericalRange A)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • (p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      panelScalarWinding c z₀ u a h • Polynomial.aeval A p := by
  exact polynomial_integral_of_principal A p z₀ u a h next hclosed r hr hh hsep
    (panelScalarWinding c z₀ u a h)
    (closed_panels_resolvent_scalar_winding A c hc z₀ u a h next hclosed r hr hh hsep)

/-- Arbitrary anchor under a true uniform homotopy gap. -/
theorem closed_panels_polynomial_scalar_winding_of_uniform_separation
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (c : ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A c s), r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖)
    (havoid : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) → contourPanel (z₀ j) (u j) (a j) (h j) t ≠ c) :
    (∑ j, ∫ t in (a j)..(a j+h j),
      u j • (p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      panelScalarWinding c z₀ u a h • Polynomial.aeval A p := by
  have h1 : scalarAnchorHomotopy A c 1 = A := by simp [scalarAnchorHomotopy]
  have hsepA : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖ := by
    intro j t ht
    simpa only [h1] using hsep 1 (by norm_num) j t ht
  exact polynomial_integral_of_principal A p z₀ u a h next hclosed r hr hh hsepA
    (panelScalarWinding c z₀ u a h)
    (closed_panels_resolvent_scalar_winding_of_uniform_separation A c z₀ u a h next hclosed r hr hh hsep havoid)

/-- A scalar geometric winding certificate supplies the normalization of
the polynomial contour. There is no matrix Cauchy premise. -/
theorem closed_panels_polynomial_normalized
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (c : ℂ) (hc : c ∈ matrixNumericalRange A)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange A, r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖)
    (κ : ℂ) (hκ : κ ≠ 0) (hwinding : panelScalarWinding c z₀ u a h = κ) :
    (∑ j, (u j/κ) • (∫ t in (a j)..(a j+h j),
      p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      Polynomial.aeval A p := by
  have hi := closed_panels_polynomial_scalar_winding A p c hc z₀ u a h next hclosed r hr hh hsep
  have hfactor : (∑ j, (u j/κ) • (∫ t in (a j)..(a j+h j),
      p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      κ⁻¹ • (∑ j, ∫ t in (a j)..(a j+h j), u j •
        (p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
          matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_smul, smul_smul]
    congr 1
    exact div_eq_inv_mul _ _
  rw [hfactor, hi, hwinding, smul_smul, inv_mul_cancel₀ hκ, one_smul]

/-- Normalization for a computational anchor, without membership in W(A). -/
theorem closed_panels_polynomial_normalized_of_uniform_separation
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (c : ℂ)
    (z₀ u : J → ℂ) (a h : J → ℝ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (u j) (a j) (h j) (a j+h j) =
      contourPanel (z₀ (next j)) (u (next j)) (a (next j)) (h (next j)) (a (next j)))
    (r : ℝ) (hr : 0 < r) (hh : ∀ j, 0 ≤ h j)
    (hsep : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j t, t ∈ Set.Icc (a j) (a j+h j) →
      ∀ w ∈ matrixNumericalRange (scalarAnchorHomotopy A c s), r ≤ ‖contourPanel (z₀ j) (u j) (a j) (h j) t-w‖)
    (havoid : ∀ j t, t ∈ Set.Icc (a j) (a j+h j) → contourPanel (z₀ j) (u j) (a j) (h j) t ≠ c)
    (κ : ℂ) (hκ : κ ≠ 0) (hwinding : panelScalarWinding c z₀ u a h = κ) :
    (∑ j, (u j/κ) • (∫ t in (a j)..(a j+h j),
      p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      Polynomial.aeval A p := by
  have hi := closed_panels_polynomial_scalar_winding_of_uniform_separation A p c z₀ u a h next hclosed r hr hh hsep havoid
  have hfactor : (∑ j, (u j/κ) • (∫ t in (a j)..(a j+h j),
      p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
        matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) =
      κ⁻¹ • (∑ j, ∫ t in (a j)..(a j+h j), u j •
        (p.eval (contourPanel (z₀ j) (u j) (a j) (h j) t) •
          matrixResolvent A (contourPanel (z₀ j) (u j) (a j) (h j) t))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_smul, smul_smul]
    congr 1
    exact div_eq_inv_mul _ _
  rw [hfactor, hi, hwinding, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end Qatlib.Concepts.MatrixContour.ContourCalc
