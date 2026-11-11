/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CrouzeixLS26.LayerDilation.PolygonSupportGauss
import Qatlib.Concepts.MatrixContour.ContourCalc.RationalResolventPanel

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


/-! The actual rational rule on each normalized panel reaches the raw closed
contour target 2*pi*i*p(A). Raw coefficients have no pi factor; the contour
normalization and its phase are handled separately by a consumer. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.LayerDilation
open Qatlib Matrix Set MeasureTheory PolygonWinding
open scoped BigOperators Matrix.Norms.L2Operator

/-- The actual scalar location, fixed by known normalized panel data. -/
def rationalPolygonNode {J : Type} {Q : ℕ} (z₀ v : J → ℂ)
    (node : J → Fin Q → ℚ) (x : J × Fin Q) : ℂ :=
  contourPanel (z₀ x.1) (v x.1) (-1) 2 (node x.1 x.2 : ℝ)

/-- Raw contour coefficient: no pi approximation is used in this table. -/
def rawRationalContourCoefficient {J : Type} {Q : ℕ} (p : Polynomial ℂ)
    (z₀ v : J → ℂ) (node weight : J → Fin Q → ℚ) (x : J × Fin Q) : ℂ :=
  (v x.1 * (weight x.1 x.2 : ℂ)) * p.eval (rationalPolygonNode z₀ v node x)

/-- Explicit scalar bound from the accepted rule and separated local expansion. -/
def rationalPolygonError {J : Type} [Fintype J] {Q : ℕ}
    (p : Polynomial ℂ) (z₀ v : J → ℂ) (weight : J → Fin Q → ℚ)
    (η : J → ℚ) (r M : ℝ) (d m : ℕ) : ℝ :=
  ∑ j, ‖v j‖ * ((2+∑ k, (weight j k : ℝ))*(M*r⁻¹*(1/8 : ℝ)^(m+1)) +
    polynomialPanelCoefficientEnvelope p (z₀ j) (v j) (-1) 2 r d m * (η j : ℝ))

/-- Finite support and crossing data imply the raw principal identity;
there is no matrix Cauchy identity or anchor membership premise. -/
theorem support_panels_polynomial_raw
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ v : J → ℂ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (v j) (-1) 2 1 =
      contourPanel (z₀ (next j)) (v (next j)) (-1) 2 (-1))
    (δA δq : ℝ) (hδA : 0 < δA) (hδq : 0 < δq)
    (hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (hnormal : ∀ k, ‖normal k‖ ≤ 1)
    (hfacetStart : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (v j) (-1) 2 (-1)) = bound (facet j))
    (hfacetEnd : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (v j) (-1) 2 1) = bound (facet j))
    (rotation : ℂ) (hrotation : rotation ≠ 0)
    (hstart : ∀ j, (panelStart q rotation (z₀ j) (v j) (-1) 2).im ≠ 0)
    (hsafe : ∀ j, (panelStart q rotation (z₀ j) (v j) (-1) 2).im*
        (panelEnd q rotation (z₀ j) (v j) (-1) 2).im < 0 →
      crossingReal (panelStart q rotation (z₀ j) (v j) (-1) 2)
        (panelEnd q rotation (z₀ j) (v j) (-1) 2) ≠ 0)
    (hcount : (∑ j, panelSign q rotation (z₀ j) (v j) (-1) 2 : ℤ) = 1) :
    (∑ j, (v j) • (∫ t in (-1 : ℝ)..1,
      p.eval (contourPanel (z₀ j) (v j) (-1) 2 t) •
        matrixResolvent A (contourPanel (z₀ j) (v j) (-1) 2 t))) =
      (2*(Real.pi : ℂ)*Complex.I) • Polynomial.aeval A p := by
  let κ : ℂ := 2*(Real.pi : ℂ)*Complex.I
  have hκ : κ ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hi := support_panels_polynomial_normalized A p q center normal bound facet z₀ v
    (fun _ => -1) (fun _ => 2) next
    (by simpa only [show (-1 : ℝ)+2=1 by norm_num] using hclosed)
    δA δq hδA hδq hA hq hnormal (fun _ => by norm_num) hfacetStart
    (by simpa only [show (-1 : ℝ)+2=1 by norm_num] using hfacetEnd)
    rotation hrotation hstart hsafe hcount
  have hs := congrArg (fun T : Matrix I I ℂ => κ • T) hi
  have hm (j : J) : κ * (v j/(2*(Real.pi : ℂ)*Complex.I)) = v j := by
    change κ * (v j/κ) = v j
    field_simp
  simp only [Finset.smul_sum, smul_smul, hm] at hs
  simpa only [show (-1 : ℝ)+2=1 by norm_num] using hs

/-- The actual finite rational tables reach the raw matrix-polynomial target. -/
theorem raw_support_polygon_moment_error
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K]
    (Q d m : ℕ) (node weight : J → Fin Q → ℚ) (η : J → ℚ)
    (hc : ∀ j, rationalPositiveMomentCheck Q (d+m) (node j) (weight j) (η j) = true)
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (q center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z₀ v : J → ℂ) (next : Equiv.Perm J)
    (hclosed : ∀ j, contourPanel (z₀ j) (v j) (-1) 2 1 =
      contourPanel (z₀ (next j)) (v (next j)) (-1) 2 (-1))
    (δA δq : ℝ) (hδA : 0 < δA) (hδq : 0 < δq)
    (hA : ∀ k w, w ∈ matrixNumericalRange A → halfplaneValue (normal k) center w ≤ bound k-δA)
    (hq : ∀ k, halfplaneValue (normal k) center q ≤ bound k-δq)
    (hnormal : ∀ k, ‖normal k‖ ≤ 1)
    (hfacetStart : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (v j) (-1) 2 (-1)) = bound (facet j))
    (hfacetEnd : ∀ j, halfplaneValue (normal (facet j)) center
      (contourPanel (z₀ j) (v j) (-1) 2 1) = bound (facet j))
    (rotation : ℂ) (hrotation : rotation ≠ 0)
    (hstart : ∀ j, (panelStart q rotation (z₀ j) (v j) (-1) 2).im ≠ 0)
    (hsafe : ∀ j, (panelStart q rotation (z₀ j) (v j) (-1) 2).im*
        (panelEnd q rotation (z₀ j) (v j) (-1) 2).im < 0 →
      crossingReal (panelStart q rotation (z₀ j) (v j) (-1) 2)
        (panelEnd q rotation (z₀ j) (v j) (-1) 2) ≠ 0)
    (hcount : (∑ j, panelSign q rotation (z₀ j) (v j) (-1) 2 : ℤ) = 1)
    (M : ℝ) (hv : ∀ j, ‖v j‖ ≤ δA/8) (hp : p.natDegree ≤ d) (hM : 0 ≤ M)
    (hpbound : ∀ j t, t ∈ Icc (-1 : ℝ) 1 →
      ‖p.eval (contourPanel (z₀ j) (v j) (-1) 2 t)‖ ≤ M) :
    ‖(∑ x : J × Fin Q, rawRationalContourCoefficient p z₀ v node weight x •
        matrixResolvent A (rationalPolygonNode z₀ v node x)) -
      (2*(Real.pi : ℂ)*Complex.I) • Polynomial.aeval A p‖ ≤
      rationalPolygonError p z₀ v weight η δA M d m := by
  let T : J → Matrix I I ℂ := fun j => ∫ t in (-1 : ℝ)..1,
    p.eval (contourPanel (z₀ j) (v j) (-1) 2 t) •
      matrixResolvent A (contourPanel (z₀ j) (v j) (-1) 2 t)
  let S : J → Matrix I I ℂ := fun j => ∑ k, (weight j k : ℝ) •
    (p.eval (contourPanel (z₀ j) (v j) (-1) 2 (node j k : ℝ)) •
      matrixResolvent A (contourPanel (z₀ j) (v j) (-1) 2 (node j k : ℝ)))
  have hsep (j : J) (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) :
      ∀ w ∈ matrixNumericalRange A, δA ≤ ‖contourPanel (z₀ j) (v j) (-1) 2 t-w‖ := by
    intro w hw
    exact halfplaneValue_separation (normal (facet j)) center _ w (bound (facet j)) δA
      (hnormal (facet j))
      (halfplaneValue_panel_of_endpoints (normal (facet j)) center (z₀ j) (v j) (-1) 2
        (bound (facet j)) (by norm_num) (hfacetStart j)
        (by simpa only [show (-1 : ℝ)+2=1 by norm_num] using hfacetEnd j) t)
      (hA (facet j) w hw)
  have he (j : J) : ‖T j-S j‖ ≤
      (2+∑ k, (weight j k : ℝ))*(M*δA⁻¹*(1/8 : ℝ)^(m+1)) +
        polynomialPanelCoefficientEnvelope p (z₀ j) (v j) (-1) 2 δA d m * (η j : ℝ) :=
    rational_polynomial_resolvent_panel Q d m (node j) (weight j) (η j) (hc j)
      A p (z₀ j) (v j) δA M hδA (hv j) hp hM (hsep j) (hpbound j)
  have hi := support_panels_polynomial_raw A p q center normal bound facet z₀ v next hclosed
    δA δq hδA hδq hA hq hnormal hfacetStart hfacetEnd
    rotation hrotation hstart hsafe hcount
  have hrepr : (∑ x : J × Fin Q, rawRationalContourCoefficient p z₀ v node weight x •
        matrixResolvent A (rationalPolygonNode z₀ v node x)) = ∑ j, v j • S j := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [rawRationalContourCoefficient, rationalPolygonNode,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, RCLike.ofReal_ratCast, mul_assoc]
  rw [hrepr, ← hi]
  change ‖(∑ j, v j • S j) - (∑ j, v j • T j)‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖v j • S j-v j • T j‖ := norm_sum_le _ _
    _ = ∑ j, ‖v j‖ * ‖S j-T j‖ := by simp only [← smul_sub, norm_smul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using he j) (norm_nonneg _))

end Qatlib.Papers.CrouzeixLS26.LayerDilation
