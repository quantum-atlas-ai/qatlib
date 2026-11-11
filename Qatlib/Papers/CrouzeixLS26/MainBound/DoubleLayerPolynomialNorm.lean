/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayerResidual
import Qatlib.Foundations.OpCalculus.PerturbTwo.ScalarTwoPerturbation
import Qatlib.Papers.CrouzeixLS26.LayerDilation.RationalSupportPolygon
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2
open Qatlib.Concepts.MatrixContour.ContourCalc.PolygonWinding
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open Qatlib.Foundations.OpCalculus.ContourCalc.PolygonWinding
open Qatlib.Foundations.OpCalculus.PerturbTwo
open Qatlib.Papers.CrouzeixLS26.LayerDilation
open Qatlib.Papers.CrouzeixLS26.LayerDilation.ContourGaussActualTable


/-! The constructed actual polygon dilation and the bounded commuting
Cauchy remainders imply the actual Matrix L2 bound ||p(A)||<=2Mc. The Cauchy
certificate is produced from the existing finite support/crossing data;
there is no prior matrix-norm promise or free dilation premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer
open Matrix MeasureTheory ContinuousLinearMap
open scoped Matrix.Norms.L2Operator BigOperators InnerProduct Classical
variable {I J : Type} [Fintype I] [DecidableEq I]
local notation "H" => EuclideanSpace ℂ I
local notation "Op" => (H →L[ℂ] H)
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- Construction for polynomial Weight in the double layer polynomial norm model. -/
def polynomialWeight (q : Polynomial ℂ) (z u : J → ℂ) : J → C(PanelTime,ℂ) := fun j =>
  ⟨fun t => q.eval (contourPanel (z j) (u j) (-1) 2 (t : ℝ)),
    q.continuous.comp ((contourPanel_continuous (z j) (u j) (-1) 2).comp continuous_subtype_val)⟩

variable [Fintype J]

/-- Construction for Polynomial Cauchy in the double layer polynomial norm model. -/
def PolynomialCauchy (A : Matrix I I ℂ) (z u : J → ℂ) : Prop :=
  ∀ q : Polynomial ℂ,(∑ j,∫ t : PanelTime,u j •
    (q.eval (contourPanel (z j) (u j) (-1) 2 (t : ℝ)) •
      matrixResolvent A (contourPanel (z j) (u j) (-1) 2 (t : ℝ))))=
        (2*(Real.pi : ℂ)*Complex.I) • Polynomial.aeval A q

/-- The identity or estimate `mass_from_cauchy` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem mass_from_cauchy (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖) (hC : PolynomialCauchy A z u) :
    (∑ j,∫ t in (-1 : ℝ)..1,matrixPanelDensity
      (matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)) (u j))=1 := by
  have hi (j : J) : IntervalIntegrable
      (fun t : ℝ => matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_iff_continuous_restrict.mpr (matrixCurve A z u r hr hsep j).continuous
  have hp := hC (1 : Polynomial ℂ)
  simp only [Polynomial.eval_one,one_smul,map_one] at hp
  have hp' : (∑ j,∫ t in (-1 : ℝ)..1,u j • matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t))=
      (2*(Real.pi : ℂ)*Complex.I) • (1 : Matrix I I ℂ) := by
    calc
      _ = ∑ j,∫ t : PanelTime,u j • matrixResolvent A (contourPanel (z j) (u j) (-1) 2 (t : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (panelTime_integral (B := Matrix I I ℂ) (fun t : ℝ =>
          u j • matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t))).symm
      _ = _ := hp
  exact matrixPanelDensity_mass_of_principal
    (fun j t => matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)) u
    (fun _ => -1) (fun _ => 1) hi hp'

/-- The identity or estimate `operator_moment_matrix` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem operator_moment_matrix (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖)
    (f : J → C(PanelTime,ℂ)) (n : ℕ) :
    (∑ j,∫ t : PanelTime,(star (f j t))^n • panelDensity (canonicalR A z u r hr hsep j t) (u j))=
      operatorIso (∑ j,∫ t : PanelTime,(star (f j t))^n •
        matrixPanelDensity (matrixCurve A z u r hr hsep j t) (u j)) := by
  calc
    _ = ∑ j,operatorIso (∫ t : PanelTime,(star (f j t))^n •
        matrixPanelDensity (matrixCurve A z u r hr hsep j t) (u j)) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∫ t : PanelTime,operatorIso ((star (f j t))^n •
            matrixPanelDensity (matrixCurve A z u r hr hsep j t) (u j)) := by
          apply integral_congr_ae
          apply Filter.Eventually.of_forall
          intro t
          have hd : operatorIso (matrixPanelDensity (matrixCurve A z u r hr hsep j t) (u j))=
              panelDensity (canonicalR A z u r hr hsep j t) (u j) := matrixPanelDensity_toEuclideanCLM _ _
          change (star (f j t))^n • panelDensity (canonicalR A z u r hr hsep j t) (u j)=
            operatorIso ((star (f j t))^n • matrixPanelDensity (matrixCurve A z u r hr hsep j t) (u j))
          rw [map_smul,hd]
        _ = _ := (operatorIso (I := I)).integral_comp_comm (μ := (volume : Measure PanelTime)) _
    _ = _ := (map_sum operatorIso _ _).symm

/-- The identity or estimate `actual_perturbation_identity` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem actual_perturbation_identity
    (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖)
    (q : Polynomial ℂ) (hC : PolynomialCauchy A z u)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →L[ℂ] K) (Q : K →L[ℂ] K)
    (hMom : ∀ n : ℕ,V† ∘L (Q†^n) ∘L V=
      ∑ j,∫ t : PanelTime,(star (polynomialWeight q z u j t))^n •
        panelDensity (canonicalR A z u r hr hsep j t) (u j)) (n : ℕ) :
    complexPerturbation (operatorIso (Polynomial.aeval A q)) Q V n=
      operatorIso (errorMatrix (matrixCurve A z u r hr hsep) u (polynomialWeight q z u) n) := by
  let T := Polynomial.aeval A q
  let R := matrixCurve A z u r hr hsep
  let f := polynomialWeight q z u
  let P := ∑ j,∫ t : PanelTime,(star (f j t))^n • matrixPanelDensity (R j t) (u j)
  have hCn : (∑ j,∫ t : PanelTime,u j • ((f j t)^n • R j t))=
      (2*(Real.pi : ℂ)*Complex.I) • T^n := by
    have hR (j : J) (t : PanelTime) : R j t =
        matrixResolvent A (contourPanel (z j) (u j) (-1) 2 (t : ℝ)) := rfl
    have hf (j : J) (t : PanelTime) : f j t =
        q.eval (contourPanel (z j) (u j) (-1) 2 (t : ℝ)) := rfl
    simp only [hR, hf, T]
    simpa only [Polynomial.eval_pow, map_pow] using hC (q^n)
  have hc : (2 : ℝ) • P-(star T)^n=errorMatrix R u f n := cauchy_error_identity R u f n T hCn
  have hstar : (operatorIso T)†^n=operatorIso ((star T)^n) := by
    change (star ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) T))^n=
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) ((star T)^n)
    rw [map_pow,map_star]
  have hM : V† ∘L (Q†^n) ∘L V=operatorIso P :=
    (hMom n).trans (operator_moment_matrix A z u r hr hsep f n)
  change (2 : ℝ) • (V† ∘L (Q†^n) ∘L V)-(operatorIso T)†^n=operatorIso (errorMatrix R u f n)
  rw [hM,hstar,two_smul ℝ _]
  have he := congrArg (operatorIso (I := I)) hc
  simpa only [two_smul ℝ _,map_sub,map_add] using he

end Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer

namespace Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer
open Matrix MeasureTheory ContinuousLinearMap
open scoped Matrix.Norms.L2Operator BigOperators InnerProduct Classical
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
local notation "H" => EuclideanSpace ℂ I
local notation "Op" => (H →L[ℂ] H)
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The actual polynomial target is bounded by two on a certified positive
polygon contour, with no prior matrix-norm promise. -/
theorem polynomial_unit_contour_norm
    (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖)
    (hsupport : ∀ j w,w∈matrixNumericalRange A → 0≤(star (-Complex.I*u j)*(z j-w)).re)
    (hC : PolynomialCauchy A z u) (q : Polynomial ℂ)
    (hq : ∀ (j : J) (t : PanelTime),‖q.eval (contourPanel (z j) (u j) (-1) 2 (t : ℝ))‖≤1) :
    ‖Polynomial.aeval A q‖≤2 := by
  let f := polynomialWeight q z u
  let R := matrixCurve A z u r hr hsep
  let T := Polynomial.aeval A q
  let C : ℝ := (2*Real.pi)⁻¹*(∑ j,2*‖u j‖*r⁻¹)
  have hbar : ∀ j t,‖barWeight (f j) t‖≤1 := by
    intro j t
    change ‖star (f j t)‖≤1
    rw [norm_star]
    exact hq j t
  obtain ⟨N,w,g,hV,hQ,hMom⟩ := actual_polygon_dilation A z u r hr hsep hsupport
    (mass_from_cauchy A z u r hr hsep hC) (fun j => barWeight (f j)) hbar
  let V := analysis (dilationMeasure N) w
  let Q := dilationContraction (dilationMeasure N) g
  have hm : ∀ n : ℕ,V† ∘L (Q†^n) ∘L V=
      ∑ j,∫ t : PanelTime,(star (polynomialWeight q z u j t))^n •
        panelDensity (canonicalR A z u r hr hsep j t) (u j) := fun n => hMom n
  have he (n : ℕ) : complexPerturbation (operatorIso T) Q V n=operatorIso (errorMatrix R u f n) :=
    actual_perturbation_identity A z u r hr hsep q hC V Q hm n
  have hb (n : ℕ) : ‖complexPerturbation (operatorIso T) Q V n‖≤C := by
    rw [he n]
    change ‖errorMatrix R u f n‖≤C
    exact errorMatrix_bound R u f r (fun j t => matrixCurve_norm A z u r hr hsep j t) (fun j t => hq j t) n
  have hc (n : ℕ) : Commute (complexPerturbation (operatorIso T) Q V n) (operatorIso T) := by
    rw [he n]
    have hh := errorMatrix_commute R u f n T (fun j t => matrixCurve_commute_polynomial A z u r hr hsep q j t)
    change operatorIso (errorMatrix R u f n)*operatorIso T=operatorIso T*operatorIso (errorMatrix R u f n)
    have ho := congrArg (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) hh.eq
    have hop (B : Matrix I I ℂ) : operatorIso B =
        (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) B := rfl
    simpa only [map_mul, hop] using ho
  have hn := complex_perturbation_norm_le_two (operatorIso T) Q V hQ hV C hb hc
  change ‖Polynomial.aeval A q‖≤2 at hn
  exact hn

end Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer

namespace Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer
open Matrix MeasureTheory ContinuousLinearMap
open scoped Matrix.Norms.L2Operator BigOperators Classical
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `polynomial_contour_norm` holds with the displayed separation, geometry and norm hypotheses. -/
theorem polynomial_contour_norm
    (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖)
    (hsupport : ∀ j w,w∈matrixNumericalRange A → 0≤(star (-Complex.I*u j)*(z j-w)).re)
    (hC : PolynomialCauchy A z u) (p : Polynomial ℂ) (Mc : ℝ) (hMc : 0<Mc)
    (hp : ∀ (j : J) (t : PanelTime),‖p.eval (contourPanel (z j) (u j) (-1) 2 (t : ℝ))‖≤Mc) :
    ‖Polynomial.aeval A p‖≤2*Mc := by
  let q : Polynomial ℂ := Polynomial.C ((Mc : ℂ)⁻¹)*p
  have hq : ∀ (j : J) (t : PanelTime),‖q.eval (contourPanel (z j) (u j) (-1) 2 (t : ℝ))‖≤1 := by
    intro j t
    simp only [q,Polynomial.eval_mul,Polynomial.eval_C,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hMc]
    exact (mul_le_mul_of_nonneg_left (hp j t) (inv_nonneg.mpr hMc.le)).trans_eq (inv_mul_cancel₀ hMc.ne')
  have heval : Polynomial.aeval A q=(Mc⁻¹ : ℝ) • Polynomial.aeval A p := by
    calc
      _ = algebraMap ℂ (Matrix I I ℂ) (Mc : ℂ)⁻¹*Polynomial.aeval A p := by
        change Polynomial.aeval A (Polynomial.C ((Mc : ℂ)⁻¹)*p)=_
        rw [map_mul,Polynomial.aeval_C]
      _ = (Mc : ℂ)⁻¹ • Polynomial.aeval A p := by
        rw [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
      _ = _ := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
        exact congrArg (fun c : ℂ => c • Polynomial.aeval A p) (Complex.ofReal_inv Mc).symm
  have hn := polynomial_unit_contour_norm A z u r hr hsep hsupport hC q hq
  rw [heval,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hMc)] at hn
  calc
    _ = Mc*(Mc⁻¹*‖Polynomial.aeval A p‖) := by field_simp
    _ ≤ Mc*2 := mul_le_mul_of_nonneg_left hn hMc.le
    _ = _ := by ring

end Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer

namespace Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators Classical
variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype K]
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The Cauchy certificate is produced from finite scalar geometry and actual
support truth, not a supplied matrix principal identity. -/
theorem polynomialCauchy_of_support
    (A : Matrix I I ℂ) (q0 center : ℂ)
    (normal : K → ℂ) (bound : K → ℝ) (facet : J → K)
    (z u : J → ℂ) (next : Equiv.Perm J)
    (hclosed : ∀ j,contourPanel (z j) (u j) (-1) 2 1=
      contourPanel (z (next j)) (u (next j)) (-1) 2 (-1))
    (δA δq : ℝ) (hδA : 0<δA) (hδq : 0<δq)
    (hA : ∀ k w,w∈matrixNumericalRange A → halfplaneValue (normal k) center w≤bound k-δA)
    (hq0 : ∀ k,halfplaneValue (normal k) center q0≤bound k-δq)
    (hnormal : ∀ k,‖normal k‖≤1)
    (hstartFace : ∀ j,halfplaneValue (normal (facet j)) center
      (contourPanel (z j) (u j) (-1) 2 (-1))=bound (facet j))
    (hendFace : ∀ j,halfplaneValue (normal (facet j)) center
      (contourPanel (z j) (u j) (-1) 2 1)=bound (facet j))
    (rotation : ℂ) (hrotation : rotation≠0)
    (hstart : ∀ j,(panelStart q0 rotation (z j) (u j) (-1) 2).im≠0)
    (hsafe : ∀ j,(panelStart q0 rotation (z j) (u j) (-1) 2).im*
      (panelEnd q0 rotation (z j) (u j) (-1) 2).im<0 →
      crossingReal (panelStart q0 rotation (z j) (u j) (-1) 2)
        (panelEnd q0 rotation (z j) (u j) (-1) 2)≠0)
    (hcount : (∑ j,panelSign q0 rotation (z j) (u j) (-1) 2 : ℤ)=1) : PolynomialCauchy A z u := by
  intro p
  have hp := support_panels_polynomial_raw A p q0 center normal bound facet z u next hclosed
    δA δq hδA hδq hA hq0 hnormal hstartFace hendFace rotation hrotation hstart hsafe hcount
  calc
    _ = ∑ j,u j • (∫ t in (-1 : ℝ)..1,p.eval (contourPanel (z j) (u j) (-1) 2 t) •
        matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)) := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∫ t in (-1 : ℝ)..1,u j • (p.eval (contourPanel (z j) (u j) (-1) 2 t) •
            matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)) :=
          panelTime_integral (B := Matrix I I ℂ) (fun t : ℝ => u j •
            (p.eval (contourPanel (z j) (u j) (-1) 2 t) • matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)))
        _ = _ := intervalIntegral.integral_smul _ _
    _ = _ := hp

end Qatlib.Papers.CrouzeixLS26.MainBound.DoubleLayer
