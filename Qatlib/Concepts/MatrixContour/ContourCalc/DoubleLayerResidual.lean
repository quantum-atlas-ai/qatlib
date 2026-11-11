/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayerCauchy
import Mathlib.Algebra.BigOperators.Ring.Finset
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2


/-! The Cauchy remainder is a scalar-weighted integral of the actual
resolvent. Its commutation and norm bound are independent of the power
index; matrix norms are the actual L2 operator norm throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Matrix MeasureTheory ContinuousLinearMap
open scoped Matrix.Norms.L2Operator BigOperators InnerProduct Classical
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `actual_resolvent_commute` holds with the displayed separation, geometry and norm hypotheses. -/
theorem actual_resolvent_commute (A : Matrix I I ℂ) (z : ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ w∈matrixNumericalRange A,r≤‖z-w‖) : Commute (matrixResolvent A z) A := by
  obtain ⟨hZR,hRZ,_⟩ := matrixResolvent_inverse_norm_of_separation A z r hr hsep
  have hh := hRZ.trans hZR.symm
  simp only [matrixShift,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.one_mul,Matrix.mul_one] at hh
  change matrixResolvent A z*A=A*matrixResolvent A z
  exact sub_right_inj.mp hh

/-- The identity or estimate `commute_polynomial` holds with the displayed separation, geometry and norm hypotheses. -/
theorem commute_polynomial (R A : Matrix I I ℂ) (q : Polynomial ℂ) (hRA : Commute R A) :
    Commute R (Polynomial.aeval A q) := by
  rw [Polynomial.aeval_eq_sum_range A]
  exact Commute.sum_right _ _ _ (fun k _ => (hRA.pow_right k).smul_right (q.coeff k))

/-- The identity or estimate `integral_commute` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem integral_commute (F : C(PanelTime,Matrix I I ℂ)) (T : Matrix I I ℂ)
    (hF : ∀ t,Commute (F t) T) : Commute (∫ t : PanelTime,F t) T := by
  have hint : Integrable F volume := memLp_one_iff_integrable.mp (F.memLp (p := 1) (μ := volume) ℝ)
  let Lr : Matrix I I ℂ →L[ℂ] Matrix I I ℂ := (ContinuousLinearMap.mul ℂ (Matrix I I ℂ)).flip T
  let Ll : Matrix I I ℂ →L[ℂ] Matrix I I ℂ := ContinuousLinearMap.mul ℂ (Matrix I I ℂ) T
  have hr : (∫ t : PanelTime,F t)*T=∫ t : PanelTime,F t*T := (Lr.integral_comp_comm hint).symm
  have hl : T*(∫ t : PanelTime,F t)=∫ t : PanelTime,T*F t := (Ll.integral_comp_comm hint).symm
  change (∫ t : PanelTime,F t)*T=T*(∫ t : PanelTime,F t)
  rw [hr,hl]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (hF t).eq))

/-- Construction for error Matrix in the double layer residual model. -/
def errorMatrix (R : J → C(PanelTime,Matrix I I ℂ)) (u : J → ℂ) (f : J → C(PanelTime,ℂ)) (n : ℕ) :
    Matrix I I ℂ := (((2*Real.pi)⁻¹ : ℝ) : ℂ) •
      (∑ j,∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j))

/-- The identity or estimate `errorMatrix_commute` holds with the displayed separation, geometry and norm hypotheses. -/
theorem errorMatrix_commute (R : J → C(PanelTime,Matrix I I ℂ)) (u : J → ℂ)
    (f : J → C(PanelTime,ℂ)) (n : ℕ) (T : Matrix I I ℂ)
    (hR : ∀ j t,Commute (R j t) T) : Commute (errorMatrix R u f n) T := by
  have hc (j : J) : Commute (∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j)) T := by
    apply integral_commute (weightedVelocity (R j) (u j) (barWeight (f j)) n) T
    intro t
    exact ((hR j t).smul_left (-Complex.I*u j)).smul_left ((star (f j t))^n)
  exact (Commute.sum_left Finset.univ _ T (fun j _ => hc j)).smul_left _

/-- The identity or estimate `weighted_velocity_norm` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem weighted_velocity_norm (R : C(PanelTime,Matrix I I ℂ)) (u : ℂ)
    (f : C(PanelTime,ℂ)) (r : ℝ) (hR : ∀ t,‖R t‖≤r⁻¹) (hf : ∀ t,‖f t‖≤1) (n : ℕ) (t : PanelTime) :
    ‖(star (f t))^n • velocityTerm (R t) u‖≤‖u‖*r⁻¹ := by
  have hp : ‖f t‖^n≤1 := pow_le_one₀ (norm_nonneg _) (hf t)
  have hu : ‖-Complex.I*u‖=‖u‖ := by rw [norm_mul,norm_neg,Complex.norm_I,one_mul]
  calc
    _ = ‖f t‖^n*(‖u‖*‖R t‖) := by rw [norm_smul,norm_pow,norm_star,velocityTerm,norm_smul,hu]
    _ ≤ 1*(‖u‖*‖R t‖) := mul_le_mul_of_nonneg_right hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_left (hR t) (norm_nonneg u)

/-- The identity or estimate `errorMatrix_bound` holds with the displayed separation, geometry and norm hypotheses. -/
theorem errorMatrix_bound (R : J → C(PanelTime,Matrix I I ℂ)) (u : J → ℂ)
    (f : J → C(PanelTime,ℂ)) (r : ℝ)
    (hR : ∀ j t,‖R j t‖≤r⁻¹) (hf : ∀ j t,‖f j t‖≤1) (n : ℕ) :
    ‖errorMatrix R u f n‖≤(2*Real.pi)⁻¹*(∑ j,2*‖u j‖*r⁻¹) := by
  have hk : ‖(((2*Real.pi)⁻¹ : ℝ) : ℂ)‖=(2*Real.pi)⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ)<2*Real.pi))]
  have hnode (j : J) : ‖∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j)‖≤2*‖u j‖*r⁻¹ := by
    have hh := norm_integral_le_of_norm_le_const (μ := (volume : Measure PanelTime))
      (Filter.Eventually.of_forall (fun t => weighted_velocity_norm (R j) (u j) (f j) r (hR j) (hf j) n t))
    have hh' : ‖∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j)‖≤‖u j‖*r⁻¹*2 := by
      simpa only [measureReal_def,panelTime_volume,ENNReal.toReal_ofNat] using hh
    exact hh'.trans_eq (by ring)
  rw [errorMatrix,norm_smul,hk]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ)≤(2*Real.pi)⁻¹)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hnode j))

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer

namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Matrix MeasureTheory ContinuousLinearMap
open scoped Matrix.Norms.L2Operator BigOperators Classical
variable {I J : Type} [Fintype I] [DecidableEq I]

/-- Matrix-valued version of the same canonical separated panel resolvent. -/
def matrixCurve (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖) : J → C(PanelTime,Matrix I I ℂ) := fun j =>
  ⟨fun t => matrixResolvent A (contourPanel (z j) (u j) (-1) 2 (t : ℝ)),by
    have hc : ContinuousOn
        (fun t : ℝ => matrixResolvent A (contourPanel (z j) (u j) (-1) 2 t)) (Set.Icc (-1 : ℝ) 1) :=
      (matrixResolvent_continuousOn_of_separation A r hr).comp
        (contourPanel_continuous (z j) (u j) (-1) 2).continuousOn (fun t ht => hsep j ⟨t,ht⟩)
    exact continuousOn_iff_continuous_restrict.mp hc⟩

/-- The identity or estimate `matrixCurve_norm` holds with the displayed separation, geometry and norm hypotheses. -/
theorem matrixCurve_norm (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖) (j : J) (t : PanelTime) :
    ‖matrixCurve A z u r hr hsep j t‖≤r⁻¹ :=
  (matrixResolvent_inverse_norm_of_separation A _ r hr (hsep j t)).2.2

/-- The identity or estimate `matrixCurve_commute_polynomial` holds with the displayed separation, geometry and norm hypotheses. -/
theorem matrixCurve_commute_polynomial (A : Matrix I I ℂ) (z u : J → ℂ) (r : ℝ) (hr : 0<r)
    (hsep : ∀ (j : J) (t : PanelTime),∀ w∈matrixNumericalRange A,
      r≤‖contourPanel (z j) (u j) (-1) 2 (t : ℝ)-w‖) (q : Polynomial ℂ) (j : J) (t : PanelTime) :
    Commute (matrixCurve A z u r hr hsep j t) (Polynomial.aeval A q) :=
  commute_polynomial _ A q (actual_resolvent_commute A _ r hr (hsep j t))

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
