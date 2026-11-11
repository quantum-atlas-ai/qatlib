/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayerPolygonL2
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonPrimitive
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolygonResolventReduction
open Qatlib.Concepts.MatrixContour.ContourCalc.ContourPolynomialDivision
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer.L2
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2


/-! Weighted Cauchy cancellation for the same matrix density and scalar
powers. The polynomial consumer supplies the Cauchy identity from its actual
support/crossing certificate; no final norm bound is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
open Matrix MeasureTheory ContinuousLinearMap
open scoped Matrix.Norms.L2Operator BigOperators InnerProduct Classical
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
noncomputable local instance : ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- Construction for weighted Velocity in the double layer cauchy model. -/
def weightedVelocity (R : C(PanelTime,Matrix I I ℂ)) (u : ℂ) (f : C(PanelTime,ℂ)) (n : ℕ) :
    C(PanelTime,Matrix I I ℂ) :=
  ⟨fun t => (f t)^n • velocityTerm (R t) u,
    by unfold velocityTerm; fun_prop⟩

/-- The identity or estimate `star_integral` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem star_integral (f : PanelTime → Matrix I I ℂ) :
    (∫ t,star (f t))=star (∫ t,f t) :=
  (starL' ℝ : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ).integral_comp_comm f

/-- The identity or estimate `weightedVelocity_integrable` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem weightedVelocity_integrable (R : C(PanelTime,Matrix I I ℂ)) (u : ℂ)
    (f : C(PanelTime,ℂ)) (n : ℕ) : Integrable (fun t => (f t)^n • velocityTerm (R t) u) volume := by
  change Integrable (weightedVelocity R u f n : PanelTime → Matrix I I ℂ) volume
  exact memLp_one_iff_integrable.mp ((weightedVelocity R u f n).memLp (p := 1) (μ := volume) ℝ)

/-- The identity or estimate `star_weightedVelocity_integrable` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem star_weightedVelocity_integrable (R : C(PanelTime,Matrix I I ℂ)) (u : ℂ)
    (f : C(PanelTime,ℂ)) (n : ℕ) : Integrable (fun t => star ((f t)^n • velocityTerm (R t) u)) volume :=
  (starL' ℝ : Matrix I I ℂ ≃L[ℝ] Matrix I I ℂ).toContinuousLinearMap.integrable_comp
    (weightedVelocity_integrable R u f n)

/-- The identity or estimate `conjugateWeight` holds with the displayed separation, geometry and norm hypotheses. -/
private theorem conjugateWeight (f : C(PanelTime,ℂ)) : Continuous (fun t => star (f t)) :=
  continuous_star.comp f.continuous

/-- Construction for bar Weight in the double layer cauchy model. -/
def barWeight (f : C(PanelTime,ℂ)) : C(PanelTime,ℂ) := ⟨fun t => star (f t),conjugateWeight f⟩

/-- The identity or estimate `velocity_eval` holds with the displayed separation, geometry and norm hypotheses. -/
theorem velocity_eval (R : J → C(PanelTime,Matrix I I ℂ)) (u : J → ℂ)
    (f : J → C(PanelTime,ℂ)) (n : ℕ) (T : Matrix I I ℂ)
    (hC : (∑ j,∫ t : PanelTime,u j • ((f j t)^n • R j t))=
      (2*(Real.pi : ℂ)*Complex.I) • T^n) :
    (∑ j,∫ t : PanelTime,(f j t)^n • velocityTerm (R j t) (u j))=
      (2*(Real.pi : ℂ)) • T^n := by
  have heq : (∑ j,∫ t : PanelTime,(f j t)^n • velocityTerm (R j t) (u j))=
      (-Complex.I) • (∑ j,∫ t : PanelTime,u j • ((f j t)^n • R j t)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← integral_smul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [velocityTerm,smul_smul]
    congr 1
    ring
  rw [heq,hC,smul_smul]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

/-- The identity or estimate `density_split` holds with the displayed separation, geometry and norm hypotheses. -/
theorem density_split (R : J → C(PanelTime,Matrix I I ℂ)) (u : J → ℂ)
    (f : J → C(PanelTime,ℂ)) (n : ℕ) :
    (∑ j,∫ t : PanelTime,(star (f j t))^n • matrixPanelDensity (R j t) (u j))=
      (((4*Real.pi)⁻¹ : ℝ) : ℂ) •
        ((∑ j,∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j))+
          star (∑ j,∫ t : PanelTime,(f j t)^n • velocityTerm (R j t) (u j))) := by
  have hp (j : J) (t : PanelTime) :
      (star (f j t))^n • matrixPanelDensity (R j t) (u j)=
        (((4*Real.pi)⁻¹ : ℝ) : ℂ) •
          ((star (f j t))^n • velocityTerm (R j t) (u j)+
            star ((f j t)^n • velocityTerm (R j t) (u j))) := by
    simp only [matrixPanelDensity,star_smul,star_pow]
    module
  calc
    _ = ∑ j,(((4*Real.pi)⁻¹ : ℝ) : ℂ) •
        ((∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j))+
          star (∫ t : PanelTime,(f j t)^n • velocityTerm (R j t) (u j))) := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [hp]
      have hbar : Integrable (fun t : PanelTime => (star (f j t))^n • velocityTerm (R j t) (u j)) volume :=
        weightedVelocity_integrable (R j) (u j) (barWeight (f j)) n
      rw [integral_smul,integral_add hbar
        (star_weightedVelocity_integrable (R j) (u j) (f j) n),star_integral]
    _ = _ := by
      rw [← Finset.smul_sum,Finset.sum_add_distrib]
      congr 2
      exact (map_sum (starAddEquiv : Matrix I I ℂ ≃+ Matrix I I ℂ) _ _).symm

/-- The identity or estimate `cauchy_error_identity` holds with the displayed separation, geometry and norm hypotheses. -/
theorem cauchy_error_identity (R : J → C(PanelTime,Matrix I I ℂ)) (u : J → ℂ)
    (f : J → C(PanelTime,ℂ)) (n : ℕ) (T : Matrix I I ℂ)
    (hC : (∑ j,∫ t : PanelTime,u j • ((f j t)^n • R j t))=
      (2*(Real.pi : ℂ)*Complex.I) • T^n) :
    (2 : ℝ) • (∑ j,∫ t : PanelTime,(star (f j t))^n • matrixPanelDensity (R j t) (u j))-
        (star T)^n=
      (((2*Real.pi)⁻¹ : ℝ) : ℂ) •
        (∑ j,∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j)) := by
  let A := ∑ j,∫ t : PanelTime,(star (f j t))^n • velocityTerm (R j t) (u j)
  let K : ℂ := (((2*Real.pi)⁻¹ : ℝ) : ℂ)
  have hpi : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have hc : (((4*Real.pi)⁻¹ : ℝ) : ℂ)=(1/2 : ℂ)*K := by
    dsimp [K]
    push_cast
    field_simp; ring
  have hk : K*(2*(Real.pi : ℂ))=1 := by
    dsimp [K]
    push_cast
    field_simp
  have hb : star (∑ j,∫ t : PanelTime,(f j t)^n • velocityTerm (R j t) (u j))=
      (2*(Real.pi : ℂ)) • (star T)^n := by
    rw [velocity_eval R u f n T hC]
    simp only [star_smul,map_mul,map_ofNat,Complex.star_def,Complex.conj_ofReal,star_pow]
  rw [density_split,hb,hc]
  change (2 : ℝ) • (((1/2 : ℂ)*K) • (A+(2*(Real.pi : ℂ)) • (star T)^n))-(star T)^n=K • A
  rw [two_smul ℝ _]
  calc
    _ = (K • A+(K*(2*(Real.pi : ℂ))) • (star T)^n)-(star T)^n := by module
    _ = _ := by rw [hk,one_smul,add_sub_cancel_right]

end Qatlib.Concepts.MatrixContour.ContourCalc.DoubleLayer
