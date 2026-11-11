/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayerL2Frame
import Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayerPanelTime
import Mathlib.Data.Fintype.BigOperators
open Qatlib.Foundations.OpCalculus.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer
open Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2


/-! Flatten finite per-panel Gram rows into one scalar L2 frame. All actual
weighted moments use the same row enumeration and continuous resolvent
family; isometry follows from the corresponding kernel mass identity. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped BigOperators InnerProduct Classical
variable {J E : Type} [Fintype J]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Construction for row Count in the double layer flat gram model. -/
def rowCount (m : J → ℕ) : ℕ := Fintype.card (Σ j,Fin (m j))
/-- Construction for row Index in the double layer flat gram model. -/
def rowIndex (m : J → ℕ) : Fin (rowCount m) ≃ Σ j,Fin (m j) := (Fintype.equivFin _).symm

/-- Construction for row Curve in the double layer flat gram model. -/
def rowCurve (R : C(PanelTime,E →L[ℂ] E)) (a : E) : C(PanelTime,E) :=
  ⟨fun t => ((R t)†) a,by
    have hc : Continuous (fun T : E →L[ℂ] E => T†) := adjoint.continuous
    exact (hc.comp R.continuous).clm_apply continuous_const⟩

/-- Construction for row Moment in the double layer flat gram model. -/
def rowMoment (R : C(PanelTime,E →L[ℂ] E)) (a : E) (f : C(PanelTime,ℂ)) (n : ℕ) :
    C(PanelTime,E →L[ℂ] E) := by
  let v := rowCurve R a
  have hv : Continuous (fun t => rankOne ℂ (v t) (v t)) := by
    simpa only [Function.comp_apply,toSpanSingletonLIE_apply,rankOne_def'] using
      ((toSpanSingletonLIE ℂ E).continuous.comp v.continuous).clm_comp
        ((innerSL ℂ).continuous.comp v.continuous)
  exact ⟨fun t => (f t)^n • rankOne ℂ (v t) (v t),(f.continuous.pow n).smul hv⟩

/-- Construction for flat Frame in the double layer flat gram model. -/
def flatFrame (m : J → ℕ) (a : ∀ j,Fin (m j) → E) (R : J → C(PanelTime,E →L[ℂ] E)) :
    C(Fin (rowCount m) × PanelTime,E) :=
  ⟨fun p => rowCurve (R (rowIndex m p.1).1) (a (rowIndex m p.1).1 (rowIndex m p.1).2) p.2,by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (rowCurve (R (rowIndex m k).1) (a (rowIndex m k).1 (rowIndex m k).2)).continuous⟩

/-- Construction for flat Weight in the double layer flat gram model. -/
def flatWeight (m : J → ℕ) (f : J → C(PanelTime,ℂ)) : C(Fin (rowCount m) × PanelTime,ℂ) :=
  ⟨fun p => f (rowIndex m p.1).1 p.2,by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (f (rowIndex m k).1).continuous⟩

/-- Construction for flat Moment in the double layer flat gram model. -/
def flatMoment (m : J → ℕ) (a : ∀ j,Fin (m j) → E) (R : J → C(PanelTime,E →L[ℂ] E))
    (f : J → C(PanelTime,ℂ)) (n : ℕ) : C(Fin (rowCount m) × PanelTime,E →L[ℂ] E) :=
  ⟨fun p => rowMoment (R (rowIndex m p.1).1) (a (rowIndex m p.1).1 (rowIndex m p.1).2)
      (f (rowIndex m p.1).1) n p.2,by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact (rowMoment (R (rowIndex m k).1) (a (rowIndex m k).1 (rowIndex m k).2)
      (f (rowIndex m k).1) n).continuous⟩

/-- The identity or estimate `sum_rankOne_adjoint` holds with the displayed separation, geometry and norm hypotheses. -/
theorem sum_rankOne_adjoint (R : E →L[ℂ] E) (m : ℕ) (a : Fin m → E) :
    (∑ i,rankOne ℂ ((R†) (a i)) ((R†) (a i)))=
      R† ∘L (∑ i,rankOne ℂ (a i) (a i)) ∘L R := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.sum_apply,comp_apply,rankOne_apply,adjoint_inner_left,map_sum,map_smul]

/-- The identity or estimate `weighted_flat_integral` holds with the displayed separation, geometry and norm hypotheses. -/
theorem weighted_flat_integral (m : J → ℕ) (a : ∀ j,Fin (m j) → E)
    (R : J → C(PanelTime,E →L[ℂ] E)) (f : J → C(PanelTime,ℂ)) (n : ℕ) :
    (∫ p,(flatWeight m f p)^n • rankOne ℂ (flatFrame m a R p) (flatFrame m a R p)
      ∂dilationMeasure (rowCount m))=
      (4*Real.pi)⁻¹ • (∑ j,∫ t : PanelTime,(f j t)^n •
        ((R j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L R j t)) := by
  let F := flatMoment m a R f n
  change (∫ p,F p ∂dilationMeasure (rowCount m))=_
  rw [dilationMeasure_integral]
  congr 1
  calc
    _ = ∑ s : Σ j,Fin (m j),∫ t : PanelTime,rowMoment (R s.1) (a s.1 s.2) (f s.1) n t :=
      (rowIndex m).sum_comp (fun s => ∫ t : PanelTime,rowMoment (R s.1) (a s.1 s.2) (f s.1) n t)
    _ = ∑ j,∑ i,∫ t : PanelTime,rowMoment (R j) (a j i) (f j) n t := by rw [Fintype.sum_sigma]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      have hint (i : Fin (m j)) (_hi : i∈Finset.univ) :
          Integrable (fun t : PanelTime => rowMoment (R j) (a j i) (f j) n t) volume :=
        memLp_one_iff_integrable.mp ((rowMoment (R j) (a j i) (f j) n).memLp (p := 1) (μ := volume) ℝ)
      rw [← integral_finsetSum Finset.univ hint]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change (∑ i,(f j t)^n • rankOne ℂ (((R j t)†) (a j i)) (((R j t)†) (a j i)))=_
      rw [← Finset.smul_sum,sum_rankOne_adjoint]

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2

namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped BigOperators InnerProduct Classical
variable {J E : Type} [Fintype J]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The identity or estimate `flat_dilation` holds with the displayed separation, geometry and norm hypotheses. -/
theorem flat_dilation (m : J → ℕ) (a : ∀ j,Fin (m j) → E)
    (R : J → C(PanelTime,E →L[ℂ] E)) (f : J → C(PanelTime,ℂ))
    (hMass : (4*Real.pi)⁻¹ • (∑ j,∫ t : PanelTime,
      (R j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L R j t)=1)
    (hf : ∀ j t,‖f j t‖≤1) :
    let μ := dilationMeasure (rowCount m)
    let w := flatFrame m a R
    let g := flatWeight m f
    (∀ x,‖analysis μ w x‖=‖x‖) ∧ ‖dilationContraction μ g‖≤1 ∧
      ∀ n : ℕ,(analysis μ w)† ∘L (((dilationContraction μ g)†)^n) ∘L analysis μ w=
        (4*Real.pi)⁻¹ • (∑ j,∫ t : PanelTime,(f j t)^n •
          ((R j t)† ∘L (∑ i,rankOne ℂ (a j i) (a j i)) ∘L R j t)) := by
  let μ := dilationMeasure (rowCount m)
  let w := flatFrame m a R
  let g := flatWeight m f
  have hw : (∫ p,rankOne ℂ (w p) (w p) ∂μ)=1 := by
    have h0 := weighted_flat_integral m a R (fun _ => 1) 0
    simp only [pow_zero,one_smul] at h0
    exact h0.trans hMass
  have hg : ∀ p,‖g p‖≤1 := fun p => hf (rowIndex m p.1).1 p.2
  refine ⟨analysis_norm μ w hw,dilationContraction_norm μ g hg,?_⟩
  intro n
  exact (all_power_moment μ w g n).trans (weighted_flat_integral m a R f n)

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
