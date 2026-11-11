/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanIntegral
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanTensor
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false

/-!
# The actual unit-cube integral and tensor quadrature

The source-curvature identity uses Euclidean coordinates, whereas the finite
quadrature uses three scalar loops. This bridge keeps their actual Lebesgue
measures, coordinate order, and normalization identical.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- The tensor loop's coordinate order, embedded in the Euclidean source domain. -/
def meanTensorSpatial (p : MeanTensorPoint) : SpatialPoint :=
  WithLp.toLp 2 ![p.1,p.2.1,p.2.2]

/-- Original `continuous_meanTensorSpatial` guarantee for the `MeanCube` construction; the complete source hypotheses are retained. -/
theorem continuous_meanTensorSpatial : Continuous meanTensorSpatial := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd.fst
  · exact continuous_snd.snd

/-- Definition of cube Coordinate Equiv in the Rational Flow construction. -/
private def cubeCoordinateEquiv : (Fin 3 → ℝ) ≃ᵐ MeanTensorPoint :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

/-- Original `cubeCoordinateEquiv_apply` guarantee for the `MeanCube` construction; the complete source hypotheses are retained. -/
private theorem cubeCoordinateEquiv_apply (u : Fin 3 → ℝ) :
    cubeCoordinateEquiv u=(u 0,u 1,u 2) := rfl

/-- Original `cubeCoordinateEquiv_symm` guarantee for the `MeanCube` construction; the complete source hypotheses are retained. -/
private theorem cubeCoordinateEquiv_symm (p : MeanTensorPoint) :
    cubeCoordinateEquiv.symm p=![p.1,p.2.1,p.2.2] := by
  ext i
  fin_cases i <;> rfl

/-- Original `cubeCoordinateEquiv_volume` guarantee for the `MeanCube` construction; the complete source hypotheses are retained. -/
private theorem cubeCoordinateEquiv_volume : MeasurePreserving cubeCoordinateEquiv := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

/-- Euclidean volume in the unit cube is exactly the nested scalar integral.
Continuity supplies the actual Fubini integrability, rather than an assumed
quadrature identity. -/
theorem unitCubeIntegral_eq_tensor (f : SpatialPoint → ℝ) (hf : Continuous f) :
    unitCubeIntegral f=meanTensorIntegral (fun p => f (meanTensorSpatial p)) := by
  let S := Icc (0 : ℝ) 1
  let B := S ×ˢ (S ×ˢ S)
  let g : MeanTensorPoint → ℝ := fun p => f (meanTensorSpatial p)
  have hg : Continuous g := hf.comp continuous_meanTensorSpatial
  have hbox : B=Icc (0 : MeanTensorPoint) 1 := by
    ext p
    simp [B,S,Prod.le_def,and_assoc]
  have hpre : cubeCoordinateEquiv ⁻¹' B=Icc (0 : Fin 3 → ℝ) 1 := by
    ext u
    simp only [mem_preimage,cubeCoordinateEquiv_apply,B,S,mem_prod,mem_Icc,Pi.le_def]
    simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two,Pi.zero_apply,Pi.one_apply]
    tauto
  have hchange := cubeCoordinateEquiv_volume.setIntegral_preimage_emb
    cubeCoordinateEquiv.measurableEmbedding g B
  have hfun : (fun u => g (cubeCoordinateEquiv u))=
      (fun u => f (WithLp.toLp 2 u)) := by
    funext u
    have he := cubeCoordinateEquiv_symm (cubeCoordinateEquiv u)
    rw [MeasurableEquiv.symm_apply_apply] at he
    change f (WithLp.toLp 2 ![(cubeCoordinateEquiv u).1,
      (cubeCoordinateEquiv u).2.1,(cubeCoordinateEquiv u).2.2])=f (WithLp.toLp 2 u)
    rw [← he]
  rw [hpre,hfun] at hchange
  change (∫ u in Icc (0 : Fin 3 → ℝ) 1, f (WithLp.toLp 2 u))=_
  rw [hchange]
  have hi : IntegrableOn g B := hbox ▸ hg.integrableOn_Icc
  rw [show B=S ×ˢ (S ×ˢ S) from rfl]
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)] at hi ⊢
  rw [setIntegral_prod g hi]
  have hinner (x : ℝ) :
      (∫ yz in S ×ˢ S, g (x,yz))=∫ y in S, ∫ z in S, g (x,y,z) := by
    have hc : Continuous (fun yz : ℝ × ℝ => g (x,yz)) :=
      hg.comp (continuous_const.prodMk continuous_id)
    have hs : S ×ˢ S=Icc (0 : ℝ × ℝ) 1 := by
      ext p
      simp [S,Prod.le_def,and_assoc]
    have hi' : IntegrableOn (fun yz : ℝ × ℝ => g (x,yz)) (S ×ˢ S) :=
      hs ▸ hc.integrableOn_Icc
    rw [Measure.volume_eq_prod ℝ ℝ] at hi' ⊢
    exact setIntegral_prod _ hi'
  simp_rw [hinner]
  simp only [meanTensorIntegral,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,S,g]

/-- The finite tensor estimate now bounds the source identity's actual cube
integral, with no supplied integral or normalization premise. -/
theorem unitCubeIntegral_tensor_error (N : ℕ) (hN : 0<N) (f : SpatialPoint → ℝ)
    (hf : Continuous f) (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ p q, meanTensorInCube p → meanTensorInCube q →
      |f (meanTensorSpatial p)-f (meanTensorSpatial q)| ≤ D*meanTensorDistance p q) :
    |unitCubeIntegral f-meanTensorLeftSum N (fun p => f (meanTensorSpatial p))| ≤
      3*D/(N : ℝ) := by
  rw [unitCubeIntegral_eq_tensor f hf]
  exact meanTensorLeftSum_error N hN _ (hf.comp continuous_meanTensorSpatial) D hD hLip

end Qatlib.Concepts.EffectiveGauge.RationalFlow
