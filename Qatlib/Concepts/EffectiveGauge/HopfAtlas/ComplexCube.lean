/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ComplexTensor
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitComplexIntegral

set_option backward.isDefEq.respectTransparency false

/-!
# Complex Cube

Hopf Atlas constructions for Effective Gauge.
Proves `unitComplexCubeIntegral_clm`, `complexMeanTensorIntegral_clm`, `unitComplexCubeIntegral_eq_tensor`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `unitComplexCubeIntegral_clm` guarantee for the `ComplexCube` construction; the complete source hypotheses are retained. -/
theorem unitComplexCubeIntegral_clm (L : ℂ →L[ℝ] ℝ) (f : SpatialPoint → ℂ) (hf : Continuous f) :
    L (unitComplexCubeIntegral f)=unitCubeIntegral (fun x => L (f x)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hi : IntegrableOn (fun u : Fin 3 → ℝ => f (WithLp.toLp 2 u)) (Icc 0 1) :=
    (hf.comp e.continuous).integrableOn_Icc
  change L (∫ u : Fin 3 → ℝ in Icc 0 1, f (WithLp.toLp 2 u))=
    ∫ u : Fin 3 → ℝ in Icc 0 1, L (f (WithLp.toLp 2 u))
  exact (L.integral_comp_comm hi).symm

/-- Original `complexMeanTensorIntegral_clm` guarantee for the `ComplexCube` construction; the complete source hypotheses are retained. -/
theorem complexMeanTensorIntegral_clm (L : ℂ →L[ℝ] ℝ) (f : MeanTensorPoint → ℂ)
    (hf : Continuous f) :
    L (complexMeanTensorIntegral f)=meanTensorIntegral (fun p => L (f p)) := by
  have h3 : Continuous (fun p : (ℝ × ℝ) × ℝ => f (p.1.1,p.1.2,p.2)) :=
    hf.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hxy : Continuous (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, f (p.1,p.2,z)) :=
    continuous_complexMeanUnitIntegral (fun p : ℝ × ℝ => fun z => f (p.1,p.2,z)) h3
  have hx : Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (x,y,z)) :=
    continuous_complexMeanUnitIntegral (fun x y => ∫ z in (0 : ℝ)..1, f (x,y,z)) hxy
  have hinner (x y : ℝ) : L (∫ z in (0 : ℝ)..1, f (x,y,z))=
      ∫ z in (0 : ℝ)..1, L (f (x,y,z)) := by
    have hc : Continuous (fun z : ℝ => f (x,y,z)) :=
      hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    exact (L.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)).symm
  have hmiddle (x : ℝ) : L (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (x,y,z))=
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, L (f (x,y,z)) := by
    have hc : Continuous (fun y : ℝ => ∫ z in (0 : ℝ)..1, f (x,y,z)) :=
      hxy.comp (continuous_const.prodMk continuous_id)
    rw [← L.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro y _
    exact hinner x y
  unfold complexMeanTensorIntegral meanTensorIntegral
  rw [← L.intervalIntegral_comp_comm (hx.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro x _
  exact hmiddle x

/-- Re/im are used only to transport an exact integral identity. The error
estimate itself stays in the complex norm and pays no extra factor two. -/
theorem unitComplexCubeIntegral_eq_tensor (f : SpatialPoint → ℂ) (hf : Continuous f) :
    unitComplexCubeIntegral f=complexMeanTensorIntegral (fun p => f (meanTensorSpatial p)) := by
  have hc : Continuous (fun p => f (meanTensorSpatial p)) := hf.comp continuous_meanTensorSpatial
  apply Complex.ext
  · change Complex.reCLM (unitComplexCubeIntegral f)=
      Complex.reCLM (complexMeanTensorIntegral (fun p => f (meanTensorSpatial p)))
    rw [unitComplexCubeIntegral_clm _ f hf,complexMeanTensorIntegral_clm _ _ hc]
    exact unitCubeIntegral_eq_tensor (fun x => Complex.reCLM (f x)) (Complex.reCLM.continuous.comp hf)
  · change Complex.imCLM (unitComplexCubeIntegral f)=
      Complex.imCLM (complexMeanTensorIntegral (fun p => f (meanTensorSpatial p)))
    rw [unitComplexCubeIntegral_clm _ f hf,complexMeanTensorIntegral_clm _ _ hc]
    exact unitCubeIntegral_eq_tensor (fun x => Complex.imCLM (f x)) (Complex.imCLM.continuous.comp hf)

/-- Original `unitComplexCubeIntegral_tensor_error` guarantee for the `ComplexCube` construction; the complete source hypotheses are retained. -/
theorem unitComplexCubeIntegral_tensor_error (N : ℕ) (hN : 0<N) (f : SpatialPoint → ℂ)
    (hf : Continuous f) (D : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ p q, meanTensorInCube p → meanTensorInCube q →
      ‖f (meanTensorSpatial p)-f (meanTensorSpatial q)‖ ≤ D*meanTensorDistance p q) :
    ‖unitComplexCubeIntegral f-complexMeanTensorLeftSum N (fun p => f (meanTensorSpatial p))‖ ≤
      3*D/(N : ℝ) := by
  rw [unitComplexCubeIntegral_eq_tensor f hf]
  exact complexMeanTensorLeftSum_error N hN _ (hf.comp continuous_meanTensorSpatial) D hD hLip

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
