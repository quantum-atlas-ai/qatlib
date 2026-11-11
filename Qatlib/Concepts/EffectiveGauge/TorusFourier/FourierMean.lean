/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Mean

Torus Fourier constructions for Effective Gauge.
Proves `unitComplexCubeIntegral_mode`, `unitFourierSeries_cubeIntegral`, `unitComplexPoisson_mean_zero`.
-/


set_option autoImplicit false
noncomputable section
open Finset Set MeasureTheory
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitComplexCubeIntegral_mode` guarantee for the `FourierMean` construction; the complete source hypotheses are retained. -/
theorem unitComplexCubeIntegral_mode (k : SpatialFrequency) :
    unitComplexCubeIntegral (unitFourierMode k)=if k=0 then 1 else 0 := by
  have h := unitFourierCoefficient_mode k 0
  rw [unitFourierCoefficient_eq_cubeIntegral] at h
  simpa only [neg_zero,unitFourierMode_zero,one_mul,eq_comm] using h

/-- Absolute uniform mode bounds justify integration of the actual
 infinite series. Consequently its true cube mean is its DC coefficient. -/
theorem unitFourierSeries_cubeIntegral (a : SpatialFrequency → ℂ)
    (ha : FourierRapidlySummable a) : unitComplexCubeIntegral (unitFourierSeries a)=a 0 := by
  let F := fun (k : SpatialFrequency) (u : Fin 3 → ℝ) => a k*unitFourierMode k (WithLp.toLp 2 u)
  let mu := (volume : Measure (Fin 3 → ℝ)).restrict (Icc 0 1)
  have hF (k : SpatialFrequency) : Integrable (F k) mu := by
    exact (((contDiff_const.mul (contDiff_unitFourierMode k)).continuous).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous).integrableOn_Icc
  have hvol : (volume : Measure (Fin 3 → ℝ)) (Icc 0 1)=1 := by
    simp [Real.volume_Icc_pi]
  have hnorm (k : SpatialFrequency) : (∫ u, ‖F k u‖ ∂mu)=‖a k‖ := by
    change (∫ u : Fin 3 → ℝ in Icc 0 1, ‖a k*unitFourierMode k (WithLp.toLp 2 u)‖)=‖a k‖
    simp only [norm_mul,unitFourierMode_norm,mul_one]
    simp [hvol,Measure.real]
  have hs : Summable (fun k : SpatialFrequency => ∫ u, ‖F k u‖ ∂mu) := by
    simp_rw [hnorm]
    simpa only [pow_zero,one_mul] using ha 0
  have hswap := integral_tsum_of_summable_integral_norm hF hs
  change (∑' k : SpatialFrequency, unitComplexCubeIntegral (fun x => a k*unitFourierMode k x))=
    unitComplexCubeIntegral (unitFourierSeries a) at hswap
  rw [← hswap]
  simp_rw [unitComplexCubeIntegral_const_mul,unitComplexCubeIntegral_mode]
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    simp [hk]

/-- Original `unitComplexPoisson_mean_zero` guarantee for the `FourierMean` construction; the complete source hypotheses are retained. -/
theorem unitComplexPoisson_mean_zero (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) :
    unitComplexCubeIntegral (unitComplexPoisson f hf hp)=0 := by
  rw [unitComplexPoisson,unitFourierSeries_cubeIntegral _
    (unitPoissonCoefficient_rapidlySummable _
      (fun j => unitFourierCoefficient_rapidlySummable (f j) (hf j) (hp j))),
    unitPoissonCoefficient_zero]

/-- Original `unitRealPoisson_mean_zero` guarantee for the `FourierMean` construction; the complete source hypotheses are retained. -/
theorem unitRealPoisson_mean_zero (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) :
    (∫ u : Fin 3 → ℝ in Icc 0 1, unitRealPoisson f hf hp (WithLp.toLp 2 u))=0 := by
  have hInt : IntegrableOn (fun u : Fin 3 → ℝ => unitComplexPoisson f hf hp (WithLp.toLp 2 u))
      (Icc 0 1) :=
    ((unitComplexPoisson_contDiff f hf hp).continuous.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous).integrableOn_Icc
  have h := Complex.reCLM.integral_comp_comm hInt
  change (∫ u : Fin 3 → ℝ in Icc 0 1, unitRealPoisson f hf hp (WithLp.toLp 2 u))=
    Complex.reCLM (unitComplexCubeIntegral (unitComplexPoisson f hf hp)) at h
  rw [h,unitComplexPoisson_mean_zero,map_zero]

end Qatlib.Concepts.EffectiveGauge.TorusFourier
