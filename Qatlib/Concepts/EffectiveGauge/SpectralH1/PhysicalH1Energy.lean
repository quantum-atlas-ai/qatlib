/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierEnergyTail
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanIntegral
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceWord

set_option backward.isDefEq.respectTransparency false

/-!
# Physical H1 Energy

Spectral H1 constructions for Effective Gauge.
Defines `physicalFieldH1Energy`, `unitFieldH1Energy`.
Proves `physicalCubeIntegral_scale`, `unitBoxEnergy_eq_unitCubeIntegral`, `physicalFieldH1Energy_integrable`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.SpectralH1
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `physicalCubeIntegral_scale` guarantee for the `PhysicalH1Energy` construction; the complete source hypotheses are retained. -/
theorem physicalCubeIntegral_scale (f : SpatialPoint → ℝ) :
    physicalCubeIntegral f=physicalPeriod^3*unitCubeIntegral (fun u => f (physicalPeriod • u)) := by
  have h := physicalCubeMean_scale f
  dsimp only [physicalCubeMean] at h
  have he := (div_eq_iff (pow_ne_zero 3 physicalPeriod_pos.ne')).mp h
  simpa only [mul_comm] using he

/-- Original `unitBoxEnergy_eq_unitCubeIntegral` guarantee for the `PhysicalH1Energy` construction; the complete source hypotheses are retained. -/
theorem unitBoxEnergy_eq_unitCubeIntegral {E : Type*} [NormedAddCommGroup E] (f : SpatialPoint → E) :
    unitBoxEnergy f=unitCubeIntegral (fun x => ‖f x‖^2) := by
  unfold unitBoxEnergy unitCubeIntegral
  exact setIntegral_congr_set Measure.univ_pi_Ioc_ae_eq_Icc

/-- Definition of physical Field H1 Energy in the Spectral H1 construction. -/
def physicalFieldH1Energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) : ℝ :=
  physicalCubeIntegral (fun X => ‖f X‖^2)+
    ∑ i : Fin 3, physicalCubeIntegral (fun X => ‖spatialWordPartial f [i] X‖^2)

/-- Definition of unit Field H1 Energy in the Spectral H1 construction. -/
def unitFieldH1Energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) : ℝ :=
  unitBoxEnergy f+(∑ i : Fin 3, unitBoxEnergy (spatialWordPartial f [i]))/physicalPeriod^2

/-- Original `physicalFieldH1Energy_integrable` guarantee for the `PhysicalH1Energy` construction; the complete source hypotheses are retained. -/
theorem physicalFieldH1Energy_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) :
    IntegrableOn (fun u : Fin 3 → ℝ => ‖f (WithLp.toLp 2 u)‖^2)
      (Icc (0 : Fin 3 → ℝ) (fun _ => physicalPeriod)) ∧
      ∀ i : Fin 3, IntegrableOn (fun u : Fin 3 → ℝ => ‖spatialWordPartial f [i] (WithLp.toLp 2 u)‖^2)
        (Icc (0 : Fin 3 → ℝ) (fun _ => physicalPeriod)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  refine ⟨((hf.continuous.comp e.continuous).norm.pow 2).integrableOn_Icc,?_⟩
  intro i
  exact (((contDiff_spatialWordPartial f hf [i]).continuous.comp e.continuous).norm.pow 2).integrableOn_Icc

/-- Original `unitBoxEnergy_partial_scale` guarantee for the `PhysicalH1Energy` construction; the complete source hypotheses are retained. -/
theorem unitBoxEnergy_partial_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    unitBoxEnergy (spatialWordPartial (fun u => f (physicalPeriod • u)) [i])=
      physicalPeriod^2*unitCubeIntegral (fun u => ‖spatialWordPartial f [i] (physicalPeriod • u)‖^2) := by
  rw [spatialWordPartial_scale f hf physicalPeriod [i],unitBoxEnergy_eq_unitCubeIntegral]
  simp only [List.length_singleton,pow_one,norm_smul,Real.norm_eq_abs,
    abs_of_pos physicalPeriod_pos,mul_pow]
  unfold unitCubeIntegral
  rw [integral_const_mul]

/-- This is the ordinary unnormalized physical cube integral of value
and all three first coordinate derivatives. The cube uses actual
Euclidean volume, as certified by physicalCubeIntegral_eq_volume. -/
theorem physicalFieldH1Energy_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) :
    physicalFieldH1Energy f=physicalPeriod^3*unitFieldH1Energy (fun u => f (physicalPeriod • u)) := by
  unfold physicalFieldH1Energy unitFieldH1Energy
  rw [unitBoxEnergy_eq_unitCubeIntegral]
  simp_rw [physicalCubeIntegral_scale,unitBoxEnergy_partial_scale f hf]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  field_simp [physicalPeriod_pos.ne']

end Qatlib.Concepts.EffectiveGauge.SpectralH1
