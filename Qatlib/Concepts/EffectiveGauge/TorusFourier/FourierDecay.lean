/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierIntegrationByParts

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Decay

Torus Fourier constructions for Effective Gauge.
Proves `unitFourierCoefficient_pure_word`, `fourierFrequencyFactor_norm`, `unitFourierCoefficient_decay`.
-/


set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Repeated integration by parts retains the exact L^n scaling. -/
theorem unitFourierCoefficient_pure_word (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) (i : Fin 3) (n : ℕ) :
    unitFourierCoefficient (spatialWordPartial f (List.replicate n i))
      (contDiff_spatialWordPartial f hf (List.replicate n i)).continuous
      (unitPeriodicField_spatialWordPartial f hf hp (List.replicate n i)) k=
      ((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))^n*unitFourierCoefficient f hf.continuous hp k := by
  induction n with
  | zero => simp only [List.replicate_zero,spatialWordPartial,pow_zero,one_mul]
  | succ n ih =>
    have h := unitFourierCoefficient_partial (spatialWordPartial f (List.replicate n i))
      (contDiff_spatialWordPartial f hf (List.replicate n i))
      (unitPeriodicField_spatialWordPartial f hf hp (List.replicate n i)) k i
    have hnew : unitFourierCoefficient (spatialWordPartial f (List.replicate (n+1) i))
        (contDiff_spatialWordPartial f hf (List.replicate (n+1) i)).continuous
        (unitPeriodicField_spatialWordPartial f hf hp (List.replicate (n+1) i)) k=
        ((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*unitFourierCoefficient
          (spatialWordPartial f (List.replicate n i))
          (contDiff_spatialWordPartial f hf (List.replicate n i)).continuous
          (unitPeriodicField_spatialWordPartial f hf hp (List.replicate n i)) k := by
      simpa only [List.replicate_succ,spatialWordPartial] using h
    rw [hnew,ih,pow_succ]
    ring

/-- Original `fourierFrequencyFactor_norm` guarantee for the `FourierDecay` construction; the complete source hypotheses are retained. -/
theorem fourierFrequencyFactor_norm (k : SpatialFrequency) (i : Fin 3) :
    ‖(physicalPeriod : ℂ)*Complex.I*(k i : ℂ)‖=physicalPeriod*|(k i : ℝ)| := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,Complex.norm_intCast,
    abs_of_pos physicalPeriod_pos,mul_one]

/-- A true n-th derivative bound yields decay of the actual Fourier
coefficient. The source consumer will instantiate n=6 with its stored c6. -/
theorem unitFourierCoefficient_decay (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) (i : Fin 3) (hi : k i≠0)
    (n : ℕ) (M : ℝ) (hb : ∀ x, InUnitCube x →
      ‖spatialWordPartial f (List.replicate n i) x‖ ≤ M) :
    ‖unitFourierCoefficient f hf.continuous hp k‖ ≤ M/(physicalPeriod^n*|(k i : ℝ)|^n) := by
  have h := unitFourierCoefficient_norm_le (spatialWordPartial f (List.replicate n i))
    (contDiff_spatialWordPartial f hf (List.replicate n i)).continuous
    (unitPeriodicField_spatialWordPartial f hf hp (List.replicate n i)) k M hb
  rw [unitFourierCoefficient_pure_word f hf hp k i n,norm_mul,norm_pow,fourierFrequencyFactor_norm] at h
  have hiR : (k i : ℝ)≠0 := Int.cast_ne_zero.mpr hi
  have hpos : 0<physicalPeriod*|(k i : ℝ)| := mul_pos physicalPeriod_pos (abs_pos.mpr hiR)
  rw [← mul_pow]
  apply (le_div_iff₀ (pow_pos hpos n)).mpr
  simpa only [mul_comm] using h

end Qatlib.Concepts.EffectiveGauge.TorusFourier
