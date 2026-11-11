/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.UnitFourierParseval
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierDecay

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Higher Energy

Torus Fourier constructions for Effective Gauge.
Proves `unitFourierCoefficient_pure_parseval`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitFourierCoefficient_pure_parseval` guarantee for the `FourierHigherEnergy` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_pure_parseval (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (i : Fin 3) (n : ℕ) :
    HasSum (fun k : SpatialFrequency => physicalPeriod^(2*n)*(k i : ℝ)^(2*n)*
      ‖unitFourierCoefficient f hf.continuous hp k‖^2)
      (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        ‖spatialWordPartial f (List.replicate n i) (WithLp.toLp 2 u)‖^2) := by
  have hs := unitFourierCoefficient_parseval (spatialWordPartial f (List.replicate n i))
    (contDiff_spatialWordPartial f hf (List.replicate n i)).continuous
    (unitPeriodicField_spatialWordPartial f hf hp (List.replicate n i))
  apply HasSum.congr_fun hs
  intro k
  rw [unitFourierCoefficient_pure_word f hf hp k i n]
  have heven : |(k i : ℝ)|^(2*n)=(k i : ℝ)^(2*n) := by rw [pow_mul,pow_mul,sq_abs]
  rw [norm_mul,norm_pow,fourierFrequencyFactor_norm]
  simp only [mul_pow,← pow_mul,Nat.mul_comm n 2,heven]

end Qatlib.Concepts.EffectiveGauge.TorusFourier
