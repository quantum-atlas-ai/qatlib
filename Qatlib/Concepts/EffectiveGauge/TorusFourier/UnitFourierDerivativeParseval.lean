/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.UnitFourierParseval
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierIntegrationByParts

set_option backward.isDefEq.respectTransparency false

/-!
# Unit Fourier Derivative Parseval

Torus Fourier constructions for Effective Gauge.
Proves `unitFourierCoefficient_partial_parseval`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The true derivative has exactly the normalized L*k frequency weight
in the actual Lebesgue cube Parseval identity. DC contributes zero. -/
theorem unitFourierCoefficient_partial_parseval (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (i : Fin 3) :
    HasSum (fun k : SpatialFrequency => physicalPeriod^2*(k i : ℝ)^2*
      ‖unitFourierCoefficient f hf.continuous hp k‖^2)
      (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        ‖spatialWordPartial f [i] (WithLp.toLp 2 u)‖^2) := by
  have hs := unitFourierCoefficient_parseval (spatialWordPartial f [i])
    (contDiff_spatialWordPartial f hf [i]).continuous (unitPeriodicField_spatialWordPartial f hf hp [i])
  apply HasSum.congr_fun hs
  intro k
  rw [unitFourierCoefficient_partial f hf hp k i,norm_mul,norm_mul,norm_mul,Complex.norm_I,mul_one]
  simp only [Complex.norm_real,Real.norm_of_nonneg physicalPeriod_pos.le,Complex.norm_intCast]
  rw [mul_pow,mul_pow,sq_abs]

end Qatlib.Concepts.EffectiveGauge.TorusFourier
