/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierFiniteCoefficient
import Qatlib.Concepts.EffectiveGauge.TorusFourier.UnitFourierDerivativeParseval

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Residual Parseval

Torus Fourier constructions for Effective Gauge.
Defines `unitFourierResidual`.
Proves `contDiff_unitFourierResidual`, `unitPeriodic_unitFourierResidual`, `unitFourierCoefficient_residual`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of unit Fourier Residual in the Torus Fourier construction. -/
def unitFourierResidual (f : SpatialPoint → ℂ) (a : SpatialFrequency → ℂ) (N : ℕ) : SpatialPoint → ℂ :=
  fun x => f x-unitFourierTruncation a N x

/-- Original `contDiff_unitFourierResidual` guarantee for the `FourierResidualParseval` construction; the complete source hypotheses are retained. -/
theorem contDiff_unitFourierResidual (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (a : SpatialFrequency → ℂ) (N : ℕ) : ContDiff ℝ ∞ (unitFourierResidual f a N) :=
  hf.sub (contDiff_unitFourierTruncation a N)

/-- Original `unitPeriodic_unitFourierResidual` guarantee for the `FourierResidualParseval` construction; the complete source hypotheses are retained. -/
theorem unitPeriodic_unitFourierResidual (f : SpatialPoint → ℂ) (hp : IsUnitPeriodicField f)
    (a : SpatialFrequency → ℂ) (N : ℕ) : IsUnitPeriodicField (unitFourierResidual f a N) := by
  intro x n
  change f (x+unitIntegerShift n)-unitFourierTruncation a N (x+unitIntegerShift n)=f x-unitFourierTruncation a N x
  rw [hp x n,unitPeriodic_unitFourierTruncation a N x n]

/-- Original `unitFourierCoefficient_residual` guarantee for the `FourierResidualParseval` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_residual (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) (k : SpatialFrequency) :
    unitFourierCoefficient (unitFourierResidual f a N) (contDiff_unitFourierResidual f hf a N).continuous
      (unitPeriodic_unitFourierResidual f hp a N) k=
      unitFourierCoefficient f hf.continuous hp k-(if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0) := by
  change unitFourierCoefficient (fun x => f x-unitFourierTruncation a N x) _ _ k=_
  rw [unitFourierCoefficient_sub f (unitFourierTruncation a N) hf.continuous
    (contDiff_unitFourierTruncation a N).continuous hp (unitPeriodic_unitFourierTruncation a N),unitFourierCoefficient_truncation]

/-- Original `unitFourierResidual_parseval` guarantee for the `FourierResidualParseval` construction; the complete source hypotheses are retained. -/
theorem unitFourierResidual_parseval (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) :
    HasSum (fun k : SpatialFrequency =>
      ‖unitFourierCoefficient f hf.continuous hp k-(if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0)‖^2)
      (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        ‖unitFourierResidual f a N (WithLp.toLp 2 u)‖^2) := by
  have hs := unitFourierCoefficient_parseval (unitFourierResidual f a N)
    (contDiff_unitFourierResidual f hf a N).continuous (unitPeriodic_unitFourierResidual f hp a N)
  exact HasSum.congr_fun hs (fun k => by rw [unitFourierCoefficient_residual f hf hp a N k])

/-- Original `unitFourierResidual_partial_parseval` guarantee for the `FourierResidualParseval` construction; the complete source hypotheses are retained. -/
theorem unitFourierResidual_partial_parseval (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) (i : Fin 3) :
    HasSum (fun k : SpatialFrequency => physicalPeriod^2*(k i : ℝ)^2*
      ‖unitFourierCoefficient f hf.continuous hp k-(if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0)‖^2)
      (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        ‖spatialWordPartial (unitFourierResidual f a N) [i] (WithLp.toLp 2 u)‖^2) := by
  have hs := unitFourierCoefficient_partial_parseval (unitFourierResidual f a N)
    (contDiff_unitFourierResidual f hf a N) (unitPeriodic_unitFourierResidual f hp a N) i
  exact HasSum.congr_fun hs (fun k => by rw [unitFourierCoefficient_residual f hf hp a N k])

end Qatlib.Concepts.EffectiveGauge.TorusFourier
