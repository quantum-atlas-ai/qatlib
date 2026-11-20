/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierFiniteCoefficient
public import Qatlib.Concepts.EffectiveGauge.TorusFourier.UnitFourierDerivativeParseval

@[expose] public section

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

/-- Subtracting the radius-`N` Fourier truncation with arbitrary coefficients from a smooth field leaves a smooth residual. -/
theorem contDiff_unitFourierResidual (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (a : SpatialFrequency → ℂ) (N : ℕ) : ContDiff ℝ ∞ (unitFourierResidual f a N) :=
  hf.sub (contDiff_unitFourierTruncation a N)

/-- The residual after subtracting a finite Fourier truncation from a unit-periodic field is unit-periodic. -/
theorem unitPeriodic_unitFourierResidual (f : SpatialPoint → ℂ) (hp : IsUnitPeriodicField f)
    (a : SpatialFrequency → ℂ) (N : ℕ) : IsUnitPeriodicField (unitFourierResidual f a N) := by
  intro x n
  change f (x+unitIntegerShift n)-unitFourierTruncation a N (x+unitIntegerShift n)=f x-unitFourierTruncation a N x
  rw [hp x n,unitPeriodic_unitFourierTruncation a N x n]

/-- For a smooth unit-periodic field, the residual coefficient at `k` is the original coefficient
minus `a k` inside the radius-`N` cube. Outside the cube it is the original coefficient. -/
theorem unitFourierCoefficient_residual (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) (k : SpatialFrequency) :
    unitFourierCoefficient (unitFourierResidual f a N) (contDiff_unitFourierResidual f hf a N).continuous
      (unitPeriodic_unitFourierResidual f hp a N) k=
      unitFourierCoefficient f hf.continuous hp k-(if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0) := by
  change unitFourierCoefficient (fun x => f x-unitFourierTruncation a N x) _ _ k=_
  rw [unitFourierCoefficient_sub f (unitFourierTruncation a N) hf.continuous
    (contDiff_unitFourierTruncation a N).continuous hp (unitPeriodic_unitFourierTruncation a N),unitFourierCoefficient_truncation]

/-- For a smooth unit-periodic field, the squared moduli of the residual coefficients sum to the integral of the squared residual norm over the unit box. -/
theorem unitFourierResidual_parseval (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (a : SpatialFrequency → ℂ) (N : ℕ) :
    HasSum (fun k : SpatialFrequency =>
      ‖unitFourierCoefficient f hf.continuous hp k-(if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0)‖^2)
      (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        ‖unitFourierResidual f a N (WithLp.toLp 2 u)‖^2) := by
  have hs := unitFourierCoefficient_parseval (unitFourierResidual f a N)
    (contDiff_unitFourierResidual f hf a N).continuous (unitPeriodic_unitFourierResidual f hp a N)
  exact HasSum.congr_fun hs (fun k => by rw [unitFourierCoefficient_residual f hf hp a N k])

/-- For a smooth unit-periodic field, the squared residual coefficients weighted by `physicalPeriod^2*(k i)^2` sum to the unit-box energy of the residual's first derivative in direction `i`. -/
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
