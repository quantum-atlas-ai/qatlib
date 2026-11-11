/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.UnitFourierLinear
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonTruncation

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Finite Coefficient

Torus Fourier constructions for Effective Gauge.
Proves `unitPeriodicField_finset_sum`, `unitFourierCoefficient_finset_sum`, `contDiff_unitFourierTruncation`.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitPeriodicField_finset_sum` guarantee for the `FourierFiniteCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitPeriodicField_finset_sum {α : Type*} (s : Finset α) (f : α → SpatialPoint → ℂ)
    (hp : ∀ i, IsUnitPeriodicField (f i)) : IsUnitPeriodicField (fun x => ∑ i∈s, f i x) := by
  intro x n
  dsimp only
  exact Finset.sum_congr rfl (fun i _ => hp i x n)

/-- Original `unitFourierCoefficient_finset_sum` guarantee for the `FourierFiniteCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_finset_sum {α : Type*} (s : Finset α) (f : α → SpatialPoint → ℂ)
    (hf : ∀ i, Continuous (f i)) (hp : ∀ i, IsUnitPeriodicField (f i)) (k : SpatialFrequency) :
    unitFourierCoefficient (fun x => ∑ i∈s, f i x) (continuous_finsetSum s (fun i _ => hf i))
      (unitPeriodicField_finset_sum s f hp) k=∑ i∈s, unitFourierCoefficient (f i) (hf i) (hp i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitFourierCoefficient_eq_cubeIntegral,unitComplexCubeIntegral]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [unitFourierCoefficient_add (f i) (fun x => ∑ j∈s, f j x) (hf i)
      (continuous_finsetSum s (fun j _ => hf j)) (hp i) (unitPeriodicField_finset_sum s f hp),ih]

/-- Original `contDiff_unitFourierTruncation` guarantee for the `FourierFiniteCoefficient` construction; the complete source hypotheses are retained. -/
theorem contDiff_unitFourierTruncation (a : SpatialFrequency → ℂ) (N : ℕ) :
    ContDiff ℝ ∞ (unitFourierTruncation a N) := by
  exact ContDiff.sum (fun k _ => contDiff_const.mul (contDiff_unitFourierMode k))

/-- Original `unitPeriodic_unitFourierTruncation` guarantee for the `FourierFiniteCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitPeriodic_unitFourierTruncation (a : SpatialFrequency → ℂ) (N : ℕ) :
    IsUnitPeriodicField (unitFourierTruncation a N) := by
  apply unitPeriodicField_finset_sum
  intro k x n
  dsimp only
  rw [unitFourierMode_periodic k x n]

/-- The finite cube has exactly its stored coefficients inside the cube
and zero outside, with no assumption of a conjugate pairing. -/
theorem unitFourierCoefficient_truncation (a : SpatialFrequency → ℂ) (N : ℕ) (k : SpatialFrequency) :
    unitFourierCoefficient (unitFourierTruncation a N) (contDiff_unitFourierTruncation a N).continuous
      (unitPeriodic_unitFourierTruncation a N) k=if k∈Finset.Icc (-N : SpatialFrequency) N then a k else 0 := by
  classical
  change unitFourierCoefficient (fun x => ∑ l∈Finset.Icc (-N : SpatialFrequency) N, a l*unitFourierMode l x) _ _ k=_
  rw [unitFourierCoefficient_finset_sum _ _
    (fun l => (contDiff_unitFourierMode l).continuous.const_mul (a l))
    (fun l x n => by rw [unitFourierMode_periodic l x n])]
  calc
    _ = ∑ l∈Finset.Icc (-N : SpatialFrequency) N, a l*(if k=l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro l hl
      change unitFourierCoefficient (fun x => a l*unitFourierMode l x) _ _ k=_
      rw [unitFourierCoefficient_const_mul (a l) (unitFourierMode l)
        (contDiff_unitFourierMode l).continuous (unitFourierMode_periodic l) k,unitFourierCoefficient_mode]
    _ = _ := by simp [mul_ite]

end Qatlib.Concepts.EffectiveGauge.TorusFourier
