/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitComplexIntegral

set_option backward.isDefEq.respectTransparency false

/-!
# Unit Fourier Linear

Torus Fourier constructions for Effective Gauge.
Proves `unitFourierCoefficient_add`, `unitFourierCoefficient_const_mul`, `unitFourierCoefficient_sub`.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitFourierCoefficient_add` guarantee for the `UnitFourierLinear` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_add (f g : SpatialPoint → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hp : IsUnitPeriodicField f) (hpg : IsUnitPeriodicField g) (k : SpatialFrequency) :
    unitFourierCoefficient (fun x => f x+g x) (hf.add hg)
      (by intro x n; dsimp only; rw [hp x n,hpg x n]) k=
      unitFourierCoefficient f hf hp k+unitFourierCoefficient g hg hpg k := by
  simp only [unitFourierCoefficient_eq_cubeIntegral]
  have heq : (fun x => unitFourierMode (-k) x*(f x+g x))=
      (fun x => unitFourierMode (-k) x*f x+unitFourierMode (-k) x*g x) := by
    funext x
    ring
  rw [heq]
  exact unitComplexCubeIntegral_add _ _ ((contDiff_unitFourierMode (-k)).continuous.mul hf)
    ((contDiff_unitFourierMode (-k)).continuous.mul hg)

/-- Original `unitFourierCoefficient_const_mul` guarantee for the `UnitFourierLinear` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_const_mul (c : ℂ) (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) :
    unitFourierCoefficient (fun x => c*f x) (hf.const_mul c)
      (by intro x n; dsimp only; rw [hp x n]) k=c*unitFourierCoefficient f hf hp k := by
  simp only [unitFourierCoefficient_eq_cubeIntegral]
  have heq : (fun x => unitFourierMode (-k) x*(c*f x))=
      (fun x => c*(unitFourierMode (-k) x*f x)) := by funext x; ring
  rw [heq,unitComplexCubeIntegral_const_mul]

/-- Original `unitFourierCoefficient_sub` guarantee for the `UnitFourierLinear` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_sub (f g : SpatialPoint → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hp : IsUnitPeriodicField f) (hpg : IsUnitPeriodicField g) (k : SpatialFrequency) :
    unitFourierCoefficient (fun x => f x-g x) (hf.sub hg)
      (by intro x n; dsimp only; rw [hp x n,hpg x n]) k=
      unitFourierCoefficient f hf hp k-unitFourierCoefficient g hg hpg k := by
  simp only [unitFourierCoefficient_eq_cubeIntegral]
  have heq : (fun x => unitFourierMode (-k) x*(f x-g x))=
      (fun x => unitFourierMode (-k) x*f x+(-1)*(unitFourierMode (-k) x*g x)) := by funext x; ring
  rw [heq,unitComplexCubeIntegral_add
    (fun x => unitFourierMode (-k) x*f x) (fun x => (-1)*(unitFourierMode (-k) x*g x))
    ((contDiff_unitFourierMode (-k)).continuous.mul hf)
    (continuous_const.mul ((contDiff_unitFourierMode (-k)).continuous.mul hg)),unitComplexCubeIntegral_const_mul]
  ring

end Qatlib.Concepts.EffectiveGauge.TorusFourier
