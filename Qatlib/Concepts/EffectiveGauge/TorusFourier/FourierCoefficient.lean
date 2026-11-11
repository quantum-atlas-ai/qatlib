/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitTorusDescent
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Coefficient

Torus Fourier constructions for Effective Gauge.
Defines `unitFourierCoefficient`.
Proves `unitFourierCoefficient_eq_integral`, `unitCoefficientBox_volume`, `unitFourierCoefficient_norm_le`.
-/


set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of unit Fourier Coefficient in the Torus Fourier construction. -/
def unitFourierCoefficient (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (unitTorusContinuousLift f hf hp) k

/-- The actual torus coefficient is the actual Lebesgue integral on the
unit coordinate box. No quadrature or Fourier identity is supplied as input. -/
theorem unitFourierCoefficient_eq_integral (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) :
    unitFourierCoefficient f hf hp k=
      ∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        unitFourierMode (-k) (WithLp.toLp 2 u)*f (WithLp.toLp 2 u) := by
  rw [unitFourierCoefficient,UnitAddTorus.mFourierCoeff_eq_integral _ k (fun _ => 0)]
  have hset : {x : Fin 3 → ℝ | ∀ i, x i∈Ioc (0 : ℝ) (0+1)}=
      Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1) := by
    ext x
    simp only [zero_add,Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,true_implies]
  rw [hset]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [unitFourierMode_eq_mFourier]
  change UnitAddTorus.mFourier (-k) (unitTorusProjection (WithLp.toLp 2 u))*
    unitTorusContinuousLift f hf hp (unitTorusProjection (WithLp.toLp 2 u))=_
  rw [unitTorusContinuousLift_apply]
  rfl

/-- Original `unitCoefficientBox_volume` guarantee for the `FourierCoefficient` construction; the complete source hypotheses are retained. -/
theorem unitCoefficientBox_volume :
    volume (Set.pi Set.univ (fun _ : Fin 3 => Ioc (0 : ℝ) 1))=1 := by
  change Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1))=1
  rw [Measure.pi_pi]
  simp

/-- The coefficient norm bound consumes a true bound on the original
function over the unit cube, not a bound on its unknown coefficients. -/
theorem unitFourierCoefficient_norm_le (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) (M : ℝ)
    (hb : ∀ x, InUnitCube x → ‖f x‖ ≤ M) : ‖unitFourierCoefficient f hf hp k‖ ≤ M := by
  rw [unitFourierCoefficient_eq_integral]
  have hfinite : volume (Set.pi Set.univ (fun _ : Fin 3 => Ioc (0 : ℝ) 1))<⊤ := by
    rw [unitCoefficientBox_volume]
    exact ENNReal.one_lt_top
  have hbound := norm_setIntegral_le_of_norm_le_const hfinite
    (f := fun u : Fin 3 → ℝ => unitFourierMode (-k) (WithLp.toLp 2 u)*f (WithLp.toLp 2 u))
    (C := M) (by
      intro u hu
      rw [norm_mul,unitFourierMode_norm,one_mul]
      apply hb
      intro i
      have hi := hu i (Set.mem_univ i)
      exact ⟨hi.1.le,hi.2⟩)
  simpa only [Measure.real,unitCoefficientBox_volume,ENNReal.toReal_one,mul_one] using hbound

/-- A single actual mode has precisely its Kronecker coefficient, including
DC. This also fixes the coefficient sign convention independently of IBP. -/
theorem unitFourierCoefficient_mode (l k : SpatialFrequency) :
    unitFourierCoefficient (unitFourierMode l) (contDiff_unitFourierMode l).continuous
      (unitFourierMode_periodic l) k=if k=l then 1 else 0 := by
  have heq : unitTorusContinuousLift (unitFourierMode l) (contDiff_unitFourierMode l).continuous
      (unitFourierMode_periodic l)=UnitAddTorus.mFourier l := by
    ext z
    obtain ⟨x,rfl⟩ := unitTorusProjection_quotient.surjective z
    rw [unitTorusContinuousLift_apply]
    exact unitFourierMode_eq_mFourier l x
  rw [unitFourierCoefficient,heq]
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 3)) k l
  simpa only [ContinuousMap.inner_toLp,← UnitAddTorus.mFourier_neg,
    UnitAddTorus.mFourierCoeff,smul_eq_mul,mul_comm] using h

end Qatlib.Concepts.EffectiveGauge.TorusFourier
