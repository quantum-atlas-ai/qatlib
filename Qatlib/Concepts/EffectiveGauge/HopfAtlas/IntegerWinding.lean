/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Gauge

/-!
# Actual periodic integer-winding lifts of constant spins

These fields include negative winding integers and arbitrary unit initial
quaternions. Their velocity is derived from the actual spatial derivative.
The real linear phase is not asserted to be periodic.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff

namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of winding Linear in the Hopf Atlas construction. -/
def windingLinear (n : Fin 3 → ℤ) : SpatialPoint →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2 (fun j => (n j : ℝ)))

/-- Original `windingLinear_apply` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLinear_apply (n : Fin 3 → ℤ) (x : SpatialPoint) :
    windingLinear n x = ∑ j, (n j : ℝ)*x j := by
  change inner ℝ (WithLp.toLp 2 (fun j => (n j : ℝ)) : SpatialPoint) x = _
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Original `windingLinear_basis` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLinear_basis (n : Fin 3 → ℤ) (j : Fin 3) :
    windingLinear n (EuclideanSpace.single j 1) = (n j : ℝ) := by
  change inner ℝ (WithLp.toLp 2 (fun k => (n k : ℝ)) : SpatialPoint)
      (EuclideanSpace.single j 1) = _
  simpa using EuclideanSpace.inner_single_right j (1 : ℝ)
    (WithLp.toLp 2 (fun k => (n k : ℝ)) : SpatialPoint)

/-- Definition of winding Lift in the Hopf Atlas construction. -/
def windingLift (n : Fin 3 → ℤ) (q0 : ℍ) : QuaternionField :=
  fun x => phase (windingLinear n x)*q0

/-- Original `contDiff_windingLift` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem contDiff_windingLift (n : Fin 3 → ℤ) (q0 : ℍ) :
    ContDiff ℝ ∞ (windingLift n q0) :=
  (contDiff_phase.comp (windingLinear n).contDiff).mul contDiff_const

/-- Original `windingLift_velocity` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_velocity (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖ = 1)
    (hbar : ℝ) (x : SpatialPoint) (j : Fin 3) :
    velocity hbar (windingLift n q0) x j = hbar*(n j : ℝ) := by
  have h := velocity_gauge_unit (x := x) (differentiableAt_const q0)
    (windingLinear n).differentiableAt hq hbar j
  rw [(windingLinear n).hasFDerivAt.fderiv, windingLinear_basis] at h
  change velocity hbar (fun x => phase (windingLinear n x)*q0) x j = _
  simpa [velocity, connection, spatialPartial, connectionValue] using h

/-- Original `windingLinear_lattice` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLinear_lattice (n m : Fin 3 → ℤ) :
    windingLinear n (latticeShift m) = ((∑ j, n j*m j : ℤ) : ℝ)*physicalPeriod := by
  simp [windingLinear_apply, latticeShift, physicalPeriod, Fin.sum_univ_succ]
  ring

/-- Original `phase_int_period` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem phase_int_period (t : ℝ) (m : ℤ) :
    phase (t+(m : ℝ)*physicalPeriod) = phase t := by
  simp [phase, physicalPeriod, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- Original `windingLift_periodic` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_periodic (n : Fin 3 → ℤ) (q0 : ℍ) :
    IsPeriodicField (windingLift n q0) := by
  intro x m
  simp only [windingLift, map_add, windingLinear_lattice, phase_int_period]

/-- Original `windingLift_norm` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_norm (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖ = 1) (x : SpatialPoint) :
    ‖windingLift n q0 x‖ = 1 := by simp [windingLift, norm_mul, hq]

/-- Original `windingLift_hopf` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_hopf (n : Fin 3 → ℤ) (q0 : ℍ) (x : SpatialPoint) :
    hopf (windingLift n q0 x) = hopf q0 := hopf_phase _ _

/-- Original `windingLift_isSmoothUnitLift` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_isSmoothUnitLift (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖ = 1) :
    IsSmoothUnitLift (fun _ => hopf q0) (windingLift n q0) := by
  refine ⟨contDiff_windingLift n q0, ?_⟩
  intro x
  exact ⟨windingLift_norm n q0 hq x, windingLift_hopf n q0 x⟩

/-- Original `windingLift_physical_divergence` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_physical_divergence (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖ = 1)
    (hbar : ℝ) : ∀ x, divergence (velocity hbar (windingLift n q0)) x = 0 := by
  intro x
  unfold divergence
  apply Finset.sum_eq_zero
  intro j _
  have hfun : (fun y => velocity hbar (windingLift n q0) y j) = fun _ => hbar*(n j : ℝ) := by
    funext y
    exact windingLift_velocity n q0 hq hbar y j
  rw [hfun]
  simp

/-- Original `windingLift_solenoidal` guarantee for the `IntegerWinding` construction; the complete source hypotheses are retained. -/
theorem windingLift_solenoidal (n : Fin 3 → ℤ) (q0 : ℍ) (hq : ‖q0‖ = 1) :
    IsSolenoidal (windingLift n q0) := windingLift_physical_divergence n q0 hq 1

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
