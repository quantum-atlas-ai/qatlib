/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.MultiSiteDynamics
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.OrbitForceReduction

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace QatlibTests.HydroSpinLatticePartBRegression

open Set
open Qatlib.Papers.HydroSpinLatt21.BesselModel
open Qatlib.Papers.HydroSpinLatt21.Rotation

private def twoSiteNeighbors (i : Fin 2) : Finset (Fin 2) :=
  if i = 0 then {1} else {0}

private def activeProfile (_ : Fin 2) (_ : ℝ) : ℝ := 3

private def activeRadius : Fin 2 → ℝ → ℝ := fun _ _ => 1

private def activeAngularAcceleration : Fin 2 → ℝ → ℝ := fun _ _ => 1

private def activeRadialSpeed : Fin 2 → ℝ → ℝ := fun _ _ => 1

private theorem active_average_orbit_force :
    averageOrbitForce (1 : ℝ) (fun _ : ℝ => 3) = 3 := by
  rw [averageOrbitForce, MeasureTheory.integral_const_mul,
    (exp_weight_Ioi (1 : ℝ) (by norm_num)).2]
  norm_num

private theorem active_profile_memory (i : Fin 2) (t : ℝ) :
    finiteMemoryProfileForce 1 activeProfile twoSiteNeighbors i t = 3 := by
  fin_cases i <;>
    simp [finiteMemoryProfileForce, activeProfile, twoSiteNeighbors]
  all_goals exact active_average_orbit_force

private theorem active_profile_instantaneous (i : Fin 2) (t : ℝ) :
    instantaneousProfileForce activeProfile twoSiteNeighbors i t = 3 := by
  fin_cases i <;> simp [instantaneousProfileForce, activeProfile, twoSiteNeighbors]

private theorem active_profile_radial (i : Fin 2) (t : ℝ) :
    radialOrbitConstraint (activeRadius i t) (activeAngularAcceleration i t)
      1 (3 / 4) := by
  simp [radialOrbitConstraint, activeRadius, activeAngularAcceleration,
    coriolisRadialRHS]
  norm_num

private theorem active_profile_balance (i : Fin 2) (t : ℝ) :
    (1 : ℝ) * activeRadius i t * activeAngularAcceleration i t =
      (1 : ℝ) * activeRadius i t * rayleighDrift 1 1 (activeAngularAcceleration i t) +
        finiteMemoryProfileForce 1 activeProfile twoSiteNeighbors i t +
        rotatingCoriolisTangential 1 (activeRadialSpeed i) t := by
  rw [active_profile_memory]
  simp [activeRadius, activeAngularAcceleration, activeRadialSpeed,
    rotatingCoriolisTangential, rayleighDrift]
  norm_num

private theorem active_profile_coriolis (i : Fin 2) (t : ℝ) :
    rotatingCoriolisTangential 1 (activeRadialSpeed i) t =
      -(2 * (1 : ℝ)) * activeRadialSpeed i t := by
  rfl

/-- The concrete two-site witness uses a nonzero profile force `3` at both
sites for every time in the comparison window.  The site angular velocities
are both `1`, so their circular-orbit velocities are strictly nonzero. -/
example :
    (∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
      0 < instantaneousProfileForce activeProfile twoSiteNeighbors i t) ∧
    (∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
      orbitVelVec 1 1 (t + (i : ℝ)) ≠ 0) := by
  constructor
  · intro i t ht
    rw [active_profile_instantaneous]
    norm_num
  · intro i t ht hzero
    have hnorm := orbitVelVec_dot_self 1 1 (t + (i : ℝ))
    rw [hzero] at hnorm
    simp [planeDot] at hnorm

/-- The unified theorem is consumed by the same non-degenerate two-site
instance, retaining memory, radial, and Coriolis premises in one call. -/
example : ∀ i : Fin 2, ∀ t : ℝ,
    activeAngularAcceleration i t =
        rayleighDrift 1 1 (activeAngularAcceleration i t) +
          (instantaneousProfileForce activeProfile twoSiteNeighbors i t +
            (0 : ℝ) - 2 * (1 : ℝ) * activeRadialSpeed i t) /
            (1 * activeRadius i t) ∧
        radialOrbitConstraint (activeRadius i t) (activeAngularAcceleration i t)
          1 (3 / 4) ∧
        rotatingCoriolisTangential 1 (activeRadialSpeed i) t =
          -(2 * (1 : ℝ)) * activeRadialSpeed i t := by
  intro i t
  exact multiSite_profile_angular_dynamics_reduction
    (m := fun _ => 1) (radius := activeRadius) (τ := fun _ => 1)
    (ω₀ := fun _ => 1) (T := 1) (Ω := 1) (k := 3 / 4)
    (angularAcceleration := activeAngularAcceleration)
    (radialSpeed := activeRadialSpeed) (profile := activeProfile)
    (neighbors := twoSiteNeighbors) (memoryError := fun _ _ => 0)
    (by norm_num) (by intro j s; norm_num [activeRadius])
    (by intro j s; rw [active_profile_memory, active_profile_instantaneous]; ring)
    (by intro j s; exact active_profile_balance j s)
    (by intro j s; exact active_profile_radial j s)
    (by intro j s; exact active_profile_coriolis j s) i t

end QatlibTests.HydroSpinLatticePartBRegression
