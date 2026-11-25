/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselMemory
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.GkTrajectory
public import Qatlib.Papers.HydroSpinLatt21.Rotation.CoriolisRadialBalance

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A finite multi-droplet angular reduction

[Saenz2021HydroSpinLattices], Methods equations (14)--(17) and (29)--(32),
are assembled here at the same scalar level for a finite set of droplets.
The memory term is the normalized exponential history of the exact `J₁`
force, the instantaneous term is the `J₀` azimuthal force, the radial
constraint is equation (31), and the rotating-frame projection is the
azimuthal Coriolis term from equation (29).

The theorem records the reduction with an explicit memory error.  Its
assumptions are exactly the two places where a physical derivation enters:
the finite-history approximation and the radial-orbit constraint.  The exact
wave force is retained, so no exchange-symmetric potential is assumed.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open Qatlib.Papers.HydroSpinLatt21.Rotation

/-- The normalized finite-memory `J₁` force received by site `i` from a
finite neighbour set. -/
def finiteMemoryBesselSiteForce {ι : Type*} (F k r L T : ℝ)
    (phase : ι → ℝ → ℝ) (neighbors : ι → Finset ι) (i : ι) (t : ℝ) : ℝ :=
  ∑ j ∈ neighbors i,
    averageOrbitForce T (fun u =>
      leftAzimuthForce (-F) besselJ1Profile k r L
        (phase i (t - u)) (phase j (t - u)))

/-- The instantaneous exact `J₀` azimuthal force summed over all neighbours. -/
def instantaneousBesselSiteForce {ι : Type*} (F k r L : ℝ)
    (phase : ι → ℝ → ℝ) (neighbors : ι → Finset ι) (i : ι) (t : ℝ) : ℝ :=
  ∑ j ∈ neighbors i,
    leftAzimuthForce F besselJ0Slope k r L (phase i t) (phase j t)

/-- The rotating-frame Coriolis contribution in the azimuthal projection. -/
def rotatingCoriolisTangential (Ω : ℝ) (radialSpeed : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(2 * Ω) * radialSpeed t

/-- The radial equation (31) imposed sitewise in a finite multi-droplet
system. -/
def radialOrbitConstraint (r ω Ω k : ℝ) : Prop :=
  coriolisRadialRHS r ω Ω k = 0

/-- A profile-parametric finite-memory force.  This companion definition is
useful for a controlled non-gradient regression where the force profile is
held at a nonzero value. -/
def finiteMemoryProfileForce {ι : Type*} (T : ℝ) (profile : ι → ℝ → ℝ)
    (neighbors : ι → Finset ι) (i : ι) : ℝ → ℝ :=
  fun t => ∑ j ∈ neighbors i,
    averageOrbitForce T (fun u => profile j (t - u))

/-- The corresponding instantaneous profile force. -/
def instantaneousProfileForce {ι : Type*} (profile : ι → ℝ → ℝ)
    (neighbors : ι → Finset ι) (i : ι) : ℝ → ℝ :=
  fun t => ∑ j ∈ neighbors i, profile j t

/-- A single theorem combining finite wave memory, exact non-gradient Bessel
coupling, the radial orbit constraint, and rotating-frame Coriolis projection
for every site of a finite droplet system. -/
theorem multiSite_angular_dynamics_reduction {ι : Type*} [Fintype ι]
    (m τ ω₀ : ι → ℝ) (radius : ι → ℝ → ℝ) (F k L T Ω : ℝ)
    (phase angularAcceleration radialSpeed : ι → ℝ → ℝ)
    (neighbors : ι → Finset ι) (memoryError : ι → ℝ → ℝ)
    (_hT : 0 < T) (hmr : ∀ i t, m i * radius i t ≠ 0)
    (hmemory : ∀ i t,
      finiteMemoryBesselSiteForce F k (radius i t) L T phase neighbors i t =
        instantaneousBesselSiteForce F k (radius i t) L phase neighbors i t +
          memoryError i t)
    (hbalance : ∀ i t,
      m i * radius i t * angularAcceleration i t =
        m i * radius i t * rayleighDrift (τ i) (ω₀ i) (angularAcceleration i t) +
          finiteMemoryBesselSiteForce F k (radius i t) L T phase neighbors i t +
          rotatingCoriolisTangential Ω (radialSpeed i) t)
    (hradial : ∀ i t, radialOrbitConstraint (radius i t)
      (angularAcceleration i t) Ω k)
    (hcoriolis : ∀ i t,
      rotatingCoriolisTangential Ω (radialSpeed i) t = -(2 * Ω) * radialSpeed i t) :
    ∀ i t,
      angularAcceleration i t =
        rayleighDrift (τ i) (ω₀ i) (angularAcceleration i t) +
          (instantaneousBesselSiteForce F k (radius i t) L phase neighbors i t +
            memoryError i t - 2 * Ω * radialSpeed i t) / (m i * radius i t) ∧
        radialOrbitConstraint (radius i t) (angularAcceleration i t) Ω k ∧
        rotatingCoriolisTangential Ω (radialSpeed i) t = -(2 * Ω) * radialSpeed i t := by
  intro i t
  have hmain := hbalance i t
  rw [hmemory i t, hcoriolis i t] at hmain
  have hden := hmr i t
  have hangular : angularAcceleration i t =
      rayleighDrift (τ i) (ω₀ i) (angularAcceleration i t) +
        (instantaneousBesselSiteForce F k (radius i t) L phase neighbors i t +
          memoryError i t - 2 * Ω * radialSpeed i t) / (m i * radius i t) := by
    have hm : m i ≠ 0 := by
      intro h
      apply hden
      simp [h]
    have hr : radius i t ≠ 0 := by
      intro h
      apply hden
      simp [h]
    field_simp [hm, hr]
    linear_combination hmain
  exact ⟨hangular, hradial i t, hcoriolis i t⟩

/-- The same unified reduction with a profile-parametric finite-memory force.
This is the consumer-facing form for an explicitly non-gradient wave profile.
-/
theorem multiSite_profile_angular_dynamics_reduction {ι : Type*} [Fintype ι]
    (m τ ω₀ : ι → ℝ) (radius : ι → ℝ → ℝ) (T Ω k : ℝ)
    (angularAcceleration radialSpeed : ι → ℝ → ℝ)
    (profile : ι → ℝ → ℝ) (neighbors : ι → Finset ι)
    (memoryError : ι → ℝ → ℝ) (_hT : 0 < T)
    (hmr : ∀ i t, m i * radius i t ≠ 0)
    (hmemory : ∀ i t,
      finiteMemoryProfileForce T profile neighbors i t =
        instantaneousProfileForce profile neighbors i t + memoryError i t)
    (hbalance : ∀ i t,
      m i * radius i t * angularAcceleration i t =
        m i * radius i t * rayleighDrift (τ i) (ω₀ i) (angularAcceleration i t) +
          finiteMemoryProfileForce T profile neighbors i t +
          rotatingCoriolisTangential Ω (radialSpeed i) t)
    (hradial : ∀ i t, radialOrbitConstraint (radius i t)
      (angularAcceleration i t) Ω k)
    (hcoriolis : ∀ i t,
      rotatingCoriolisTangential Ω (radialSpeed i) t = -(2 * Ω) * radialSpeed i t) :
    ∀ i t,
      angularAcceleration i t =
        rayleighDrift (τ i) (ω₀ i) (angularAcceleration i t) +
          (instantaneousProfileForce profile neighbors i t + memoryError i t -
            2 * Ω * radialSpeed i t) / (m i * radius i t) ∧
        radialOrbitConstraint (radius i t) (angularAcceleration i t) Ω k ∧
        rotatingCoriolisTangential Ω (radialSpeed i) t = -(2 * Ω) * radialSpeed i t := by
  intro i t
  have hmain := hbalance i t
  rw [hmemory i t, hcoriolis i t] at hmain
  have hden := hmr i t
  have hangular : angularAcceleration i t =
      rayleighDrift (τ i) (ω₀ i) (angularAcceleration i t) +
        (instantaneousProfileForce profile neighbors i t + memoryError i t -
          2 * Ω * radialSpeed i t) / (m i * radius i t) := by
    have hm : m i ≠ 0 := by
      intro h
      apply hden
      simp [h]
    have hr : radius i t ≠ 0 := by
      intro h
      apply hden
      simp [h]
    field_simp [hm, hr]
    linear_combination hmain
  exact ⟨hangular, hradial i t, hcoriolis i t⟩

end Qatlib.Papers.HydroSpinLatt21.BesselModel
