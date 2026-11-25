/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.GkTrajectory
public import Qatlib.Papers.HydroSpinLatt21.GKModel.LatticeEnergy

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact energy balance of the Bessel-coefficient active lattice field

[Saenz2021HydroSpinLattices], Methods equations (23)-(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
This file instantiates the exact energy balance of
`Qatlib.Papers.HydroSpinLatt21.GKModel.LatticeEnergy` for the *actual*
active second-order lattice vector field `gkLatticeRhs` of
`Qatlib.Papers.HydroSpinLatt21.BesselModel.GkTrajectory`, whose pair
forces carry the Bessel coefficients `α = ℱ k_F r J₀''(k_F L)` and
`β = (ℱ r / L) J₀'(k_F L)` of equations (25) and (26). On a symmetric
(mutual-inverse neighbour maps) finite lattice, any trajectory of the field
satisfies: the time derivative of the energy — angular-velocity kinetic
energy with inertia `m r` plus the signed pair potential with the Bessel
coefficients — is exactly the Rayleigh power
`Σ_i (m r/τ)(1 - ω_i²/ω₀²)ω_i²`. The wave-mediated coupling channel cancels
identically by the chain rule; the only non-conservative contribution is the
active Rayleigh friction, which injects energy below the natural orbital
frequency `ω₀ = v₀/r₀` and dissipates above it. This is the paper's
equation-level statement of the balance between wave-mediated coupling
(potential channel, exactly conservative at the GK level) and the active
driving.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel

/-! ## The Bessel-coefficient force sum inside the lattice field -/

/-- The acceleration component of the active lattice field is the Rayleigh
drift plus the signed pair force sum with the Bessel coefficients of
equations (25)-(26), divided by the angular inertia `m r`. -/
theorem gk_lattice_rhs_acceleration_eq {ι : Type*} (F k r L m τ ω₀ : ℝ)
    (left right : ι → ι) (q : AngularState ι) (i : ι) :
    (gkLatticeRhs F k r L m τ ω₀ left right q).2 i
      = rayleighAngularAcceleration τ ω₀ (q.2 i)
        + latticeForceSum (F * k * r * besselJ0Curv (k * L))
            (F * r / L * besselJ0Slope (k * L)) left right q.1 i / (m * r) := by
  rw [gkLatticeRhs]
  simp only [rayleighDrift, rayleighAngularAcceleration, besselGkPairForce,
    gkPairForce, latticeForceSum]

/-- The exact energy balance of the actual active lattice field: along any
trajectory of `gkLatticeRhs` on a symmetric finite lattice, with positive
mass and radius, the derivative of the energy (kinetic energy in the angular
velocities plus the signed pair potential with the Bessel coefficients
`α = ℱ k_F r J₀''(k_F L)` and `β = (ℱ r / L) J₀'(k_F L)`) is exactly the
Rayleigh power. The coupling channel cancels identically. -/
theorem bessel_gk_lattice_energy_balance {ι : Type*} [Fintype ι]
    (F k r L m τ ω₀ : ℝ) (left right : ι → ι)
    (hinv : MutuallyInverse left right) (hm : 0 < m) (hr : 0 < r)
    (Φ W : ι → ℝ → ℝ) (t₀ : ℝ)
    (hkin : ∀ i, HasDerivAt (Φ i) (W i t₀) t₀)
    (hvel : ∀ i, HasDerivAt (W i) ((gkLatticeRhs F k r L m τ ω₀ left right
      ((fun i => Φ i t₀ : ι → ℝ), (fun i => W i t₀ : ι → ℝ))).2 i) t₀) :
    HasDerivAt (fun t => latticeEnergy
        (F * k * r * besselJ0Curv (k * L)) (F * r / L * besselJ0Slope (k * L))
        m r left right (fun i => Φ i t) (fun i => W i t))
      (latticeRayleighPower m r τ ω₀ (fun i => W i t₀)) t₀ := by
  have hmr : m * r ≠ 0 := mul_ne_zero hm.ne' hr.ne'
  refine lattice_energy_balance
    (F * k * r * besselJ0Curv (k * L)) (F * r / L * besselJ0Slope (k * L))
    m r τ ω₀ left right hinv Φ W
    (fun i t => (gkLatticeRhs F k r L m τ ω₀ left right
      ((fun i => Φ i t : ι → ℝ), (fun i => W i t : ι → ℝ))).2 i) t₀ hkin hvel
    fun i => ?_
  rw [gk_lattice_rhs_acceleration_eq]
  rw [mul_add, mul_div_cancel₀ _ hmr]

end Qatlib.Papers.HydroSpinLatt21.BesselModel

end
