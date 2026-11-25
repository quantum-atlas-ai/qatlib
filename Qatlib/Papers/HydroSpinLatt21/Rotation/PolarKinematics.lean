/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.OrbitForceReduction
public import Qatlib.Papers.HydroSpinLatt21.Rotation.CoriolisRadialBalance
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Kinematics of orbits with time-dependent radius

[Saenz2021HydroSpinLattices], Methods equations (29)-(32), drops the
fixed-radius assumption of equations (9)-(12): the droplet position in its
well is written in polar coordinates as `x(t) = r(t)(cos φ(t), sin φ(t))`
with both the orbital radius and the azimuth time-dependent. Projecting the
acceleration onto the radial and azimuthal directions then produces the
terms of the rotating-frame balances: the radial projection is
`r̈ - r ω²` (the centripetal combination whose vanishing inertia defines
the radial balance (31)) and the azimuthal projection is `r ω̇ + 2ṙω`
(the angular-acceleration and Coriolis-type azimuthal terms entering the
phase equation (32)). See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This file proves these projection identities exactly, for a twice
differentiable radius and azimuth: the velocity decomposition
`ẋ = ṙ r̂ + r ω θ̂`, the radial acceleration projection
`⟨ẍ, r̂⟩ = r̈ - r ω²` and the azimuthal acceleration projection
`⟨ẍ, θ̂⟩ = r ω̇ + 2ṙω`. Together with the fixed-radius identities of
`Qatlib.Papers.HydroSpinLatt21.BesselModel.OrbitForceReduction` these
are the kinematic inputs of equations (31) and (32).

The file also computes the components of the Coriolis term `-2Ω × ẋ` of
equation (29) via the quarter-turn operator `rot90` (radial component
`2Ωωr`, azimuthal component `-2Ωṙ`), and assembles the radial balance:
under the radial Newton balance with the constitutive Coriolis and quartic
well terms of equation (29), the radial acceleration satisfies exactly
`r̈ = coriolisRadialRHS r ω Ω k`, the reduced equation (31). The paper's
simplifying assumptions reducing (29) to (31) are quoted in the article
and are hypotheses of the assembly, not formalized statements.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.Rotation

open Real Qatlib.Papers.HydroSpinLatt21.GKModel
open Qatlib.Papers.HydroSpinLatt21.BesselModel

/-! ## The polar ansatz with time-dependent radius -/

/-- The position of a droplet in polar coordinates with time-dependent
radius `r(t)` and azimuth `φ(t)`, equation (30). -/
def polarPos (r φ : ℝ → ℝ) : ℝ → (ℝ × ℝ) :=
  fun t => (r t * Real.cos (φ t), r t * Real.sin (φ t))

/-- The velocity of the polar ansatz in the form `ṙ r̂ + r ω θ̂`, given the
radial speed function `rd = ṙ` and the angular speed function `ω = φ̇`. -/
def polarVel (r rd φ ω : ℝ → ℝ) : ℝ → (ℝ × ℝ) :=
  fun t => (rd t * Real.cos (φ t) - r t * ω t * Real.sin (φ t),
    rd t * Real.sin (φ t) + r t * ω t * Real.cos (φ t))

/-- The velocity of the polar ansatz is `ṙ r̂ + r ω θ̂` whenever `rd` and
`ω` realize the derivatives of `r` and `φ` at the point. -/
theorem hasDerivAt_polarPos (r rd φ ω : ℝ → ℝ) (t : ℝ)
    (hr : HasDerivAt r (rd t) t) (hφ : HasDerivAt φ (ω t) t) :
    HasDerivAt (polarPos r φ) (polarVel r rd φ ω t) t := by
  have hc : HasDerivAt (fun s => Real.cos (φ s)) (-Real.sin (φ t) * ω t) t :=
    (Real.hasDerivAt_cos (φ t)).comp t hφ
  have hs : HasDerivAt (fun s => Real.sin (φ s)) (Real.cos (φ t) * ω t) t :=
    (Real.hasDerivAt_sin (φ t)).comp t hφ
  have h1 := HasDerivAt.mul hr hc
  have h2 := HasDerivAt.mul hr hs
  refine (h1.prodMk h2).congr_deriv ?_
  simp only [polarVel, Prod.mk.injEq]
  constructor
  · ring
  · ring

/-! ## Acceleration projections -/

/-- The acceleration projections of the polar ansatz: if the radius and
azimuth are twice differentiable at `t` (with second derivatives `rdd` and
`wdot`, and first derivatives realized by `rd` and `ω`), then the
acceleration exists, its radial projection is `r̈ - r ω²`, the centripetal
combination of the radial balance (31), and its azimuthal projection is
`r ω̇ + 2ṙω`, the angular-acceleration and Coriolis-type azimuthal terms
of the phase equation (32). -/
theorem polar_acc_projections (r rd φ ω : ℝ → ℝ) (t rdd wdot : ℝ)
    (hr : HasDerivAt r (rd t) t) (hrd : HasDerivAt rd rdd t)
    (hφ : HasDerivAt φ (ω t) t) (hω : HasDerivAt ω wdot t) :
    ∃ acc : ℝ × ℝ,
      HasDerivAt (polarVel r rd φ ω) acc t
        ∧ planeDot acc (radialUnit (φ t)) = rdd - r t * ω t * ω t
        ∧ planeDot acc (orbitAzimuth (φ t)) = r t * wdot + 2 * rd t * ω t := by
  have hc : HasDerivAt (fun s => Real.cos (φ s)) (-Real.sin (φ t) * ω t) t :=
    (Real.hasDerivAt_cos (φ t)).comp t hφ
  have hs : HasDerivAt (fun s => Real.sin (φ s)) (Real.cos (φ t) * ω t) t :=
    (Real.hasDerivAt_sin (φ t)).comp t hφ
  have hw : HasDerivAt (fun s => r s * ω s) (rd t * ω t + r t * wdot) t :=
    HasDerivAt.mul hr hω
  have hA : HasDerivAt (fun s => rd s * Real.cos (φ s))
      (rdd * Real.cos (φ t) + rd t * (-Real.sin (φ t) * ω t)) t :=
    HasDerivAt.mul hrd hc
  have hB : HasDerivAt (fun s => r s * ω s * Real.sin (φ s))
      ((rd t * ω t + r t * wdot) * Real.sin (φ t)
        + r t * ω t * (Real.cos (φ t) * ω t)) t :=
    HasDerivAt.mul hw hs
  have hC : HasDerivAt (fun s => rd s * Real.sin (φ s))
      (rdd * Real.sin (φ t) + rd t * (Real.cos (φ t) * ω t)) t :=
    HasDerivAt.mul hrd hs
  have hD : HasDerivAt (fun s => r s * ω s * Real.cos (φ s))
      ((rd t * ω t + r t * wdot) * Real.cos (φ t)
        + r t * ω t * (-Real.sin (φ t) * ω t)) t :=
    HasDerivAt.mul hw hc
  refine ⟨(rdd * Real.cos (φ t) + rd t * (-Real.sin (φ t) * ω t)
        - ((rd t * ω t + r t * wdot) * Real.sin (φ t)
          + r t * ω t * (Real.cos (φ t) * ω t)),
      rdd * Real.sin (φ t) + rd t * (Real.cos (φ t) * ω t)
        + ((rd t * ω t + r t * wdot) * Real.cos (φ t)
          + r t * ω t * (-Real.sin (φ t) * ω t))), ?_, ?_, ?_⟩
  · exact (HasDerivAt.sub hA hB).prodMk (HasDerivAt.add hC hD)
  · show (rdd * Real.cos (φ t) + rd t * (-Real.sin (φ t) * ω t)
        - ((rd t * ω t + r t * wdot) * Real.sin (φ t)
          + r t * ω t * (Real.cos (φ t) * ω t))) * Real.cos (φ t)
      + (rdd * Real.sin (φ t) + rd t * (Real.cos (φ t) * ω t)
        + ((rd t * ω t + r t * wdot) * Real.cos (φ t)
          + r t * ω t * (-Real.sin (φ t) * ω t))) * Real.sin (φ t)
      = rdd - r t * ω t * ω t
    calc (rdd * Real.cos (φ t) + rd t * (-Real.sin (φ t) * ω t)
        - ((rd t * ω t + r t * wdot) * Real.sin (φ t)
          + r t * ω t * (Real.cos (φ t) * ω t))) * Real.cos (φ t)
      + (rdd * Real.sin (φ t) + rd t * (Real.cos (φ t) * ω t)
        + ((rd t * ω t + r t * wdot) * Real.cos (φ t)
          + r t * ω t * (-Real.sin (φ t) * ω t))) * Real.sin (φ t)
        = (rdd - r t * ω t * ω t) * (Real.sin (φ t) ^ 2 + Real.cos (φ t) ^ 2) := by
          ring
      _ = rdd - r t * ω t * ω t := by rw [Real.sin_sq_add_cos_sq, mul_one]
  · show (rdd * Real.cos (φ t) + rd t * (-Real.sin (φ t) * ω t)
        - ((rd t * ω t + r t * wdot) * Real.sin (φ t)
          + r t * ω t * (Real.cos (φ t) * ω t))) * (-Real.sin (φ t))
      + (rdd * Real.sin (φ t) + rd t * (Real.cos (φ t) * ω t)
        + ((rd t * ω t + r t * wdot) * Real.cos (φ t)
          + r t * ω t * (-Real.sin (φ t) * ω t))) * Real.cos (φ t)
      = r t * wdot + 2 * rd t * ω t
    calc (rdd * Real.cos (φ t) + rd t * (-Real.sin (φ t) * ω t)
        - ((rd t * ω t + r t * wdot) * Real.sin (φ t)
          + r t * ω t * (Real.cos (φ t) * ω t))) * (-Real.sin (φ t))
      + (rdd * Real.sin (φ t) + rd t * (Real.cos (φ t) * ω t)
        + ((rd t * ω t + r t * wdot) * Real.cos (φ t)
          + r t * ω t * (-Real.sin (φ t) * ω t))) * Real.cos (φ t)
        = (r t * wdot + 2 * rd t * ω t)
            * (Real.sin (φ t) ^ 2 + Real.cos (φ t) ^ 2) := by
          ring
      _ = r t * wdot + 2 * rd t * ω t := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-! ## The Coriolis force components and the radial balance (31) -/

/-- Rotation by a quarter turn in the plane, representing the action of the
cross product with the bath rotation axis on in-plane vectors: for the
Coriolis term `-2Ω × ẋ` of equation (29). -/
def rot90 (p : ℝ × ℝ) : ℝ × ℝ := (-p.2, p.1)

/-- The quarter turn sends the radial direction to the azimuthal one. -/
theorem rot90_radialUnit (φ : ℝ) : rot90 (radialUnit φ) = orbitAzimuth φ :=
  rfl

/-- The quarter turn sends the azimuthal direction to minus the radial
one. -/
theorem rot90_orbitAzimuth (φ : ℝ) : rot90 (orbitAzimuth φ) = -radialUnit φ :=
  rfl

/-- The radial component of the Coriolis force `-2Ω × ẋ` of equation (29)
for the polar velocity `ẋ = ṙ r̂ + r ω θ̂` is `2Ω r ω`, the term entering
the radial balance (31). -/
theorem coriolis_force_radial_proj (r rd φ ω : ℝ → ℝ) (Ω t : ℝ) :
    planeDot (-(2 * Ω) • rot90 (polarVel r rd φ ω t)) (radialUnit (φ t))
      = 2 * Ω * r t * ω t := by
  show -(2 * Ω) * (-(rd t * Real.sin (φ t) + r t * ω t * Real.cos (φ t))) * Real.cos (φ t)
      + -(2 * Ω) * (rd t * Real.cos (φ t) - r t * ω t * Real.sin (φ t)) * Real.sin (φ t)
      = 2 * Ω * r t * ω t
  calc -(2 * Ω) * (-(rd t * Real.sin (φ t) + r t * ω t * Real.cos (φ t))) * Real.cos (φ t)
      + -(2 * Ω) * (rd t * Real.cos (φ t) - r t * ω t * Real.sin (φ t)) * Real.sin (φ t)
      = -(2 * Ω) * (-(r t * ω t))
          * (Real.sin (φ t) ^ 2 + Real.cos (φ t) ^ 2) := by ring
    _ = 2 * Ω * r t * ω t := by
          rw [Real.sin_sq_add_cos_sq, mul_one]
          ring

/-- The azimuthal component of the Coriolis force `-2Ω × ẋ` of equation
(29) is `-2Ω ṙ`, the rotation term of the phase equation (32). -/
theorem coriolis_force_azimuth_proj (r rd φ ω : ℝ → ℝ) (Ω t : ℝ) :
    planeDot (-(2 * Ω) • rot90 (polarVel r rd φ ω t)) (orbitAzimuth (φ t))
      = -(2 * Ω) * rd t := by
  show -(2 * Ω) * (-(rd t * Real.sin (φ t) + r t * ω t * Real.cos (φ t))) * (-Real.sin (φ t))
      + -(2 * Ω) * (rd t * Real.cos (φ t) - r t * ω t * Real.sin (φ t)) * Real.cos (φ t)
      = -(2 * Ω) * rd t
  calc -(2 * Ω) * (-(rd t * Real.sin (φ t) + r t * ω t * Real.cos (φ t))) * (-Real.sin (φ t))
      + -(2 * Ω) * (rd t * Real.cos (φ t) - r t * ω t * Real.sin (φ t)) * Real.cos (φ t)
      = -(2 * Ω) * rd t * (Real.sin (φ t) ^ 2 + Real.cos (φ t) ^ 2) := by ring
    _ = -(2 * Ω) * rd t := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- The radial balance of equation (29) reduces to equation (31): if the
radial Newton balance holds at `t` — the inertial radial acceleration
`r̈ - r ω²` (the radial projection of the acceleration, by
`polar_acc_projections`) balances the Coriolis radial component `2Ωωr`
plus the quartic well force `-4kr³` of equation (29) — then the radial
acceleration satisfies exactly `r̈ = coriolisRadialRHS r ω Ω k`, equation
(31). The Coriolis component and the well force are the constitutive
terms of equation (29); the paper's simplifying assumptions reducing (29)
to (31) are quoted in the module header and not formalized. -/
theorem radial_balance_eq31 (r rd φ ω : ℝ → ℝ) (t rdd wdot Ω k m : ℝ)
    (hr : HasDerivAt r (rd t) t) (hrd : HasDerivAt rd rdd t)
    (hφ : HasDerivAt φ (ω t) t) (hω : HasDerivAt ω wdot t) (hm : m ≠ 0)
    (hbal : m * (rdd - r t * ω t * ω t)
      = m * (2 * Ω * ω t * r t) - m * (4 * k * r t ^ 3)) :
    rdd = coriolisRadialRHS (r t) (ω t) Ω k := by
  obtain ⟨acc, _hacc, hrad, _haz⟩ :=
    polar_acc_projections r rd φ ω t rdd wdot hr hrd hφ hω
  have hlin : m * rdd - m * (r t * ω t * ω t)
      = m * (2 * Ω * ω t * r t) - m * (4 * k * r t ^ 3) := by
    rw [← hbal]
    ring
  have hkey : m * rdd
      = m * (r t * ω t * ω t + 2 * Ω * ω t * r t - 4 * k * r t ^ 3) := by
    linarith [hlin]
  exact mul_left_cancel₀ hm hkey

/-! ## The azimuthal balance and the phase equation (32) -/

/-- The azimuthal balance of equation (29) reduces to the strict polar
form of the phase equation (32): if the azimuthal Newton balance holds at
`t` — the inertial azimuthal acceleration `r ω̇ + 2ṙω` (the azimuthal
projection of the acceleration, by `polar_acc_projections`) balances the
Rayleigh drag term evaluated with the orbital speed alone (the paper's
simplification neglecting the `ṙ` contribution to the drag), the azimuthal
wave force `Fθ`, and the Coriolis azimuthal component `−2Ωṙ` — then

`ω̇ = (1/τ)(1 − ω²/ω₀²) ω + Fθ/(m r) − (2ṙ/r)(Ω + ω)`,

with `τ = m/D` and `ω₀ = u₀/r`. The rotation term agrees with equation
(32) in the article. The polar acceleration `r ω̇ + 2ṙω` and the
azimuthal Coriolis component `−2Ωṙ` give the coefficient `−2ṙ/r`.
The multi-body wave-force sum of equation (32) is represented by `Fθ`. -/
theorem azimuthal_balance_eq32_strict (m : ℝ) (r rd φ ω : ℝ → ℝ)
    (t rdd wdot D u₀ Fθ Ω τ ω₀ : ℝ)
    (hr : HasDerivAt r (rd t) t) (hrd : HasDerivAt rd rdd t)
    (hφ : HasDerivAt φ (ω t) t) (hω : HasDerivAt ω wdot t)
    (hm : m ≠ 0) (hr0 : r t ≠ 0)
    (hτ : τ = m / D) (hω₀ : ω₀ = u₀ / r t)
    (hbal : m * (r t * wdot + 2 * rd t * ω t)
      = D * (1 - (r t * ω t) ^ 2 / u₀ ^ 2) * (r t * ω t) + Fθ
        - m * (2 * Ω * rd t)) :
    wdot = 1 / τ * (1 - ω t ^ 2 / ω₀ ^ 2) * ω t + Fθ / (m * r t)
      - (2 * rd t / r t) * (Ω + ω t) := by
  obtain ⟨acc, _hacc, _hrad, _haz⟩ :=
    polar_acc_projections r rd φ ω t rdd wdot hr hrd hφ hω
  have hmr : m * r t ≠ 0 := mul_ne_zero hm hr0
  rw [hτ, hω₀]
  rw [show 1 / (m / D) = D / m from by field_simp,
    show ω t ^ 2 / (u₀ / r t) ^ 2 = ω t ^ 2 * r t ^ 2 / u₀ ^ 2 from by field_simp]
  refine mul_left_cancel₀ hmr ?_
  field_simp [hm, hr0]
  linear_combination hbal

end Qatlib.Papers.HydroSpinLatt21.Rotation

end
