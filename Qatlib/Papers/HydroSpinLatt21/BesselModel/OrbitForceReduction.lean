/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.BesselCoefficientBridge
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Circular-orbit kinematics and the tangential force balance reduction

[Saenz2021HydroSpinLattices], Methods equations (9)-(12), restricts each
droplet to a circular orbit of fixed radius `r` about its well centre,
writing the trajectory as `xᵢ(t) = (r cos φᵢ(t) + (i - 1)L, r sin φᵢ(t))`
with angular frequency `ωᵢ = φ̇ᵢ`; the constant well-centre offset
`(i - 1)L x̂` drops out of all velocities and accelerations. Substituting
this ansatz into Newton's law (equation (9)) and projecting onto the radial
and azimuthal unit vectors yields the force balances (10) and (11), and the
azimuthal balance is then rewritten as the phase evolution equation (12).
See [the article](https://doi.org/10.1038/s41586-021-03682-1).

This file proves the exact kinematic content of that substitution for a
general differentiable azimuth `φ(t)`: the velocity of the ansatz is the
vector `r ω θ̂` with azimuthal projection `r ω` and squared speed `(r ω)²`,
the azimuthal projection of the acceleration is the inertial term `r ω̇` of
equation (11), and the radial projection of the acceleration is the
centripetal term `-r ω²` of equation (10) (reappearing in the rotating-frame
equation (31)). The final theorem is the exact algebraic reduction of the
tangential balance (11) to the phase equation (12), with `τ = m_w / D_R` and
`ω₀ = u₀ / r`; no memory, Bessel function or lattice geometry enters here.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Real Qatlib.Papers.HydroSpinLatt21.GKModel

/-! ## Projections on the plane -/

/-- The Euclidean dot product on the plane, used to project forces and
accelerations onto the azimuthal and radial directions of an orbit. -/
def planeDot (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- The radial unit vector `r̂` of an orbit with azimuth `φ`. -/
def radialUnit (φ : ℝ) : ℝ × ℝ := (Real.cos φ, Real.sin φ)

/-! ## Exact kinematics of the circular-orbit ansatz -/

/-- The velocity of the circular-orbit ansatz with radius `r`, angular speed
`ω` and azimuth `φ`, i.e. the vector `r ω θ̂` obtained by differentiating
`(r cos φ, r sin φ)`; `orbitAzimuth` is the azimuthal unit vector `θ̂`. -/
def orbitVelVec (r ω φ : ℝ) : ℝ × ℝ :=
  (r * (-Real.sin φ * ω), r * (Real.cos φ * ω))

/-- The acceleration of the circular-orbit ansatz with radius `r`, angular
speed `ω`, angular acceleration `ωd` and azimuth `φ`, i.e.
`r ω̇ θ̂ - r ω² r̂`. -/
def orbitAccVec (r ω ωd φ : ℝ) : ℝ × ℝ :=
  (r * ((-Real.cos φ * ω) * ω + -Real.sin φ * ωd),
   r * ((-Real.sin φ * ω) * ω + Real.cos φ * ωd))

/-- Exact velocity of the ansatz: if the azimuth is differentiable at `t`
with derivative `ω`, then the trajectory `(r cos φ(t), r sin φ(t))` is
differentiable at `t` with velocity `orbitVelVec r ω (φ t)`, the vector
`r ω θ̂` used in the substitution preceding equation (10). -/
theorem hasDerivAt_orbitCoord_of_angle (r : ℝ) (φ : ℝ → ℝ) (t ω : ℝ)
    (hdφ : HasDerivAt φ ω t) :
    HasDerivAt (fun s => orbitCoord r (φ s)) (orbitVelVec r ω (φ t)) t := by
  have hc : HasDerivAt (fun s => Real.cos (φ s)) (-Real.sin (φ t) * ω) t :=
    (Real.hasDerivAt_cos (φ t)).comp t hdφ
  have hs : HasDerivAt (fun s => Real.sin (φ s)) (Real.cos (φ t) * ω) t :=
    (Real.hasDerivAt_sin (φ t)).comp t hdφ
  exact (HasDerivAt.const_mul r hc).prodMk (HasDerivAt.const_mul r hs)

/-- The azimuthal projection of the orbit velocity is `r ω`: the paper's
identity `ẋ ⋅ θ̂ = r ω` entering equations (10) and (11). -/
theorem orbitVelVec_dot_azimuth (r ω φ : ℝ) :
    planeDot (orbitVelVec r ω φ) (orbitAzimuth φ) = r * ω := by
  show (r * (-Real.sin φ * ω)) * (-Real.sin φ) + (r * (Real.cos φ * ω)) * Real.cos φ
      = r * ω
  calc (r * (-Real.sin φ * ω)) * (-Real.sin φ) + (r * (Real.cos φ * ω)) * Real.cos φ
      = r * ω * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = r * ω := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- The squared speed of the orbit velocity is `(r ω)²`: with the paper's
`u₀ = r ω₀`, the active self-propulsion factor `(r ω)² / u₀²` of equations
(11) and (12) is the squared speed relative to the free-walking speed. -/
theorem orbitVelVec_dot_self (r ω φ : ℝ) :
    planeDot (orbitVelVec r ω φ) (orbitVelVec r ω φ) = (r * ω) ^ 2 := by
  show (r * (-Real.sin φ * ω)) * (r * (-Real.sin φ * ω))
      + (r * (Real.cos φ * ω)) * (r * (Real.cos φ * ω)) = (r * ω) ^ 2
  calc (r * (-Real.sin φ * ω)) * (r * (-Real.sin φ * ω))
      + (r * (Real.cos φ * ω)) * (r * (Real.cos φ * ω))
      = (r * ω) ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = (r * ω) ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- Exact acceleration of the ansatz: if the azimuth is differentiable at
`t` with derivative `ω`, the angular speed function `φ'` satisfies
`φ' t = ω` and is differentiable at `t` with derivative `ωd` (the angular
acceleration), then the velocity of the ansatz is differentiable at `t` with
acceleration `orbitAccVec r ω ωd (φ t)`. -/
theorem hasDerivAt_orbitVelVec (r : ℝ) (φ φ' : ℝ → ℝ) (t ω ωd : ℝ)
    (hdφ : HasDerivAt φ ω t) (hdω : HasDerivAt φ' ωd t) (hω : φ' t = ω) :
    HasDerivAt (fun s => orbitVelVec r (φ' s) (φ s)) (orbitAccVec r ω ωd (φ t)) t := by
  have hc : HasDerivAt (fun s => Real.cos (φ s)) (-Real.sin (φ t) * ω) t :=
    (Real.hasDerivAt_cos (φ t)).comp t hdφ
  have hs : HasDerivAt (fun s => Real.sin (φ s)) (Real.cos (φ t) * ω) t :=
    (Real.hasDerivAt_sin (φ t)).comp t hdφ
  have h1 := (hs.neg.mul hdω).const_mul r
  have h2 := (hc.mul hdω).const_mul r
  rw [hω] at h1 h2
  simp only [Pi.mul_apply, Pi.neg_apply] at h1 h2
  refine (h1.prodMk h2).congr_deriv ?_
  simp only [orbitAccVec, Prod.mk.injEq]
  exact ⟨by ring, trivial⟩

/-- The azimuthal projection of the orbit acceleration is `r ω̇`: the
inertial term on the left-hand side of the tangential balance, equation
(11). -/
theorem orbitAccVec_dot_azimuth (r ω ωd φ : ℝ) :
    planeDot (orbitAccVec r ω ωd φ) (orbitAzimuth φ) = r * ωd := by
  show (r * ((-Real.cos φ * ω) * ω + -Real.sin φ * ωd)) * (-Real.sin φ)
      + (r * ((-Real.sin φ * ω) * ω + Real.cos φ * ωd)) * Real.cos φ = r * ωd
  calc (r * ((-Real.cos φ * ω) * ω + -Real.sin φ * ωd)) * (-Real.sin φ)
      + (r * ((-Real.sin φ * ω) * ω + Real.cos φ * ωd)) * Real.cos φ
      = r * ωd * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = r * ωd := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- The radial projection of the orbit acceleration is `-r ω²`: the
centripetal term on the left-hand side of the radial balance, equation (10),
which reappears in the rotating-frame radial equation (31). -/
theorem orbitAccVec_dot_radial (r ω ωd φ : ℝ) :
    planeDot (orbitAccVec r ω ωd φ) (radialUnit φ) = -(r * ω * ω) := by
  show (r * ((-Real.cos φ * ω) * ω + -Real.sin φ * ωd)) * Real.cos φ
      + (r * ((-Real.sin φ * ω) * ω + Real.cos φ * ωd)) * Real.sin φ = -(r * ω * ω)
  calc (r * ((-Real.cos φ * ω) * ω + -Real.sin φ * ωd)) * Real.cos φ
      + (r * ((-Real.sin φ * ω) * ω + Real.cos φ * ωd)) * Real.sin φ
      = -(r * ω * ω) * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = -(r * ω * ω) := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-! ## From the tangential balance (11) to the phase equation (12) -/

/-- The exact algebraic reduction of the tangential force balance, equation
(11), to the phase evolution equation (12): with the relaxation time
`τ = m_w / D_R`, the preferred angular frequency `ω₀ = u₀ / r` and the
azimuthal wave force `Fθ = F_{i,j} ⋅ θ̂ᵢ`, the balance
`m_w r ω̇ = D_R (1 - (r ω)² / u₀²) r ω + Fθ` is equivalent to
`ω̇ = (1/τ) (1 - ω²/ω₀²) ω + Fθ / (m_w r)`. The reduction only divides by
`m_w r`, so it assumes exactly `m ≠ 0` and `r ≠ 0`; the physical reading
further assumes the standard regime `m_w, r, u₀ > 0` and `D_R > 0`, under
which `τ > 0` and `ω₀ > 0`. -/
theorem tangential_balance_reduction (m r D τ u₀ ω₀ ωdot ω Fθ : ℝ)
    (hm : m ≠ 0) (hr : r ≠ 0)
    (hτ : τ = m / D) (hω₀ : ω₀ = u₀ / r)
    (hbal : m * (r * ωdot) = D * (1 - (r * ω) ^ 2 / u₀ ^ 2) * (r * ω) + Fθ) :
    ωdot = 1 / τ * (1 - ω ^ 2 / ω₀ ^ 2) * ω + Fθ / (m * r) := by
  have hmr : m * r ≠ 0 := mul_ne_zero hm hr
  rw [show (r * ω) ^ 2 = ω ^ 2 * r ^ 2 from by ring] at hbal
  rw [hτ, hω₀]
  rw [show 1 / (m / D) = D / m from by field_simp,
    show ω ^ 2 / (u₀ / r) ^ 2 = ω ^ 2 * r ^ 2 / u₀ ^ 2 from by field_simp]
  refine mul_right_cancel₀ hmr ?_
  rw [add_mul, div_mul_cancel₀ Fθ hmr]
  rw [show D / m * (1 - ω ^ 2 * r ^ 2 / u₀ ^ 2) * ω * (m * r)
      = D * (1 - ω ^ 2 * r ^ 2 / u₀ ^ 2) * (r * ω) from by
    field_simp [hm]]
  exact (show ωdot * (m * r) = m * (r * ωdot) from by ring).trans hbal

end Qatlib.Papers.HydroSpinLatt21.BesselModel

end
