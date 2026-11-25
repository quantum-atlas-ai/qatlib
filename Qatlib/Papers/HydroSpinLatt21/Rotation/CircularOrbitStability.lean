/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.Rotation.PolarKinematics
public import Qatlib.Papers.HydroSpinLatt21.SingleSpin.QuarticSpin
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormDet

@[expose] public section

/-!
# Analytic circular-orbit conditions and linear stability in the rotating frame

[Saenz2021HydroSpinLattices], Methods section "Bath rotation", develops the
rotating-frame extension of the spin model used for Fig. 3e-h: equation (29)
adds the Coriolis force `-2Ω × ẋ` and the quartic well force `-4k|x|²x` to
the Rayleigh trajectory equation, equation (30) writes the position in polar
coordinates with time-dependent radius, and after the four simplifications
stated in the article (neglecting `ṙ` in the Rayleigh drag, the Rayleigh drag
in the radial balance, the wave force in the radial balance, and the radius
dependence of `α`, `β`) these reduce to the radial balance (31)
`r̈ = rω² + 2Ωω r - 4kr³` and the phase equation (32). These equations were
verified against the fixed article source; the article's last numbered
Methods equation is (32). Its rotation term `-(2ṙ/r)(Ω + ω)` is derived
in `Qatlib.Papers.HydroSpinLatt21.Rotation.PolarKinematics`
(see `azimuthal_balance_eq32_strict`). See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This file analyses a single-droplet reduction of equations (31) and (32) at the
phase-oscillator level used for equations (1), (16) and (23) of the article,
where the preferred orbital frequency `ω₀` is a fixed parameter of the
Rayleigh term `rayleighDrift τ ω₀ ω` (that is, `ω₀ = u₀/r₀` at the reference
radius, not re-evaluated at the instantaneous radius), with the multi-body
wave force set to zero. Equation (32) has rotation coupling coefficient
`κ = 2`. The results below hold for every `κ > 0`.

Main results:

* Circular orbits are exactly the states `(r*, 0, ±ω₀)` with `r*` the radial
  equilibrium of equation (31): the co-rotating branch `ω* = ω₀ > 0` exists
  for every `Ω > -ω₀/2` (in particular every `Ω ≥ 0`) with radius strictly
  increasing in `Ω`; the counter-rotating branch `ω* = -ω₀` exists exactly
  for `Ω < ω₀/2`, with radius strictly smaller than the co-rotating one and
  shrinking to zero as `Ω → ω₀/2`. At reduced level this is an analytic
  threshold at which the counter-rotating circular orbit ceases to exist
  (non-existence, not a proven dynamical instability).
* The system linearization at the orbit is the explicit matrix `spinJacobian`
  (its entries are the exact one-variable derivatives of the field
  components), and it is non-degenerate: `det (spinJacobian) ≠ 0`.
* The characteristic polynomial is
  `λ³ + (2/τ)λ² + (2κ(ω*+Ω)² + 2ω*(ω*+2Ω))λ + (4/τ)ω*(ω*+2Ω)`, whose
  Routh-Hurwitz determinant collapses to `a₁a₂ - a₃ = (4κ/τ)(ω*+Ω)² > 0`.
  A self-contained proof of the cubic Routh-Hurwitz criterion
  (`cubic_re_neg_of_routh_hurwitz`) then shows that every characteristic
  root lies in the open left half-plane whenever the orbit exists: within
  this reduced model no existing circular orbit is linearly unstable, for
  either rotation sense.
* The quadratic form `orbitLyapunov` satisfies along every solution of the
  linearized system the exact dissipation identity
  `d/dt orbitLyapunov = -(8r*²/(κτ))σ²`, so the linearized energy is
  non-increasing (`orbitLyapunov_nonincreasing`).

Not covered (boundaries): the upgrade from spectral stability to exponential
decay of solutions (matrix exponentials) and from the linearization to local
nonlinear asymptotic stability of the full coupled system; the instantaneous-radius
Rayleigh prefactor `1 - r²ω²/u₀²` in equation (32) (its linearization carries an additional
radial-Rayleigh coupling entry); trefoil trajectories and the `γ > γ_c`
regime; multi-droplet wave forces; and the experimental polarization
threshold `Ω_c ≈ 0.22 rad s⁻¹` of Fig. 3e, which is a collective-order
transition and is not identified with the reduced single-drop existence
threshold `ω₀/2`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.Rotation

open Qatlib.Papers.HydroSpinLatt21.BesselModel
open Qatlib.Papers.HydroSpinLatt21.SingleSpin
open Filter Polynomial Set

/-! ## The coupled single-spin rotating-frame system -/

/-- The right-hand side of the rotating-frame phase equation for a single
droplet: the Rayleigh drift towards the preferred orbital frequency `ω₀`, as
in equations (1), (16) and (23) of [Saenz2021HydroSpinLattices], minus the
rotation coupling with coefficient `κ` (`κ = 2` in equation (32), as
derived in `azimuthal_balance_eq32_strict`). The wave force is set to zero. -/
def rotationPhaseRHS (κ τ ω₀ Ω r v ω : ℝ) : ℝ :=
  rayleighDrift τ ω₀ ω - κ * (v / r) * (Ω + ω)

/-- The coupled single-droplet rotating-frame system in the coordinates
`(r, v, ω)`: the radial balance (31) for `r̈` and the fixed-`ω₀`
phase equation for `ω̇` with zero wave force. -/
def rotatingSpinField (κ k τ ω₀ Ω : ℝ) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  fun p => (p.2.1, coriolisRadialRHS p.1 p.2.2 Ω k,
    rotationPhaseRHS κ τ ω₀ Ω p.1 p.2.1 p.2.2)

/-- The Rayleigh drift vanishes at the reference frequency. -/
theorem rayleighDrift_self_eq_zero (τ ω₀ : ℝ) (hω₀ : ω₀ ≠ 0) :
    rayleighDrift τ ω₀ ω₀ = 0 := by
  unfold rayleighDrift
  field_simp [hω₀]
  ring

/-- The Rayleigh drift also vanishes at the reversed reference frequency. -/
theorem rayleighDrift_neg_self_eq_zero (τ ω₀ : ℝ) (hω₀ : ω₀ ≠ 0) :
    rayleighDrift τ ω₀ (-ω₀) = 0 := by
  unfold rayleighDrift
  rw [neg_sq]
  field_simp [hω₀]
  ring

/-- Characterization of the circular orbits of the coupled system: with a
positive radius, non-vanishing well stiffness and Rayleigh parameters, the
equilibria of `rotatingSpinField` are exactly the states with zero radial
velocity, angular velocity `±ω₀`, and radial balance
`4kr² = ω(ω + 2Ω)`. The zero-frequency stationary point of the Rayleigh
drift is eliminated by the radial balance, since `k ≠ 0` and `r > 0` force
`-4kr³ ≠ 0`. -/
theorem rotatingSpinField_eq_zero_iff (κ k τ ω₀ Ω : ℝ) (p : ℝ × ℝ × ℝ)
    (hk : k ≠ 0) (hτ : τ ≠ 0) (hω₀ : ω₀ ≠ 0) (hr : 0 < p.1) :
    rotatingSpinField κ k τ ω₀ Ω p = 0 ↔
      p.2.1 = 0 ∧ (p.2.2 = ω₀ ∨ p.2.2 = -ω₀)
        ∧ 4 * k * p.1 ^ 2 = p.2.2 * (p.2.2 + 2 * Ω) := by
  constructor
  · intro hz
    unfold rotatingSpinField at hz
    have hv : p.2.1 = 0 := congrArg Prod.fst hz
    have hrad : coriolisRadialRHS p.1 p.2.2 Ω k = 0 :=
      congrArg Prod.fst (congrArg Prod.snd hz)
    have hph : rotationPhaseRHS κ τ ω₀ Ω p.1 p.2.1 p.2.2 = 0 :=
      congrArg Prod.snd (congrArg Prod.snd hz)
    unfold rotationPhaseRHS at hph
    rw [hv, zero_div, mul_zero, zero_mul, sub_zero] at hph
    rcases (rayleigh_stationary_iff τ ω₀ p.2.2 hτ hω₀).mp hph with hω | hω | hω
    · exfalso
      rw [hω] at hrad
      unfold coriolisRadialRHS at hrad
      norm_num at hrad
      rcases hrad with h | h
      · exact hk h
      · exact hr.ne' h
    · exact ⟨hv, Or.inl hω, (coriolisRadialRHS_eq_zero_iff p.1 p.2.2 Ω k hr).mp hrad⟩
    · exact ⟨hv, Or.inr hω, (coriolisRadialRHS_eq_zero_iff p.1 p.2.2 Ω k hr).mp hrad⟩
  · rintro ⟨hv, (hω | hω), hbal⟩
    · have hcz : coriolisRadialRHS p.1 p.2.2 Ω k = 0 :=
        (coriolisRadialRHS_eq_zero_iff p.1 p.2.2 Ω k hr).mpr hbal
      unfold rotatingSpinField rotationPhaseRHS
      rw [hcz, hω, hv, zero_div, mul_zero, zero_mul, sub_zero,
        rayleighDrift_self_eq_zero τ ω₀ hω₀]
      rfl
    · have hcz : coriolisRadialRHS p.1 p.2.2 Ω k = 0 :=
        (coriolisRadialRHS_eq_zero_iff p.1 p.2.2 Ω k hr).mpr hbal
      unfold rotatingSpinField rotationPhaseRHS
      rw [hcz, hω, hv, zero_div, mul_zero, zero_mul, sub_zero,
        rayleighDrift_neg_self_eq_zero τ ω₀ hω₀]
      rfl

/-- The co-rotating circular orbit: for a positive preferred frequency and
`Ω > -ω₀/2` (in particular every `Ω ≥ 0`), the state
`(radialEquilibrium ω₀ Ω k, 0, ω₀)` is an exact equilibrium of the coupled
rotating-frame system. -/
theorem corotating_circular_orbit (κ k τ ω₀ Ω : ℝ) (hk : 0 < k)
    (hω₀ : 0 < ω₀) (hΩ : -ω₀ / 2 < Ω) :
    rotatingSpinField κ k τ ω₀ Ω (radialEquilibrium ω₀ Ω k, 0, ω₀) = 0 := by
  have hβ : 0 < ω₀ * (ω₀ + 2 * Ω) := mul_pos hω₀ (by linarith)
  have hrad : coriolisRadialRHS (radialEquilibrium ω₀ Ω k) ω₀ Ω k = 0 :=
    coriolisRadialRHS_at_equilibrium ω₀ Ω k hk hβ
  show (0, coriolisRadialRHS _ _ _ _, rayleighDrift _ _ _ - _) = 0
  rw [show (0 : ℝ) / radialEquilibrium ω₀ Ω k = 0 from zero_div _,
    mul_zero, zero_mul, sub_zero, rayleighDrift_self_eq_zero τ ω₀ hω₀.ne', hrad]
  rfl

/-- The counter-rotating circular orbit exists (with positive radius) exactly
below the reduced threshold `Ω = ω₀/2`: for `Ω ≥ 0`, there is a positive
equilibrium radius for the counter-rotating walker if and only if
`Ω < ω₀/2`. At and above the threshold the radial balance has no positive
solution and the counter-rotating circular orbit ceases to exist (the
degenerate remnant is the well centre `r = 0`); this is an analytic
non-existence statement at reduced level, not a dynamical instability proof
(the observed destabilization into trefoil trajectories lies beyond the
circular-orbit regime of the model). -/
theorem counterrotating_orbit_iff (κ k τ ω₀ Ω : ℝ) (hk : 0 < k)
    (hω₀ : 0 < ω₀) :
    (∃ r : ℝ, 0 < r ∧ rotatingSpinField κ k τ ω₀ Ω (r, 0, -ω₀) = 0) ↔ Ω < ω₀ / 2 := by
  constructor
  · rintro ⟨r, hr, hz⟩
    unfold rotatingSpinField at hz
    have hrad : coriolisRadialRHS r (-ω₀) Ω k = 0 :=
      congrArg Prod.fst (congrArg Prod.snd hz)
    have hbal : 4 * k * r ^ 2 = (-ω₀) * (-ω₀ + 2 * Ω) :=
      (coriolisRadialRHS_eq_zero_iff r (-ω₀) Ω k hr).mp hrad
    have hpos : (0:ℝ) < 4 * k * r ^ 2 := by positivity
    rw [hbal] at hpos
    have h2 : (-ω₀:ℝ) + 2 * Ω < 0 := by
      by_contra hcon
      push Not at hcon
      have hprod : (0:ℝ) ≤ ω₀ * (-ω₀ + 2 * Ω) := mul_nonneg hω₀.le hcon
      have hring : (-ω₀) * (-ω₀ + 2 * Ω) = -(ω₀ * (-ω₀ + 2 * Ω)) := by ring
      linarith
    linarith
  · intro hΩlt
    have hβ : 0 < (-ω₀) * (-ω₀ + 2 * Ω) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    refine ⟨radialEquilibrium (-ω₀) Ω k, radialEquilibrium_pos (-ω₀) Ω k hk hβ, ?_⟩
    have hrad : coriolisRadialRHS (radialEquilibrium (-ω₀) Ω k) (-ω₀) Ω k = 0 :=
      coriolisRadialRHS_at_equilibrium (-ω₀) Ω k hk hβ
    unfold rotatingSpinField rotationPhaseRHS
    rw [zero_div, mul_zero, zero_mul, sub_zero,
      rayleighDrift_neg_self_eq_zero τ ω₀ hω₀.ne', hrad]
    rfl

/-- The equilibrium radius is strictly increasing in the bath rotation while
the sign factor stays positive (for `ω > 0`, whenever `-ω/2 < Ω₁ < Ω₂`): the
co-rotating branch expands as `Ω` grows, the analytic counterpart of
Fig. 3f,h of [Saenz2021HydroSpinLattices]. -/
theorem radialEquilibrium_strict_mono_in_Ω (ω Ω₁ Ω₂ k : ℝ) (hω : 0 < ω)
    (hk : 0 < k) (hΩ : Ω₁ < Ω₂) (hb₁ : -ω / 2 < Ω₁) :
    radialEquilibrium ω Ω₁ k < radialEquilibrium ω Ω₂ k := by
  have hb₂ : -ω / 2 < Ω₂ := lt_of_lt_of_le hb₁ (by linarith)
  have hpos₁ : 0 ≤ ω * (ω + 2 * Ω₁) / (4 * k) :=
    div_nonneg (mul_nonneg hω.le (by linarith)) (by positivity)
  refine Real.sqrt_lt_sqrt hpos₁ ?_
  have hlt : ω * (ω + 2 * Ω₁) < ω * (ω + 2 * Ω₂) :=
    mul_lt_mul_of_pos_left (by linarith) hω
  exact div_lt_div_of_pos_right hlt (by positivity)

/-- For positive bath rotation below the counter-rotating threshold, the
counter-rotating equilibrium radius is strictly smaller than the co-rotating
one at the same rotation: the two branches coincide only for `Ω = 0`. -/
theorem counterrotating_radius_lt_corotating (ω₀ Ω k : ℝ) (hω₀ : 0 < ω₀)
    (hk : 0 < k) (hΩ : 0 < Ω) (hΩlt : Ω < ω₀ / 2) :
    radialEquilibrium (-ω₀) Ω k < radialEquilibrium ω₀ Ω k := by
  have hpos : 0 ≤ (-ω₀) * (-ω₀ + 2 * Ω) / (4 * k) :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
      (by positivity)
  refine Real.sqrt_lt_sqrt hpos ?_
  have hlt : (-ω₀) * (-ω₀ + 2 * Ω) < ω₀ * (ω₀ + 2 * Ω) := by
    have hring : ω₀ * (ω₀ + 2 * Ω) - (-ω₀) * (-ω₀ + 2 * Ω) = 4 * ω₀ * Ω := by ring
    have hpos' : (0:ℝ) < 4 * ω₀ * Ω := by positivity
    linarith
  exact div_lt_div_of_pos_right hlt (by positivity)

/-- As the bath rotation approaches the counter-rotating threshold from
below, the counter-rotating equilibrium radius shrinks to zero: at `Ω = ω₀/2`
the would-be orbit collapses onto the well centre, the reduced-level
mechanism behind counter-rotating orbits passing ever closer to the centre in
Fig. 3g,h of [Saenz2021HydroSpinLattices]. -/
theorem counterrotating_radius_tendsto_zero (ω₀ k : ℝ)
    (hk : 0 < k) :
    Tendsto (fun Ω => radialEquilibrium (-ω₀) Ω k)
      (nhdsWithin (ω₀ / 2) (Set.Iio (ω₀ / 2))) (nhds 0) := by
  have hval : (-ω₀) * (-ω₀ + 2 * (ω₀ / 2)) / (4 * k) = 0 := by
    field_simp
    ring
  have hcont : Continuous (fun Ω : ℝ => (-ω₀) * (-ω₀ + 2 * Ω) / (4 * k)) := by
    continuity
  have hterm : Tendsto (fun Ω => (-ω₀) * (-ω₀ + 2 * Ω) / (4 * k))
      (nhdsWithin (ω₀ / 2) (Set.Iio (ω₀ / 2))) (nhds 0) := by
    rw [← hval]
    exact tendsto_nhdsWithin_of_tendsto_nhds hcont.continuousAt.tendsto
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x) (nhds 0) (nhds 0) := by
    have := (Real.continuous_sqrt).continuousAt.tendsto (x := (0:ℝ))
    simpa using this
  exact hsqrt.comp hterm

/-! ## The linearization at the circular orbit -/

/-- The Jacobian matrix of the coupled rotating-frame system at a point with
zero radial velocity, in the coordinates `(r, v, ω)`: its entries are the
exact one-variable derivatives of the field components, as proved by the
`*_hasDerivAt_*` theorems below. -/
def spinJacobian (κ k τ ω₀ Ω r ω : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![0, 1, 0],
    ![ω * ω + 2 * Ω * ω - 12 * k * r ^ 2, 0, 2 * r * (ω + Ω)],
    ![0, -κ * (Ω + ω) / r, (1 / τ) * (1 - 3 * ω ^ 2 / ω₀ ^ 2)]]

/-- The radial component of the field is differentiable in the radius, with
derivative `ω² + 2Ωω - 12kr²`: the `(2,1)` entry of `spinJacobian`. -/
theorem coriolisRadialRHS_hasDerivAt_r (r ω Ω k : ℝ) :
    HasDerivAt (fun x => coriolisRadialRHS x ω Ω k)
      (ω * ω + 2 * Ω * ω - 12 * k * r ^ 2) r := by
  have h1 : HasDerivAt (fun x : ℝ => ω * (ω + 2 * Ω) * x) (ω * (ω + 2 * Ω)) r := by
    simpa using (hasDerivAt_id r).const_mul (ω * (ω + 2 * Ω))
  have h2 : HasDerivAt (fun x : ℝ => 4 * k * x ^ 3) (4 * k * (3 * r ^ 2)) r := by
    simpa using (hasDerivAt_pow 3 r).const_mul (4 * k)
  exact (h1.sub h2).congr_of_eventuallyEq
    (Eventually.of_forall fun y => by
      simp only [coriolisRadialRHS, Pi.sub_apply]
      ring) |>.congr_deriv (by ring)

/-- The radial component of the field is differentiable in the angular
velocity, with derivative `2r(ω + Ω)`: the `(2,3)` entry of `spinJacobian`. -/
theorem coriolisRadialRHS_hasDerivAt_ω (r ω Ω k : ℝ) :
    HasDerivAt (fun x => coriolisRadialRHS r x Ω k) (2 * r * (ω + Ω)) ω := by
  have h1 : HasDerivAt (fun x : ℝ => r * x ^ 2) (r * (2 * ω)) ω := by
    simpa using (hasDerivAt_pow 2 ω).const_mul r
  have h2 : HasDerivAt (fun x : ℝ => 2 * Ω * r * x) (2 * Ω * r) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * Ω * r)
  have h3 : HasDerivAt (fun x : ℝ => 4 * k * r ^ 3) 0 ω := by
    simpa using hasDerivAt_const ω (4 * k * r ^ 3)
  exact ((h1.add h2).sub h3).congr_of_eventuallyEq
    (Eventually.of_forall fun y => by
      simp only [coriolisRadialRHS, Pi.add_apply, Pi.sub_apply]
      ring) |>.congr_deriv (by ring)

/-- The phase component of the field is differentiable in the radial
velocity, with derivative `-κ(Ω + ω)/r`: the `(3,2)` entry of `spinJacobian`. -/
theorem rotationPhaseRHS_hasDerivAt_v (κ τ ω₀ Ω r v ω : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x => rotationPhaseRHS κ τ ω₀ Ω r x ω)
      (-κ * (Ω + ω) / r) v := by
  have h1 : HasDerivAt (fun x : ℝ => κ * (Ω + ω) * (x / r))
      (κ * (Ω + ω) * (1 / r)) v := by
    simpa using ((hasDerivAt_id v).div_const r).const_mul (κ * (Ω + ω))
  exact (hasDerivAt_const v (rayleighDrift τ ω₀ ω)).sub h1 |>.congr_of_eventuallyEq
    (Eventually.of_forall fun y => by
      simp only [rotationPhaseRHS, Pi.sub_apply]
      ring) |>.congr_deriv (by field_simp [hr]; ring)

/-- The phase component of the field, evaluated at zero radial velocity, is
differentiable in the angular velocity with derivative
`(1/τ)(1 - 3ω²/ω₀²)`: the `(3,3)` entry of `spinJacobian` (the rotation
coupling contributes `-κ(v/r)`, which vanishes at `v = 0`). -/
theorem rotationPhaseRHS_hasDerivAt_ω (κ τ ω₀ Ω r ω : ℝ)
    (hω₀ : ω₀ ≠ 0) :
    HasDerivAt (fun x => rotationPhaseRHS κ τ ω₀ Ω r 0 x)
      ((1 / τ) * (1 - 3 * ω ^ 2 / ω₀ ^ 2)) ω := by
  have hq : HasDerivAt (fun x : ℝ => x ^ 2 / ω₀ ^ 2) (2 * ω / ω₀ ^ 2) ω := by
    simpa using (hasDerivAt_pow 2 ω).div_const (ω₀ ^ 2)
  have hd : HasDerivAt (fun x : ℝ => 1 - x ^ 2 / ω₀ ^ 2) (-(2 * ω / ω₀ ^ 2)) ω :=
    (hasDerivAt_const ω (1:ℝ)).sub hq |>.congr_of_eventuallyEq
      (Eventually.of_forall fun y => by
        simp only [Pi.sub_apply]) |>.congr_deriv (by ring)
  have hfin := (hasDerivAt_const ω (1 / τ)).mul (hd.mul (hasDerivAt_id ω))
  exact hfin.congr_of_eventuallyEq
    (Eventually.of_forall fun y => by
      simp only [rotationPhaseRHS, rayleighDrift, zero_div, mul_zero,
        Pi.mul_apply, id_eq]
      ring) |>.congr_deriv (by
        simp only [id_eq, zero_mul]
        field_simp [hω₀]
        ring)

/-- At a circular orbit the Jacobian simplifies: the radial-diagonal entry
becomes `-2ω(ω + 2Ω)` (using `4kr*² = ω(ω + 2Ω)`) and the phase-diagonal
entry becomes `-2/τ` (using `ω*² = ω₀²`). -/
theorem spinJacobian_at_orbit (κ k τ ω₀ Ω ω : ℝ) (hτ : τ ≠ 0) (hω₀ : ω₀ ≠ 0)
    (hωs : ω = ω₀ ∨ ω = -ω₀) (hβ : 0 < ω * (ω + 2 * Ω)) (hk : 0 < k) :
    spinJacobian κ k τ ω₀ Ω (radialEquilibrium ω Ω k) ω
      = !![0, 1, 0;
         -(2 * (ω * (ω + 2 * Ω))), 0, 2 * radialEquilibrium ω Ω k * (ω + Ω);
         0, -κ * (Ω + ω) / radialEquilibrium ω Ω k, -2 / τ] := by
  have hpos : 0 < radialEquilibrium ω Ω k := radialEquilibrium_pos ω Ω k hk hβ
  have h4 : 4 * k * radialEquilibrium ω Ω k ^ 2 = ω * (ω + 2 * Ω) :=
    (coriolisRadialRHS_eq_zero_iff (radialEquilibrium ω Ω k) ω Ω k hpos).mp
      (coriolisRadialRHS_at_equilibrium ω Ω k hk hβ)
  have hW : ω * ω + 2 * Ω * ω - 12 * k * radialEquilibrium ω Ω k ^ 2
      = -(2 * (ω * (ω + 2 * Ω))) := by
    rw [show 12 * k * radialEquilibrium ω Ω k ^ 2
        = 3 * (4 * k * radialEquilibrium ω Ω k ^ 2) from by ring, h4]
    field_simp
    ring
  have hsq : ω ^ 2 = ω₀ ^ 2 := by
    rcases hωs with h | h
    · rw [h]
    · rw [h, neg_sq]
  have hE : (1 / τ) * (1 - 3 * ω ^ 2 / ω₀ ^ 2) = -2 / τ := by
    rw [hsq]
    field_simp [hω₀]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinJacobian, hW]
  rw [hsq]
  field_simp [hω₀]
  ring

/-- The linearization at a circular orbit is non-degenerate: its determinant
equals `-4ω(ω + 2Ω)/τ`, nonzero exactly when the sign factor and the
relaxation time are nonzero. Together with the `*_hasDerivAt_*` theorems this
makes `spinJacobian` the non-degenerate linearization of the coupled system
at the orbit. -/
theorem spinJacobian_det_eq (κ k τ ω₀ Ω ω : ℝ) (hτ : τ ≠ 0) (hω₀ : ω₀ ≠ 0)
    (hωs : ω = ω₀ ∨ ω = -ω₀) (hβ : 0 < ω * (ω + 2 * Ω)) (hk : 0 < k) :
    (spinJacobian κ k τ ω₀ Ω (radialEquilibrium ω Ω k) ω).det
      = -(4 / τ) * (ω * (ω + 2 * Ω)) := by
  rw [spinJacobian_at_orbit κ k τ ω₀ Ω ω hτ hω₀ hωs hβ hk]
  eval_det
  field_simp [hτ]
  ring

/-- Non-degeneracy of the linearization at every existing circular orbit. -/
theorem spinJacobian_det_ne_zero (κ k τ ω₀ Ω ω : ℝ) (hτ : τ ≠ 0) (hω₀ : ω₀ ≠ 0)
    (hωs : ω = ω₀ ∨ ω = -ω₀) (hβ : 0 < ω * (ω + 2 * Ω)) (hk : 0 < k) :
    (spinJacobian κ k τ ω₀ Ω (radialEquilibrium ω Ω k) ω).det ≠ 0 := by
  rw [spinJacobian_det_eq κ k τ ω₀ Ω ω hτ hω₀ hωs hβ hk]
  intro hcon
  have hz : (4 / τ) * (ω * (ω + 2 * Ω)) = 0 := by
    have hn : -((4 / τ) * (ω * (ω + 2 * Ω))) = 0 := by linarith
    linarith
  rcases mul_eq_zero.mp hz with h | h
  · field_simp at h
    norm_num at h
  · exact absurd h hβ.ne'


/-! ## The characteristic polynomial and the Routh-Hurwitz criterion -/

/-- The complex determinant identity used to evaluate the characteristic
polynomial at complex points: for the real matrix
`[[0, 1, 0], [-A, 0, B], [0, -D, -c]]`, the determinant of `z` times the
identity minus the complexified matrix expands to the monic cubic
`z³ + cz² + (A + BD)z + cA`. -/
theorem det_scalar_sub_complex (z : ℂ) (A B D c : ℝ) :
    (Matrix.scalar (Fin 3) z
        - Matrix.map (!![0, 1, 0; -A, 0, B; 0, -D, -c]) Complex.ofRealHom).det
      = z ^ 3 + (c : ℂ) * z ^ 2 + ((A : ℂ) + (B : ℂ) * (D : ℂ)) * z
          + (c : ℂ) * (A : ℂ) := by
  have h : (Matrix.scalar (Fin 3) z
      - Matrix.map (Matrix.of ![![0, 1, 0], ![-A, 0, B], ![0, -D, -c]])
        Complex.ofRealHom)
      = !![z, -1, 0; (A : ℂ), z, -(B : ℂ); 0, (D : ℂ), z + (c : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, Matrix.map_apply, Complex.ofRealHom]
  rw [h]
  eval_det
  ring

/-- At a circular orbit the sign factor forces `ω + Ω ≠ 0`: the alternative
`ω = -Ω` would make the sign factor `-Ω² ≤ 0`. -/
theorem orbit_offset_ne_zero (ω Ω : ℝ) (hβ : 0 < ω * (ω + 2 * Ω)) : ω + Ω ≠ 0 := by
  intro h
  have hω : ω = -Ω := by linarith
  rw [hω] at hβ
  have hval : (-Ω : ℝ) * (-Ω + 2 * Ω) = -(Ω ^ 2) := by ring
  rw [hval] at hβ
  nlinarith [sq_nonneg Ω]

/-- Self-contained cubic Routh-Hurwitz criterion: a monic real cubic
`λ³ + a₁λ² + a₂λ + a₃` whose coefficients satisfy the Routh-Hurwitz
conditions `0 < a₁`, `0 < a₃` and `a₃ < a₁ a₂` has every complex root in
the open left half-plane. The proof extracts the real and imaginary parts of
the root equation directly; no external stability machinery is used. -/
theorem cubic_re_neg_of_routh_hurwitz (a₁ a₂ a₃ : ℝ) (z : ℂ)
    (h1 : 0 < a₁) (h3 : 0 < a₃) (hrw : a₃ < a₁ * a₂)
    (hz : z ^ 3 + a₁ * z ^ 2 + a₂ * z + a₃ = 0) : z.re < 0 := by
  have h2 : 0 < a₂ := by
    by_contra hcon
    push Not at hcon
    have hp : (0:ℝ) ≤ a₁ * (-a₂) := mul_nonneg h1.le (neg_nonneg.2 hcon)
    have hr : a₁ * (-a₂) = -(a₁ * a₂) := by ring
    linarith
  have hzexp : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
  have hz2 : (z.re + z.im * Complex.I) ^ 2
      = (z.re * z.re - z.im * z.im) + (2 * z.re * z.im) * Complex.I := by
    refine Complex.ext ?_ ?_
    all_goals simp [pow_two, Complex.mul_re, Complex.mul_im]
    all_goals ring
  have hz3 : (z.re + z.im * Complex.I) ^ 3
      = (z.re * z.re * z.re - 3 * z.re * z.im * z.im)
          + (3 * z.re * z.re * z.im - z.im * z.im * z.im) * Complex.I := by
    refine Complex.ext ?_ ?_ <;>
      simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring
  rw [hzexp, hz2, hz3] at hz
  have hR1 : z.re * z.re * z.re - 3 * z.re * z.im * z.im
      + a₁ * (z.re * z.re - z.im * z.im) + a₂ * z.re + a₃ = 0 := by
    have h := congrArg Complex.re hz
    simpa using h
  have hR2' : 3 * z.re * z.re * z.im - z.im * z.im * z.im
      + a₁ * (2 * z.re * z.im) + a₂ * z.im = 0 := by
    have h := congrArg Complex.im hz
    simpa using h
  have hR2 : z.im * (3 * z.re * z.re - z.im * z.im + 2 * a₁ * z.re + a₂) = 0 := by
    linear_combination hR2'
  rcases eq_or_ne z.im 0 with hy0 | hy0
  · rw [hy0] at hR1
    simp only [mul_zero, sub_zero] at hR1
    by_contra hx0
    push Not at hx0
    have hx2 : (0:ℝ) ≤ z.re * z.re := by nlinarith [sq_nonneg z.re]
    have hx3 : (0:ℝ) ≤ z.re * z.re * z.re := mul_nonneg hx2 hx0
    have ha1 : (0:ℝ) ≤ a₁ * (z.re * z.re) := mul_nonneg h1.le hx2
    have ha2 : (0:ℝ) ≤ a₂ * z.re := mul_nonneg h2.le hx0
    nlinarith
  · have hsub : z.im * z.im - 3 * z.re * z.re - 2 * a₁ * z.re - a₂ = 0 := by
      rcases mul_eq_zero.mp hR2 with h | h
      · exact absurd h hy0
      · nlinarith
    by_contra hx0
    push Not at hx0
    have hkey : 8 * z.re ^ 3 + 8 * a₁ * z.re ^ 2 + 2 * a₂ * z.re
        + 2 * a₁ ^ 2 * z.re + a₁ * a₂ - a₃ = 0 := by
      linear_combination -hR1 - (3 * z.re + a₁) * hsub
    have hx3 : (0:ℝ) ≤ z.re ^ 3 := pow_nonneg hx0 3
    have hx2 : (0:ℝ) ≤ z.re ^ 2 := pow_nonneg hx0 2
    have ha1 : (0:ℝ) ≤ 8 * a₁ * z.re ^ 2 :=
      by nlinarith [mul_nonneg h1.le hx2]
    have ha2 : (0:ℝ) ≤ 2 * a₂ * z.re := by nlinarith [mul_nonneg h2.le hx0]
    have ha3 : (0:ℝ) ≤ 2 * a₁ ^ 2 * z.re :=
      by nlinarith [mul_nonneg (pow_nonneg h1.le 2) hx0]
    nlinarith


/-- The characteristic polynomial of the linearization at a circular orbit is
the explicit monic cubic `λ³ + (2/τ)λ² + (2κ(ω+Ω)² + 2ω(ω+2Ω))λ +
(4/τ)ω(ω+2Ω)`: the off-diagonal Coriolis coupling `2r*(ω+Ω)` times the
phase-velocity coupling `κ(Ω+ω)/r*` collapses to `2κ(ω+Ω)²`, so the
polynomial does not depend on the equilibrium radius. -/
theorem charpoly_spinJacobian_at_orbit (κ k τ ω₀ Ω ω : ℝ) (hτ : τ ≠ 0)
    (hω₀ : ω₀ ≠ 0) (hωs : ω = ω₀ ∨ ω = -ω₀) (hβ : 0 < ω * (ω + 2 * Ω))
    (hk : 0 < k) :
    (spinJacobian κ k τ ω₀ Ω (radialEquilibrium ω Ω k) ω).charpoly
      = X ^ 3 + C (2 / τ) * X ^ 2
          + C (2 * κ * (ω + Ω) ^ 2 + 2 * ω * (ω + 2 * Ω)) * X
          + C ((4 / τ) * (ω * (ω + 2 * Ω))) := by
  have hpos : 0 < radialEquilibrium ω Ω k := radialEquilibrium_pos ω Ω k hk hβ
  apply Polynomial.funext
  intro t
  have hcp := Matrix.eval_charpoly
    (spinJacobian κ k τ ω₀ Ω (radialEquilibrium ω Ω k) ω) t
  have hmat := spinJacobian_at_orbit κ k τ ω₀ Ω ω hτ hω₀ hωs hβ hk
  have hdet : (Matrix.scalar (Fin 3) t - !![0, 1, 0;
        -(2 * (ω * (ω + 2 * Ω))), 0, 2 * radialEquilibrium ω Ω k * (ω + Ω);
        0, -κ * (Ω + ω) / radialEquilibrium ω Ω k, -2 / τ])
      = !![t, -1, 0; 2 * (ω * (ω + 2 * Ω)), t,
        -(2 * radialEquilibrium ω Ω k * (ω + Ω));
        0, κ * (Ω + ω) / radialEquilibrium ω Ω k, t + 2 / τ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    all_goals ring_nf
  have hkey : ∀ x : ℝ, x * (κ * (Ω + ω) / radialEquilibrium ω Ω k)
      * radialEquilibrium ω Ω k = x * κ * (Ω + ω) := fun x => by
    field_simp [hpos.ne']
  rw [hcp, hmat, hdet]
  eval_det
  rw [hkey]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp [hτ]
  ring

set_option maxHeartbeats 800000 in
/-- Linear stability criterion (Routh-Hurwitz): at every circular orbit of
the reduced rotating-frame system, all characteristic roots of the
linearization lie in the open left half-plane. The Routh-Hurwitz determinant
collapses to `a₁a₂ - a₃ = (4κ/τ)(ω+Ω)² > 0`, which is positive for every
coupling coefficient `κ > 0` whenever the orbit exists. Both rotation
senses are spectrally stable in the fixed-`ω₀` model. The counter-rotating
branch of this model exists below the threshold `Ω = ω₀/2` by
`counterrotating_orbit_iff`. -/
theorem charpoly_roots_re_neg (κ k τ ω₀ Ω ω : ℝ) (hκ : 0 < κ) (hk : 0 < k)
    (hτ : 0 < τ) (hω₀ : ω₀ ≠ 0) (hωs : ω = ω₀ ∨ ω = -ω₀)
    (hβ : 0 < ω * (ω + 2 * Ω)) :
    ∀ z : ℂ, ((spinJacobian κ k τ ω₀ Ω (radialEquilibrium ω Ω k) ω).charpoly.map
      Complex.ofRealHom).eval z = 0 → z.re < 0 := by
  have hoff : ω + Ω ≠ 0 := orbit_offset_ne_zero ω Ω hβ
  intro z hzroot
  rw [charpoly_spinJacobian_at_orbit κ k τ ω₀ Ω ω hτ.ne' hω₀ hωs hβ hk,
    ← Polynomial.eval₂_eq_eval_map] at hzroot
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X] at hzroot
  exact cubic_re_neg_of_routh_hurwitz (2 / τ)
    (2 * κ * (ω + Ω) ^ 2 + 2 * ω * (ω + 2 * Ω))
    ((4 / τ) * (ω * (ω + 2 * Ω))) z
    (div_pos two_pos hτ) (mul_pos (div_pos four_pos hτ) hβ) (by
      have hsq : (0:ℝ) < (ω + Ω) ^ 2 := sq_pos_of_ne_zero hoff
      have h4τ : (0:ℝ) < 4 / τ := div_pos four_pos hτ
      have hkey : (2:ℝ) / τ * (2 * κ * (ω + Ω) ^ 2 + 2 * ω * (ω + 2 * Ω))
          - (4 / τ) * (ω * (ω + 2 * Ω)) = (4 / τ) * κ * (ω + Ω) ^ 2 := by
        field_simp
        ring
      rw [← sub_pos, hkey]
      exact mul_pos (mul_pos h4τ hκ) hsq) hzroot

/-! ## The Lyapunov energy of the linearized flow -/

/-- The quadratic Lyapunov form of the linearized rotating-frame flow at the
circular orbit: the radial weight `2ω(ω+2Ω)` is the restoring coefficient of
the linearized radial balance and the frequency weight `2r*²/κ` is exactly
the ratio of the Coriolis and rotation-coupling entries of `spinJacobian`,
which forces the cancellation of the indefinite cross terms in the energy
balance. -/
def orbitLyapunov (κ k Ω ω : ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun p => 2 * ω * (ω + 2 * Ω) * p.1 ^ 2 + p.2.1 ^ 2
    + (2 * radialEquilibrium ω Ω k ^ 2 / κ) * p.2.2 ^ 2

/-- The Lyapunov form is nonnegative, and positive away from the origin,
whenever the orbit exists and `κ > 0`. -/
theorem orbitLyapunov_nonneg (κ k Ω ω : ℝ) (hκ : 0 < κ)
    (hβ : 0 < ω * (ω + 2 * Ω)) (p : ℝ × ℝ × ℝ) :
    0 ≤ orbitLyapunov κ k Ω ω p := by
  have hA : (0:ℝ) ≤ 2 * ω * (ω + 2 * Ω) := by nlinarith [hβ]
  have hB : (0:ℝ) ≤ 2 * radialEquilibrium ω Ω k ^ 2 / κ :=
    div_nonneg (by positivity) hκ.le
  unfold orbitLyapunov
  nlinarith [mul_nonneg hA (sq_nonneg p.1), mul_nonneg hB (sq_nonneg p.2.2)]

/-- Exact dissipation identity of the linearized flow: along any solution of
the linearized system at the circular orbit, the Lyapunov form has derivative
`-(8r*²/(κτ)) σ² ≤ 0`, with the Coriolis/rotation cross terms cancelling
exactly. The three component derivatives required here are the rows of
`spinJacobian` evaluated at the orbit (see `spinJacobian_at_orbit`). -/
theorem hasDerivAt_orbitLyapunov (κ k τ Ω ω : ℝ) (hκ : 0 < κ) (hk : 0 < k)
    (hτ : 0 < τ) (hβ : 0 < ω * (ω + 2 * Ω)) (ξ u σ : ℝ → ℝ) (t : ℝ)
    (hξ : HasDerivAt ξ (u t) t)
    (hu : HasDerivAt u (-(2 * ω * (ω + 2 * Ω)) * ξ t
      + 2 * radialEquilibrium ω Ω k * (ω + Ω) * σ t) t)
    (hσ : HasDerivAt σ (-(κ * (Ω + ω) / radialEquilibrium ω Ω k) * u t
      - 2 / τ * σ t) t) :
    HasDerivAt (fun s => orbitLyapunov κ k Ω ω (ξ s, u s, σ s))
      (-(8 * radialEquilibrium ω Ω k ^ 2 / (κ * τ)) * σ t ^ 2) t := by
  have hpos : 0 < radialEquilibrium ω Ω k := radialEquilibrium_pos ω Ω k hk hβ
  have h1 := (hasDerivAt_const t (2 * ω * (ω + 2 * Ω))).mul (hξ.pow 2)
  have h2 := hu.pow 2
  have h3 := (hasDerivAt_const t (2 * radialEquilibrium ω Ω k ^ 2 / κ)).mul
    (hσ.pow 2)
  exact (h1.add (h2.add h3)).congr_of_eventuallyEq
    (Eventually.of_forall fun s => by
      simp only [orbitLyapunov, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
      ring) |>.congr_deriv (by
    field_simp [hκ.ne', hτ.ne', hpos.ne']
    ring)

/-- The Lyapunov energy is non-increasing along solutions of the linearized
system on compact time intervals: linear stability in the sense of Lyapunov
for the reduced linearized flow. -/
theorem orbitLyapunov_nonincreasing (κ k τ Ω ω : ℝ) (hκ : 0 < κ) (hk : 0 < k)
    (hτ : 0 < τ) (hβ : 0 < ω * (ω + 2 * Ω)) (ξ u σ : ℝ → ℝ) (t₀ t₁ : ℝ)
    (hle : t₀ ≤ t₁)
    (hsol : ∀ s ∈ Icc t₀ t₁, HasDerivAt ξ (u s) s ∧
      HasDerivAt u (-(2 * ω * (ω + 2 * Ω)) * ξ s
        + 2 * radialEquilibrium ω Ω k * (ω + Ω) * σ s) s ∧
      HasDerivAt σ (-(κ * (Ω + ω) / radialEquilibrium ω Ω k) * u s
        - 2 / τ * σ s) s) :
    orbitLyapunov κ k Ω ω (ξ t₁, u t₁, σ t₁)
      ≤ orbitLyapunov κ k Ω ω (ξ t₀, u t₀, σ t₀) := by
  rcases eq_or_ne t₀ t₁ with h | h
  · rw [h]
  · have hlt : t₀ < t₁ := lt_of_le_of_ne hle h
    have hder : ∀ s ∈ Ioo t₀ t₁, HasDerivAt
        (fun s => orbitLyapunov κ k Ω ω (ξ s, u s, σ s))
        (-(8 * radialEquilibrium ω Ω k ^ 2 / (κ * τ)) * σ s ^ 2) s := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hsol s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact hasDerivAt_orbitLyapunov κ k τ Ω ω hκ hk hτ hβ ξ u σ s h1 h2 h3
    have hcont : ContinuousOn
        (fun s => orbitLyapunov κ k Ω ω (ξ s, u s, σ s)) (Icc t₀ t₁) := by
      intro s hs
      obtain ⟨h1, h2, h3⟩ := hsol s hs
      have hCA : ContinuousAt
          (fun s => 2 * ω * (ω + 2 * Ω) * ξ s ^ 2 + u s ^ 2
            + (2 * radialEquilibrium ω Ω k ^ 2 / κ) * σ s ^ 2) s :=
        ((((hasDerivAt_const s (2 * ω * (ω + 2 * Ω))).continuousAt.mul
          (h1.continuousAt.pow 2)).add (h2.continuousAt.pow 2)).add
          ((hasDerivAt_const s (2 * radialEquilibrium ω Ω k ^ 2 / κ)).continuousAt.mul
            (h3.continuousAt.pow 2)))
      exact (hCA.congr (Eventually.of_forall fun y => by
        simp only [orbitLyapunov])).continuousWithinAt
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope
      (fun s => orbitLyapunov κ k Ω ω (ξ s, u s, σ s))
      (fun s => -(8 * radialEquilibrium ω Ω k ^ 2 / (κ * τ)) * σ s ^ 2)
      hlt hcont hder
    have hle0 : -(8 * radialEquilibrium ω Ω k ^ 2 / (κ * τ)) * σ c ^ 2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · have hfrac : (0:ℝ) ≤ 8 * radialEquilibrium ω Ω k ^ 2 / (κ * τ) :=
          div_nonneg (by positivity) (mul_pos hκ hτ).le
        exact neg_nonpos.2 hfrac
      · exact sq_nonneg _
    have hsplit : orbitLyapunov κ k Ω ω (ξ t₁, u t₁, σ t₁)
        - orbitLyapunov κ k Ω ω (ξ t₀, u t₀, σ t₀)
        = (-(8 * radialEquilibrium ω Ω k ^ 2 / (κ * τ)) * σ c ^ 2) * (t₁ - t₀) := by
      rw [hc, div_mul_cancel₀ _ (sub_ne_zero_of_ne (Ne.symm h))]
    linarith [hsplit, mul_nonpos_of_nonpos_of_nonneg hle0 (sub_nonneg.2 hle)]

end Qatlib.Papers.HydroSpinLatt21.Rotation

end
