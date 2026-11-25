/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Rotating-frame radial balance and its equilibrium structure

[Saenz2021HydroSpinLattices], Methods equations (29)-(32), extends the spin
model to a bath rotating at angular velocity `Ω`: in the rotating frame each
droplet obeys equation (29) with a Coriolis term `-2Ω × ẋ`, the position is
written in polar coordinates (30), and after the simplifications stated in
the article (neglecting the radial velocity in the Rayleigh drag, the
Rayleigh drag in the radial balance and the wave force in the radial
balance, and holding `α`, `β` fixed), the radial balance reduces to
equation (31): `r̈ = r ω² + 2Ωω r - 4k r³`, where `-4kr³` is the radial
component of the confining force `F_w = -4k|x|²x` of equation (29). See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

This file analyses the exact mathematical content of the reduced radial
equation (31): the sign factor `ω(ω + 2Ω)` governs the existence of a
positive equilibrium, which is then unique and equal to
`radialEquilibrium ω Ω k = √(ω(ω+2Ω)/(4k))`; for a counter-rotating walker
(`ω < 0`, `Ω ≥ 0`) an equilibrium exists exactly when `|ω| > 2Ω`; for a
co-rotating walker (`ω > 0`) the equilibrium radius increases with `Ω`; and
the radial force is minus the gradient of the potential
`V(r) = kr⁴ - ω(ω+2Ω)r²/2`, whose deviation from its equilibrium value
factorizes as `V(r) - V(r*) = k(r² - r*²)²`, so the equilibrium is the
unique global minimum. The reduction from equation (29) itself, the full
dynamics, and the comparison with experiment (Fig. 3e, Ω_c ≈ 0.22 rad s⁻¹)
are not formalized here.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.Rotation

/-! ## The reduced radial equation (31) -/

/-- The right-hand side of the reduced rotating-frame radial balance,
equation (31): `r̈ = r ω² + 2Ωω r - 4k r³`, with inertial, Coriolis and
confinement contributions. -/
def coriolisRadialRHS (r ω Ω k : ℝ) : ℝ := r * ω * ω + 2 * Ω * ω * r - 4 * k * r ^ 3

/-- The positive equilibrium radius of equation (31), `√(ω(ω+2Ω)/(4k))`,
defined whenever the sign factor `ω(ω+2Ω)` and `k` are positive. -/
def radialEquilibrium (ω Ω k : ℝ) : ℝ :=
  Real.sqrt (ω * (ω + 2 * Ω) / (4 * k))

/-- The radial potential of equation (31), `V(r) = k r⁴ - ω(ω+2Ω) r²/2`,
whose negative gradient is the right-hand side of (31). -/
def radialPotential (ω Ω k : ℝ) : ℝ → ℝ :=
  fun x => k * x ^ (4:ℕ) - ω * (ω + 2 * Ω) / 2 * x ^ (2:ℕ)

/-- Factorized form of the right-hand side of (31): the radial acceleration
is `r (ω(ω+2Ω) - 4kr²)`, so its sign is governed by the sign factor
`ω(ω+2Ω)`. -/
theorem coriolisRadialRHS_eq (r ω Ω k : ℝ) :
    coriolisRadialRHS r ω Ω k = r * (ω * (ω + 2 * Ω) - 4 * k * r ^ 2) := by
  unfold coriolisRadialRHS
  ring

/-- A positive radius is an equilibrium of (31) exactly when `4kr²` equals
the sign factor `ω(ω+2Ω)`. -/
theorem coriolisRadialRHS_eq_zero_iff (r ω Ω k : ℝ) (hr : 0 < r) :
    coriolisRadialRHS r ω Ω k = 0 ↔ 4 * k * r ^ 2 = ω * (ω + 2 * Ω) := by
  rw [coriolisRadialRHS_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hr.ne'
    · linarith
  · intro h
    exact Or.inr (by linarith)

/-! ## Existence and uniqueness of the positive equilibrium -/

/-- When the sign factor is positive and `k > 0`, the equilibrium radius of
(31) is positive. -/
theorem radialEquilibrium_pos (ω Ω k : ℝ) (hk : 0 < k) (hβ : 0 < ω * (ω + 2 * Ω)) :
    0 < radialEquilibrium ω Ω k :=
  Real.sqrt_pos.mpr (div_pos hβ (mul_pos four_pos hk))

/-- When the sign factor is positive and `k > 0`, `radialEquilibrium` is an
equilibrium of equation (31). -/
theorem coriolisRadialRHS_at_equilibrium (ω Ω k : ℝ) (hk : 0 < k)
    (hβ : 0 < ω * (ω + 2 * Ω)) :
    coriolisRadialRHS (radialEquilibrium ω Ω k) ω Ω k = 0 := by
  rw [coriolisRadialRHS_eq_zero_iff (radialEquilibrium ω Ω k) ω Ω k
    (radialEquilibrium_pos ω Ω k hk hβ)]
  show 4 * k * (Real.sqrt (ω * (ω + 2 * Ω) / (4 * k))) ^ 2 = ω * (ω + 2 * Ω)
  rw [Real.sq_sqrt (div_nonneg hβ.le (mul_nonneg four_pos.le hk.le))]
  field_simp [hk.ne']

/-- Uniqueness of the positive equilibrium: any positive equilibrium radius
of equation (31) equals `radialEquilibrium ω Ω k`. -/
theorem positive_equilibrium_eq (ω Ω k r : ℝ) (hk : 0 < k) (hr : 0 < r)
    (hβ : 0 < ω * (ω + 2 * Ω))
    (heq : coriolisRadialRHS r ω Ω k = 0) :
    r = radialEquilibrium ω Ω k := by
  have h4k : (4:ℝ) * k ≠ 0 := mul_ne_zero four_ne_zero hk.ne'
  have h4 : 4 * k * r ^ 2 = ω * (ω + 2 * Ω) :=
    (coriolisRadialRHS_eq_zero_iff r ω Ω k hr).mp heq
  have hb : ω * (ω + 2 * Ω) = 4 * k * radialEquilibrium ω Ω k ^ 2 := by
    have hs : radialEquilibrium ω Ω k ^ 2 = ω * (ω + 2 * Ω) / (4 * k) :=
      Real.sq_sqrt (div_nonneg hβ.le (mul_nonneg four_pos.le hk.le))
    rw [hs]
    field_simp [hk.ne']
  have hs2 : r ^ 2 = radialEquilibrium ω Ω k ^ 2 :=
    mul_left_cancel₀ h4k (by rw [← hb]; exact h4)
  have habs : |r| = |radialEquilibrium ω Ω k| :=
    (sq_eq_sq_iff_abs_eq_abs r (radialEquilibrium ω Ω k)).mp hs2
  rcases abs_eq_abs.mp habs with h | h
  · exact h
  · exact absurd h (by linarith [hr, radialEquilibrium_pos ω Ω k hk hβ])

/-- If the sign factor `ω(ω+2Ω)` is non-positive, equation (31) has no
positive equilibrium. -/
theorem coriolisRadialRHS_ne_zero_of_nonpos (ω Ω k r : ℝ) (hk : 0 < k) (hr : 0 < r)
    (hβ : ω * (ω + 2 * Ω) ≤ 0) : coriolisRadialRHS r ω Ω k ≠ 0 := by
  intro heq
  have h4 : 4 * k * r ^ 2 = ω * (ω + 2 * Ω) :=
    (coriolisRadialRHS_eq_zero_iff r ω Ω k hr).mp heq
  have hpos : (0:ℝ) < 4 * k * r ^ 2 := mul_pos (mul_pos four_pos hk) (pow_pos hr 2)
  linarith

/-- Counter-rotating threshold: for a counter-rotating walker (`ω < 0`) in
a bath rotating at `Ω ≥ 0`, equation (31) has a positive equilibrium
exactly when `|ω| > 2Ω`, i.e. when the counter-rotation dominates the bath
rotation; otherwise no positive equilibrium radius exists. -/
theorem counter_rotating_equilibrium_iff (ω Ω k : ℝ) (hω : ω < 0) (hk : 0 < k) :
    (∃ r : ℝ, 0 < r ∧ coriolisRadialRHS r ω Ω k = 0) ↔ ω < -2 * Ω := by
  constructor
  · rintro ⟨r, hr, heq⟩
    have h4 : 4 * k * r ^ 2 = ω * (ω + 2 * Ω) :=
      (coriolisRadialRHS_eq_zero_iff r ω Ω k hr).mp heq
    have hpos : (0:ℝ) < 4 * k * r ^ 2 := mul_pos (mul_pos four_pos hk) (pow_pos hr 2)
    have hβ : 0 < ω * (ω + 2 * Ω) := by linarith
    rcases mul_pos_iff.mp hβ with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact absurd h1 (by linarith)
    · linarith
  · intro h
    have h2 : ω + 2 * Ω < 0 := by linarith
    have hβ : 0 < ω * (ω + 2 * Ω) := mul_pos_of_neg_of_neg hω h2
    exact ⟨radialEquilibrium ω Ω k, radialEquilibrium_pos ω Ω k hk hβ,
      coriolisRadialRHS_at_equilibrium ω Ω k hk hβ⟩

/-- Co-rotating threshold: for a co-rotating walker (`ω > 0`), equation
(31) has a positive equilibrium exactly when `Ω > -ω/2`. -/
theorem co_rotating_equilibrium_iff (ω Ω k : ℝ) (hω : 0 < ω) (hk : 0 < k) :
    (∃ r : ℝ, 0 < r ∧ coriolisRadialRHS r ω Ω k = 0) ↔ -ω / 2 < Ω := by
  constructor
  · rintro ⟨r, hr, heq⟩
    have h4 : 4 * k * r ^ 2 = ω * (ω + 2 * Ω) :=
      (coriolisRadialRHS_eq_zero_iff r ω Ω k hr).mp heq
    have hpos : (0:ℝ) < 4 * k * r ^ 2 := mul_pos (mul_pos four_pos hk) (pow_pos hr 2)
    have hβ : 0 < ω * (ω + 2 * Ω) := by linarith
    rcases mul_pos_iff.mp hβ with ⟨h1, h2⟩ | ⟨h1, _⟩
    · linarith
    · exact absurd hω (by linarith)
  · intro h
    have h2 : 0 < ω + 2 * Ω := by linarith
    have hβ : 0 < ω * (ω + 2 * Ω) := mul_pos hω h2
    exact ⟨radialEquilibrium ω Ω k, radialEquilibrium_pos ω Ω k hk hβ,
      coriolisRadialRHS_at_equilibrium ω Ω k hk hβ⟩

/-- The equilibrium radius grows with the bath rotation for a co-rotating
walker (`ω > 0`), rationalizing the increase of orbital radius with `Ω`
reported in Fig. 3f-h. -/
theorem radialEquilibrium_mono_in_Ω (ω Ω₁ Ω₂ k : ℝ) (hω : 0 < ω) (hk : 0 < k)
    (hΩ : Ω₁ ≤ Ω₂) :
    radialEquilibrium ω Ω₁ k ≤ radialEquilibrium ω Ω₂ k := by
  apply Real.sqrt_le_sqrt
  rw [← sub_nonneg]
  have hsub : ω * (ω + 2 * Ω₂) / (4 * k) - ω * (ω + 2 * Ω₁) / (4 * k)
      = 2 * ω * (Ω₂ - Ω₁) / (4 * k) := by
    field_simp
    ring
  rw [hsub]
  exact div_nonneg (mul_nonneg (mul_nonneg (le_of_lt two_pos) (le_of_lt hω)) (by linarith))
    (mul_nonneg (le_of_lt four_pos) (le_of_lt hk))

/-! ## The radial potential of equation (31) -/

/-- The radial force of equation (31) is minus the derivative of the
potential `V(r) = kr⁴ - ω(ω+2Ω)r²/2`. -/
theorem hasDerivAt_radialPotential (ω Ω k r : ℝ) :
    HasDerivAt (radialPotential ω Ω k) (-(coriolisRadialRHS r ω Ω k)) r := by
  have h4 := HasDerivAt.const_mul k (hasDerivAt_pow (4:ℕ) r)
  have h2 := HasDerivAt.const_mul (ω * (ω + 2 * Ω) / 2) (hasDerivAt_pow (2:ℕ) r)
  refine (HasDerivAt.sub h4 h2).congr_deriv ?_
  unfold coriolisRadialRHS
  norm_num
  ring

/-- The deviation of the radial potential from its equilibrium value
factorizes as a perfect square, `V(r) - V(r*) = k(r² - r*²)²`. -/
theorem radialPotential_min_identity (ω Ω k r : ℝ) (hk : 0 < k)
    (hβ : 0 ≤ ω * (ω + 2 * Ω)) :
    radialPotential ω Ω k r - radialPotential ω Ω k (radialEquilibrium ω Ω k)
      = k * (r ^ 2 - radialEquilibrium ω Ω k ^ 2) ^ 2 := by
  have hpos : 0 ≤ ω * (ω + 2 * Ω) / (4 * k) :=
    div_nonneg hβ (mul_nonneg four_pos.le hk.le)
  have hs : radialEquilibrium ω Ω k ^ 2 = ω * (ω + 2 * Ω) / (4 * k) :=
    Real.sq_sqrt hpos
  have hb : ω * (ω + 2 * Ω) = 4 * k * radialEquilibrium ω Ω k ^ 2 := by
    rw [hs]
    field_simp [hk.ne']
  show k * r ^ (4:ℕ) - ω * (ω + 2 * Ω) / 2 * r ^ (2:ℕ)
      - (k * radialEquilibrium ω Ω k ^ (4:ℕ)
        - ω * (ω + 2 * Ω) / 2 * radialEquilibrium ω Ω k ^ (2:ℕ))
      = k * (r ^ 2 - radialEquilibrium ω Ω k ^ 2) ^ 2
  rw [hb]
  ring

/-- The equilibrium radius is a global minimum of the radial potential. -/
theorem radialPotential_ge_at_equilibrium (ω Ω k r : ℝ) (hk : 0 < k)
    (hβ : 0 ≤ ω * (ω + 2 * Ω)) :
    radialPotential ω Ω k (radialEquilibrium ω Ω k) ≤ radialPotential ω Ω k r := by
  rw [← sub_nonneg, radialPotential_min_identity ω Ω k r hk hβ]
  exact mul_nonneg hk.le (sq_nonneg _)

/-- The radial potential attains its equilibrium value only at the
equilibrium radius and its reflection. -/
theorem radialPotential_eq_equilibrium_iff (ω Ω k r : ℝ) (hk : 0 < k)
    (hβ : 0 ≤ ω * (ω + 2 * Ω)) :
    radialPotential ω Ω k r = radialPotential ω Ω k (radialEquilibrium ω Ω k)
      ↔ r = radialEquilibrium ω Ω k ∨ r = -radialEquilibrium ω Ω k := by
  constructor
  · intro h
    have hz : radialPotential ω Ω k r - radialPotential ω Ω k (radialEquilibrium ω Ω k)
        = 0 := sub_eq_zero_of_eq h
    rw [radialPotential_min_identity ω Ω k r hk hβ] at hz
    rcases mul_eq_zero.mp hz with hk0 | hsq
    · exact absurd hk0 (by linarith [hk])
    · rw [pow_two, mul_eq_zero] at hsq
      rcases hsq with hs | hs
      · have habs : |r| = |radialEquilibrium ω Ω k| :=
          (sq_eq_sq_iff_abs_eq_abs r (radialEquilibrium ω Ω k)).mp (by linarith [hs])
        rcases abs_eq_abs.mp habs with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      · have habs : |r| = |radialEquilibrium ω Ω k| :=
          (sq_eq_sq_iff_abs_eq_abs r (radialEquilibrium ω Ω k)).mp (by linarith [hs])
        rcases abs_eq_abs.mp habs with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
  · rintro (h | h)
    · rw [h]
    · rw [h]
      show k * (-(radialEquilibrium ω Ω k)) ^ (4:ℕ)
          - ω * (ω + 2 * Ω) / 2 * (-(radialEquilibrium ω Ω k)) ^ (2:ℕ)
          = k * radialEquilibrium ω Ω k ^ (4:ℕ)
            - ω * (ω + 2 * Ω) / 2 * radialEquilibrium ω Ω k ^ (2:ℕ)
      ring

end Qatlib.Papers.HydroSpinLatt21.Rotation

end
