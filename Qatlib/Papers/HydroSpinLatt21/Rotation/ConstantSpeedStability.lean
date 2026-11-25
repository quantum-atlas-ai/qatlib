/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.Rotation.CircularOrbitStability
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Circular orbits of the instantaneous-radius, constant-speed model

[Saenz2021HydroSpinLattices], Methods equations (31) and (32), uses the
instantaneous radius in the Rayleigh prefactor `1 - r²ω²/u₀²`, where `u₀`
is the free walking speed. This file studies the exact zero-wave-force,
single-droplet vector field in coordinates `(r, v, ω)`:

`ṙ = v`, `v̇ = rω² + 2Ωωr - 4kr³`, and
`ω̇ = (1/τ)(1 - r²ω²/u₀²)ω - 2(v/r)(Ω + ω)`.

Thus this is deliberately separate from the fixed-reference-frequency
reduction in `CircularOrbitStability`. The strict polar derivation of the
printed rotation coefficient is `azimuthal_balance_eq32_strict`. See
[the article](https://doi.org/10.1038/s41586-021-03682-1).

At a positive-radius circular orbit, `v = 0`, `r²ω² = u₀²`, and
`4kr² = ω(ω + 2Ω)`. Eliminating the radius gives
`ω³(ω + 2Ω) = 4ku₀²`. For `Ω ≥ 0` and `k,u₀ > 0`, this equation has exactly
one positive root and exactly one root below `-2Ω`; these are respectively
the unique co-rotating and counter-rotating circular orbits.

The circular-orbit Jacobian has the additional radial Rayleigh entry
`-2ω/(τr)`. Its characteristic polynomial is

`λ³ + (2/τ)λ² + (2ω(ω+2Ω) + 4(ω+Ω)²)λ + (4/τ)ω(2ω+3Ω)`.

The Routh--Hurwitz determinant is
`a₁a₂-a₃ = (4/τ)(ω+Ω)(ω+2Ω)`, strictly positive on both branches. The
cubic criterion `cubic_re_neg_of_routh_hurwitz` therefore proves that every
characteristic root has negative real part.

These conclusions concern only this zero-wave-force single-droplet model
and its linear spectrum. They do not assert nonlinear asymptotic stability,
trefoil dynamics, multi-droplet behavior, or the experimental collective
polarization threshold.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.Rotation

open Filter Polynomial Set

/-! ## The literal zero-wave-force field (31)--(32) -/

/-- The instantaneous-radius Rayleigh term of equation (32), with constant
free walking speed `u₀`. -/
def instantaneousRayleighRHS (τ u₀ r ω : ℝ) : ℝ :=
  (1 / τ) * (1 - r ^ 2 * ω ^ 2 / u₀ ^ 2) * ω

/-- The right-hand side of equation (32) for one droplet with zero wave
force. The coefficient of the rotation term is the printed coefficient `2`. -/
def zeroWavePhaseRHS (τ u₀ Ω r v ω : ℝ) : ℝ :=
  instantaneousRayleighRHS τ u₀ r ω - 2 * (v / r) * (Ω + ω)

/-- The literal single-droplet, zero-wave-force vector field determined by
equations (31) and (32), in coordinates `(r,v,ω)`. -/
def constantSpeedSpinField (k τ u₀ Ω : ℝ) : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  fun p => (p.2.1, coriolisRadialRHS p.1 p.2.2 Ω k,
    zeroWavePhaseRHS τ u₀ Ω p.1 p.2.1 p.2.2)

/-- Specializing the strict polar azimuthal balance to zero wave force gives
exactly the phase component `zeroWavePhaseRHS` of the literal field. -/
theorem azimuthal_balance_eq32_zero_wave (m : ℝ) (r rd φ ω : ℝ → ℝ)
    (t rdd wdot D u₀ Ω τ : ℝ)
    (hr : HasDerivAt r (rd t) t) (hrd : HasDerivAt rd rdd t)
    (hφ : HasDerivAt φ (ω t) t) (hω : HasDerivAt ω wdot t) (hm : m ≠ 0)
    (hr0 : r t ≠ 0) (hτ : τ = m / D)
    (hbal : m * (r t * wdot + 2 * rd t * ω t)
      = D * (1 - (r t * ω t) ^ 2 / u₀ ^ 2) * (r t * ω t)
        - m * (2 * Ω * rd t)) :
    wdot = zeroWavePhaseRHS τ u₀ Ω (r t) (rd t) (ω t) := by
  have h := azimuthal_balance_eq32_strict m r rd φ ω t rdd wdot D u₀ 0 Ω τ
    (u₀ / r t) hr hrd hφ hω hm hr0 hτ rfl (by simpa using hbal)
  rw [h]
  simp only [zeroWavePhaseRHS, instantaneousRayleighRHS, zero_div, add_zero]
  rw [show ω t ^ 2 / (u₀ / r t) ^ 2 = r t ^ 2 * ω t ^ 2 / u₀ ^ 2 from by
    field_simp [hr0]]
  ring

/-- Away from zero frequency, the instantaneous Rayleigh term vanishes
exactly when the orbital speed has magnitude `u₀`. -/
theorem instantaneousRayleighRHS_eq_zero_iff (τ u₀ r ω : ℝ)
    (hτ : τ ≠ 0) (hu₀ : u₀ ≠ 0) (hω : ω ≠ 0) :
    instantaneousRayleighRHS τ u₀ r ω = 0 ↔ r ^ 2 * ω ^ 2 = u₀ ^ 2 := by
  unfold instantaneousRayleighRHS
  constructor
  · intro h
    have h1 : 1 / τ ≠ 0 := div_ne_zero one_ne_zero hτ
    have hpre : 1 - r ^ 2 * ω ^ 2 / u₀ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 h1
        · exact h3
      · exact absurd h2 hω
    field_simp [hu₀] at hpre
    nlinarith
  · intro h
    rw [show r ^ 2 * ω ^ 2 / u₀ ^ 2 = 1 from by field_simp [hu₀]; nlinarith]
    ring

/-- Positive-radius equilibria of the literal field are precisely circular
orbits with zero radial velocity, orbital speed `u₀`, and the radial balance
of equation (31). -/
theorem constantSpeedSpinField_eq_zero_iff (k τ u₀ Ω : ℝ) (p : ℝ × ℝ × ℝ)
    (hk : k ≠ 0) (hτ : τ ≠ 0) (hu₀ : u₀ ≠ 0) (hr : 0 < p.1) :
    constantSpeedSpinField k τ u₀ Ω p = 0 ↔
      p.2.1 = 0 ∧ p.1 ^ 2 * p.2.2 ^ 2 = u₀ ^ 2
        ∧ 4 * k * p.1 ^ 2 = p.2.2 * (p.2.2 + 2 * Ω) := by
  constructor
  · intro hz
    have hv : p.2.1 = 0 := congrArg Prod.fst hz
    have hrad : coriolisRadialRHS p.1 p.2.2 Ω k = 0 :=
      congrArg Prod.fst (congrArg Prod.snd hz)
    have hph : zeroWavePhaseRHS τ u₀ Ω p.1 p.2.1 p.2.2 = 0 :=
      congrArg Prod.snd (congrArg Prod.snd hz)
    have hbal := (coriolisRadialRHS_eq_zero_iff p.1 p.2.2 Ω k hr).mp hrad
    have hω : p.2.2 ≠ 0 := by
      intro h
      have hr3 : p.1 ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
      have h4 : (4 : ℝ) * k ≠ 0 := mul_ne_zero four_ne_zero hk
      apply (mul_ne_zero h4 hr3)
      calc
        4 * k * p.1 ^ 2 = p.2.2 * (p.2.2 + 2 * Ω) := hbal
        _ = 0 := by rw [h]; ring
    rw [hv] at hph
    simp only [zeroWavePhaseRHS, zero_div, mul_zero, zero_mul, sub_zero] at hph
    exact ⟨hv, (instantaneousRayleighRHS_eq_zero_iff τ u₀ p.1 p.2.2 hτ hu₀ hω).mp hph,
      hbal⟩
  · rintro ⟨hv, hspeed, hbal⟩
    have hω : p.2.2 ≠ 0 := by
      intro h
      rw [h] at hspeed
      norm_num at hspeed
      exact hu₀ (sq_eq_zero_iff.mp hspeed.symm)
    have hray : instantaneousRayleighRHS τ u₀ p.1 p.2.2 = 0 :=
      (instantaneousRayleighRHS_eq_zero_iff τ u₀ p.1 p.2.2 hτ hu₀ hω).mpr hspeed
    have hrad : coriolisRadialRHS p.1 p.2.2 Ω k = 0 :=
      (coriolisRadialRHS_eq_zero_iff p.1 p.2.2 Ω k hr).mpr hbal
    unfold constantSpeedSpinField zeroWavePhaseRHS
    rw [hv, hrad, hray]
    norm_num

/-- Eliminating the positive radius from the circular-orbit conditions gives
the quartic-in-`ω` equation `ω³(ω+2Ω)=4ku₀²`. -/
theorem circular_orbit_frequency_equation (k τ u₀ Ω r ω : ℝ)
    (hk : k ≠ 0) (hτ : τ ≠ 0) (hu₀ : u₀ ≠ 0) (hr : 0 < r)
    (hz : constantSpeedSpinField k τ u₀ Ω (r, 0, ω) = 0) :
    ω ^ 3 * (ω + 2 * Ω) = 4 * k * u₀ ^ 2 := by
  obtain ⟨_, hspeed, hbal⟩ :=
    (constantSpeedSpinField_eq_zero_iff k τ u₀ Ω (r, 0, ω) hk hτ hu₀ hr).mp hz
  calc
    ω ^ 3 * (ω + 2 * Ω) = (4 * k * r ^ 2) * ω ^ 2 := by rw [hbal]; ring
    _ = 4 * k * (r ^ 2 * ω ^ 2) := by ring
    _ = 4 * k * u₀ ^ 2 := by rw [hspeed]

/-- A counter-rotating circular orbit in a nonnegative rotating bath has
frequency strictly below `-2Ω`. -/
theorem counterrotating_frequency_lt (k τ u₀ Ω r ω : ℝ)
    (hk : 0 < k) (hr : 0 < r)
    (hω : ω < 0) (hz : constantSpeedSpinField k τ u₀ Ω (r, 0, ω) = 0) :
    ω < -2 * Ω := by
  have hrad : coriolisRadialRHS r ω Ω k = 0 :=
    congrArg Prod.fst (congrArg Prod.snd hz)
  exact (counter_rotating_equilibrium_iff ω Ω k hω hk).mp ⟨r, hr, hrad⟩

/-! ## Unique co- and counter-rotating frequencies -/

/-- For `Ω ≥ 0` and `k,u₀ > 0`, the eliminated circular-orbit equation has
exactly one positive frequency. -/
theorem corotating_frequency_exists_unique (k u₀ Ω : ℝ)
    (hk : 0 < k) (hu₀ : 0 < u₀) (hΩ : 0 ≤ Ω) :
    ∃! ω : ℝ, 0 < ω ∧ ω ^ 3 * (ω + 2 * Ω) = 4 * k * u₀ ^ 2 := by
  let C : ℝ := 4 * k * u₀ ^ 2
  let f : ℝ → ℝ := fun x => x ^ 3 * (x + 2 * Ω)
  have hC : 0 < C := mul_pos (mul_pos four_pos hk) (pow_pos hu₀ 2)
  have hf : Continuous f := by fun_prop
  have htop : C < f (C + 1) := by
    have hb : (1 : ℝ) ≤ C + 1 := by linarith
    have hb3 : (1 : ℝ) ≤ (C + 1) ^ 3 := one_le_pow₀ hb
    have hnonneg : 0 ≤ 2 * Ω * (C + 1) ^ 3 := by positivity
    have hid : f (C + 1) = (C + 1) ^ 4 + 2 * Ω * (C + 1) ^ 3 := by
      simp only [f]
      ring
    have hpow : C + 1 ≤ (C + 1) ^ 4 := by
      calc
        C + 1 = (C + 1) * 1 := by ring
        _ ≤ (C + 1) * (C + 1) ^ 3 :=
          mul_le_mul_of_nonneg_left hb3 (by linarith)
        _ = (C + 1) ^ 4 := by ring
    rw [hid]
    linarith
  have hmem : C ∈ Icc (f 0) (f (C + 1)) := by
    constructor
    · have hz : f 0 = 0 := by norm_num [f]
      rw [hz]
      exact hC.le
    · exact htop.le
  obtain ⟨ω, hωmem, hωeq⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ C + 1)
    hf.continuousOn hmem
  have hωroot : f ω = C := hωeq
  have hωpos : 0 < ω := by
    by_contra hcon
    have hωzero : ω = 0 := le_antisymm (not_lt.mp hcon) hωmem.1
    rw [hωzero] at hωroot
    have hz : f 0 = 0 := by norm_num [f]
    rw [hz] at hωroot
    linarith
  refine ⟨ω, ⟨hωpos, hωroot⟩, ?_⟩
  intro y hy
  have hyroot : f y = C := hy.2
  have hfactor : (y - ω) *
      (y ^ 3 + y ^ 2 * ω + y * ω ^ 2 + ω ^ 3
        + 2 * Ω * (y ^ 2 + y * ω + ω ^ 2)) = 0 := by
    have heq : f y = f ω := hyroot.trans hωroot.symm
    simp only [f] at heq
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · have hy3 : 0 < y ^ 3 := pow_pos hy.1 3
    have h1 : 0 ≤ y ^ 2 * ω := mul_nonneg (sq_nonneg y) hωpos.le
    have h2 : 0 ≤ y * ω ^ 2 := mul_nonneg hy.1.le (sq_nonneg ω)
    have h3 : 0 ≤ ω ^ 3 := (pow_pos hωpos 3).le
    have hs : 0 ≤ y ^ 2 + y * ω + ω ^ 2 := by
      nlinarith [sq_nonneg (y + ω), sq_nonneg y, sq_nonneg ω]
    have h4 : 0 ≤ 2 * Ω * (y ^ 2 + y * ω + ω ^ 2) :=
      mul_nonneg (mul_nonneg two_pos.le hΩ) hs
    linarith

/-- For `Ω ≥ 0` and `k,u₀ > 0`, the eliminated equation has exactly one
frequency in the counter-rotating admissible region `ω < -2Ω`. -/
theorem counterrotating_frequency_exists_unique (k u₀ Ω : ℝ)
    (hk : 0 < k) (hu₀ : 0 < u₀) (hΩ : 0 ≤ Ω) :
    ∃! ω : ℝ, ω < -2 * Ω ∧ ω ^ 3 * (ω + 2 * Ω) = 4 * k * u₀ ^ 2 := by
  let C : ℝ := 4 * k * u₀ ^ 2
  let g : ℝ → ℝ := fun q => q ^ 3 * (q - 2 * Ω)
  have hC : 0 < C := mul_pos (mul_pos four_pos hk) (pow_pos hu₀ 2)
  have hg : Continuous g := by fun_prop
  have htop : C < g (2 * Ω + C + 1) := by
    have hb : (1 : ℝ) ≤ 2 * Ω + C + 1 := by linarith
    have hb3 : (1 : ℝ) ≤ (2 * Ω + C + 1) ^ 3 := one_le_pow₀ hb
    have hid : g (2 * Ω + C + 1) = (2 * Ω + C + 1) ^ 3 * (C + 1) := by
      simp only [g]
      ring
    have hpos : 0 ≤ (2 * Ω + C + 1) ^ 3 := by positivity
    rw [hid]
    have hmul : C + 1 ≤ (2 * Ω + C + 1) ^ 3 * (C + 1) := by
      calc
        C + 1 = 1 * (C + 1) := by ring
        _ ≤ (2 * Ω + C + 1) ^ 3 * (C + 1) :=
          mul_le_mul_of_nonneg_right hb3 (by linarith)
    linarith
  have hmem : C ∈ Icc (g (2 * Ω)) (g (2 * Ω + C + 1)) := by
    simp only [g, sub_self, mul_zero]
    exact ⟨hC.le, htop.le⟩
  obtain ⟨q, hqmem, hqeq⟩ := intermediate_value_Icc
    (by linarith : 2 * Ω ≤ 2 * Ω + C + 1) hg.continuousOn hmem
  have hqroot : g q = C := hqeq
  have hqgt : 2 * Ω < q := by
    by_contra hcon
    have hq : q = 2 * Ω := le_antisymm (not_lt.mp hcon) hqmem.1
    rw [hq] at hqroot
    simp only [g, sub_self, mul_zero] at hqroot
    linarith
  have hqUnique : ∀ y : ℝ, 2 * Ω < y ∧ g y = C → y = q := by
    intro y hy
    have hfactor : (y - q) *
        (y ^ 2 * (y - 2 * Ω) + q ^ 2 * (q - 2 * Ω)
          + y * q * (y + q - 2 * Ω)) = 0 := by
      have heq : g y = g q := hy.2.trans hqroot.symm
      simp only [g] at heq
      nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · have h1 : 0 < y ^ 2 * (y - 2 * Ω) := mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
      have h2 : 0 < q ^ 2 * (q - 2 * Ω) := mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
      have hypos : 0 < y := by linarith
      have hqpos : 0 < q := by linarith
      have h3 : 0 < y * q * (y + q - 2 * Ω) :=
        mul_pos (mul_pos hypos hqpos) (by linarith)
      linarith
  refine ⟨-q, ⟨by linarith, ?_⟩, ?_⟩
  · have heq := hqroot
    simp only [g] at heq
    nlinarith
  · intro y hy
    have hyneg : 2 * Ω < -y ∧ g (-y) = C := by
      constructor
      · linarith [hy.1]
      · have heq := hy.2
        simp only [g]
        nlinarith
    have := hqUnique (-y) hyneg
    linarith

/-! ## The unique circular orbits -/

/-- The positive radius determined by the constant-speed condition. -/
def constantSpeedOrbitRadius (u₀ ω : ℝ) : ℝ := u₀ / |ω|

/-- The constant-speed radius is positive when `u₀` and the frequency are
nonzero. -/
theorem constantSpeedOrbitRadius_pos (u₀ ω : ℝ) (hu₀ : 0 < u₀) (hω : ω ≠ 0) :
    0 < constantSpeedOrbitRadius u₀ ω :=
  div_pos hu₀ (abs_pos.mpr hω)

/-- The constant-speed radius satisfies `r²ω²=u₀²`. -/
theorem constantSpeedOrbitRadius_speed (u₀ ω : ℝ) (hu₀ : u₀ ≠ 0) (hω : ω ≠ 0) :
    constantSpeedOrbitRadius u₀ ω ^ 2 * ω ^ 2 = u₀ ^ 2 := by
  unfold constantSpeedOrbitRadius
  rw [div_pow, sq_abs]
  field_simp [hu₀, hω]

/-- A root of the eliminated frequency equation and its constant-speed
radius satisfy the radial balance (31). -/
theorem constantSpeedOrbitRadius_balance (k u₀ Ω ω : ℝ)
    (hω : ω ≠ 0) (hroot : ω ^ 3 * (ω + 2 * Ω) = 4 * k * u₀ ^ 2) :
    4 * k * constantSpeedOrbitRadius u₀ ω ^ 2 = ω * (ω + 2 * Ω) := by
  unfold constantSpeedOrbitRadius
  rw [div_pow, sq_abs]
  field_simp [hω]
  nlinarith

/-- The co-rotating circular orbit exists and is unique among positive-radius
positive-frequency equilibria of the literal field. -/
theorem corotating_orbit_exists_unique (k τ u₀ Ω : ℝ)
    (hk : 0 < k) (hτ : 0 < τ) (hu₀ : 0 < u₀) (hΩ : 0 ≤ Ω) :
    ∃! p : ℝ × ℝ × ℝ, 0 < p.1 ∧ constantSpeedSpinField k τ u₀ Ω p = 0 ∧ 0 < p.2.2 := by
  obtain ⟨ω, ⟨hωpos, hroot⟩, hωunique⟩ := corotating_frequency_exists_unique k u₀ Ω hk hu₀ hΩ
  let r := constantSpeedOrbitRadius u₀ ω
  have hr : 0 < r := constantSpeedOrbitRadius_pos u₀ ω hu₀ hωpos.ne'
  have hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2 :=
    constantSpeedOrbitRadius_speed u₀ ω hu₀.ne' hωpos.ne'
  have hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω) :=
    constantSpeedOrbitRadius_balance k u₀ Ω ω hωpos.ne' hroot
  have hz : constantSpeedSpinField k τ u₀ Ω (r, 0, ω) = 0 :=
    (constantSpeedSpinField_eq_zero_iff k τ u₀ Ω (r, 0, ω) hk.ne' hτ.ne' hu₀.ne' hr).mpr
      ⟨rfl, hspeed, hbal⟩
  refine ⟨(r, 0, ω), ⟨hr, hz, hωpos⟩, ?_⟩
  intro p hp
  have hpcond := (constantSpeedSpinField_eq_zero_iff k τ u₀ Ω p hk.ne' hτ.ne' hu₀.ne' hp.1).mp hp.2.1
  have hpv : p.2.1 = 0 := hpcond.1
  have hproot : p.2.2 ^ 3 * (p.2.2 + 2 * Ω) = 4 * k * u₀ ^ 2 := by
    calc
      p.2.2 ^ 3 * (p.2.2 + 2 * Ω) = (4 * k * p.1 ^ 2) * p.2.2 ^ 2 := by
        rw [hpcond.2.2]
        ring
      _ = 4 * k * (p.1 ^ 2 * p.2.2 ^ 2) := by ring
      _ = 4 * k * u₀ ^ 2 := by rw [hpcond.2.1]
  have hpeq : p.2.2 = ω := hωunique p.2.2 ⟨hp.2.2, hproot⟩
  have hreq : p.1 = r := by
    have hspeedr : p.1 ^ 2 * ω ^ 2 = r ^ 2 * ω ^ 2 := by
      calc
        p.1 ^ 2 * ω ^ 2 = p.1 ^ 2 * p.2.2 ^ 2 := by rw [hpeq]
        _ = u₀ ^ 2 := hpcond.2.1
        _ = r ^ 2 * ω ^ 2 := hspeed.symm
    have hsq : p.1 ^ 2 = r ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hωpos.ne') hspeedr
    exact (sq_eq_sq₀ hp.1.le hr.le).mp hsq
  apply Prod.ext hreq
  apply Prod.ext hpv
  exact hpeq

/-- The counter-rotating circular orbit exists and is unique among
positive-radius negative-frequency equilibria of the literal field. -/
theorem counterrotating_orbit_exists_unique (k τ u₀ Ω : ℝ)
    (hk : 0 < k) (hτ : 0 < τ) (hu₀ : 0 < u₀) (hΩ : 0 ≤ Ω) :
    ∃! p : ℝ × ℝ × ℝ, 0 < p.1 ∧ constantSpeedSpinField k τ u₀ Ω p = 0 ∧ p.2.2 < 0 := by
  obtain ⟨ω, ⟨hωlt, hroot⟩, hωunique⟩ :=
    counterrotating_frequency_exists_unique k u₀ Ω hk hu₀ hΩ
  have hωneg : ω < 0 := by linarith
  let r := constantSpeedOrbitRadius u₀ ω
  have hr : 0 < r := constantSpeedOrbitRadius_pos u₀ ω hu₀ hωneg.ne
  have hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2 :=
    constantSpeedOrbitRadius_speed u₀ ω hu₀.ne' hωneg.ne
  have hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω) :=
    constantSpeedOrbitRadius_balance k u₀ Ω ω hωneg.ne hroot
  have hz : constantSpeedSpinField k τ u₀ Ω (r, 0, ω) = 0 :=
    (constantSpeedSpinField_eq_zero_iff k τ u₀ Ω (r, 0, ω) hk.ne' hτ.ne' hu₀.ne' hr).mpr
      ⟨rfl, hspeed, hbal⟩
  refine ⟨(r, 0, ω), ⟨hr, hz, hωneg⟩, ?_⟩
  intro p hp
  have hpcond := (constantSpeedSpinField_eq_zero_iff k τ u₀ Ω p hk.ne' hτ.ne' hu₀.ne' hp.1).mp hp.2.1
  have hpv : p.2.1 = 0 := hpcond.1
  have hproot : p.2.2 ^ 3 * (p.2.2 + 2 * Ω) = 4 * k * u₀ ^ 2 := by
    calc
      p.2.2 ^ 3 * (p.2.2 + 2 * Ω) = (4 * k * p.1 ^ 2) * p.2.2 ^ 2 := by
        rw [hpcond.2.2]
        ring
      _ = 4 * k * (p.1 ^ 2 * p.2.2 ^ 2) := by ring
      _ = 4 * k * u₀ ^ 2 := by rw [hpcond.2.1]
  have hpdecomp : (p.1, 0, p.2.2) = p := Prod.ext rfl (Prod.ext hpv.symm rfl)
  have hpz : constantSpeedSpinField k τ u₀ Ω (p.1, 0, p.2.2) = 0 := by
    rw [hpdecomp]
    exact hp.2.1
  have hplt : p.2.2 < -2 * Ω :=
    counterrotating_frequency_lt k τ u₀ Ω p.1 p.2.2 hk hp.1 hp.2.2 hpz
  have hpeq : p.2.2 = ω := hωunique p.2.2 ⟨hplt, hproot⟩
  have hreq : p.1 = r := by
    have hspeedr : p.1 ^ 2 * ω ^ 2 = r ^ 2 * ω ^ 2 := by
      calc
        p.1 ^ 2 * ω ^ 2 = p.1 ^ 2 * p.2.2 ^ 2 := by rw [hpeq]
        _ = u₀ ^ 2 := hpcond.2.1
        _ = r ^ 2 * ω ^ 2 := hspeed.symm
    have hsq : p.1 ^ 2 = r ^ 2 := mul_right_cancel₀ (pow_ne_zero 2 hωneg.ne) hspeedr
    exact (sq_eq_sq₀ hp.1.le hr.le).mp hsq
  apply Prod.ext hreq
  apply Prod.ext hpv
  exact hpeq

/-! ## Exact partial derivatives and the circular-orbit Jacobian -/

/-- The radial derivative of the zero-wave-force phase equation at `v=0`. -/
theorem zeroWavePhaseRHS_hasDerivAt_r (τ u₀ Ω r ω : ℝ) :
    HasDerivAt (fun x => zeroWavePhaseRHS τ u₀ Ω x 0 ω)
      (-(2 * r * ω ^ 3 / (τ * u₀ ^ 2))) r := by
  have hq : HasDerivAt (fun x : ℝ => x ^ 2 * ω ^ 2 / u₀ ^ 2)
      (2 * r * ω ^ 2 / u₀ ^ 2) r := by
    simpa using ((hasDerivAt_pow 2 r).mul_const (ω ^ 2)).div_const (u₀ ^ 2)
  have hd : HasDerivAt (fun x : ℝ => 1 - x ^ 2 * ω ^ 2 / u₀ ^ 2)
      (-(2 * r * ω ^ 2 / u₀ ^ 2)) r :=
    (hasDerivAt_const r (1 : ℝ)).sub hq |>.congr_of_eventuallyEq
      (Eventually.of_forall fun y => by simp only [Pi.sub_apply]) |>.congr_deriv (by ring)
  have hfin := ((hasDerivAt_const r (1 / τ)).mul (hd.mul_const ω))
  exact hfin.congr_of_eventuallyEq
    (Eventually.of_forall fun y => by
      simp only [zeroWavePhaseRHS, instantaneousRayleighRHS, zero_div, mul_zero,
        zero_mul, sub_zero, Pi.mul_apply]
      ring) |>.congr_deriv (by ring)

/-- The radial-velocity derivative of the zero-wave-force phase equation. -/
theorem zeroWavePhaseRHS_hasDerivAt_v (τ u₀ Ω r v ω : ℝ) :
    HasDerivAt (fun x => zeroWavePhaseRHS τ u₀ Ω r x ω)
      (-2 * (Ω + ω) / r) v := by
  have hrot : HasDerivAt (fun x : ℝ => 2 * (x / r) * (Ω + ω))
      (2 * (1 / r) * (Ω + ω)) v := by
    simpa using ((hasDerivAt_id v).div_const r).const_mul 2 |>.mul_const (Ω + ω)
  exact (hasDerivAt_const v (instantaneousRayleighRHS τ u₀ r ω)).sub hrot |>.congr_deriv (by ring)

/-- The angular-frequency derivative of the zero-wave-force phase equation at
`v=0`. -/
theorem zeroWavePhaseRHS_hasDerivAt_ω (τ u₀ Ω r ω : ℝ) :
    HasDerivAt (fun x => zeroWavePhaseRHS τ u₀ Ω r 0 x)
      ((1 / τ) * (1 - 3 * r ^ 2 * ω ^ 2 / u₀ ^ 2)) ω := by
  have hq : HasDerivAt (fun x : ℝ => r ^ 2 * x ^ 2 / u₀ ^ 2)
      (r ^ 2 * (2 * ω) / u₀ ^ 2) ω := by
    simpa using ((hasDerivAt_pow 2 ω).const_mul (r ^ 2)).div_const (u₀ ^ 2)
  have hd : HasDerivAt (fun x : ℝ => 1 - r ^ 2 * x ^ 2 / u₀ ^ 2)
      (-(r ^ 2 * (2 * ω) / u₀ ^ 2)) ω :=
    (hasDerivAt_const ω (1 : ℝ)).sub hq |>.congr_of_eventuallyEq
      (Eventually.of_forall fun y => by simp only [Pi.sub_apply]) |>.congr_deriv (by ring)
  have hfin := (hasDerivAt_const ω (1 / τ)).mul (hd.mul (hasDerivAt_id ω))
  exact hfin.congr_of_eventuallyEq
    (Eventually.of_forall fun y => by
      simp only [zeroWavePhaseRHS, instantaneousRayleighRHS, zero_div, mul_zero,
        zero_mul, sub_zero, Pi.mul_apply, id_eq]
      ring) |>.congr_deriv (by simp only [id_eq, zero_mul]; ring)

/-- The Jacobian at zero radial velocity. Its entries are justified by
`coriolisRadialRHS_hasDerivAt_r`, `coriolisRadialRHS_hasDerivAt_ω`, and the
three `zeroWavePhaseRHS_hasDerivAt_*` theorems. -/
def constantSpeedJacobian (k τ u₀ Ω r ω : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![0, 1, 0],
    ![ω * ω + 2 * Ω * ω - 12 * k * r ^ 2, 0, 2 * r * (ω + Ω)],
    ![-(2 * r * ω ^ 3 / (τ * u₀ ^ 2)), -2 * (Ω + ω) / r,
      (1 / τ) * (1 - 3 * r ^ 2 * ω ^ 2 / u₀ ^ 2)]]

/-- At a circular orbit the Jacobian simplifies, in particular its radial
Rayleigh entry is `-2ω/(τr)`. -/
theorem constantSpeedJacobian_at_orbit (k τ u₀ Ω r ω : ℝ)
    (hτ : τ ≠ 0) (hu₀ : u₀ ≠ 0) (hr : 0 < r)
    (hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2)
    (hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω)) :
    constantSpeedJacobian k τ u₀ Ω r ω =
      !![0, 1, 0;
        -(2 * (ω * (ω + 2 * Ω))), 0, 2 * r * (ω + Ω);
        -2 * ω / (τ * r), -2 * (Ω + ω) / r, -2 / τ] := by
  have hW : ω * ω + 2 * Ω * ω - 12 * k * r ^ 2 = -(2 * (ω * (ω + 2 * Ω))) := by
    rw [show 12 * k * r ^ 2 = 3 * (4 * k * r ^ 2) from by ring, hbal]
    ring
  have hR : -(2 * r * ω ^ 3 / (τ * u₀ ^ 2)) = -2 * ω / (τ * r) := by
    have hω : ω ≠ 0 := by
      intro h
      rw [h] at hspeed
      norm_num at hspeed
      exact hu₀ (sq_eq_zero_iff.mp hspeed.symm)
    field_simp [hτ, hu₀, hr.ne', hω]
    nlinarith
  have hE : (1 / τ) * (1 - 3 * r ^ 2 * ω ^ 2 / u₀ ^ 2) = -2 / τ := by
    field_simp [hτ, hu₀]
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [constantSpeedJacobian, hW, hR]
  simpa only [one_div] using hE

/-- The determinant of the circular-orbit Jacobian. -/
theorem constantSpeedJacobian_det_eq (k τ u₀ Ω r ω : ℝ)
    (hτ : τ ≠ 0) (hu₀ : u₀ ≠ 0) (hr : 0 < r)
    (hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2)
    (hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω)) :
    (constantSpeedJacobian k τ u₀ Ω r ω).det = -(4 / τ) * (ω * (2 * ω + 3 * Ω)) := by
  rw [constantSpeedJacobian_at_orbit k τ u₀ Ω r ω hτ hu₀ hr hspeed hbal]
  eval_det
  field_simp [hτ, hr.ne']
  ring

/-! ## Characteristic polynomial and spectral stability -/

/-- The characteristic polynomial of the circular-orbit Jacobian. -/
theorem charpoly_constantSpeedJacobian_at_orbit (k τ u₀ Ω r ω : ℝ)
    (hτ : τ ≠ 0) (hu₀ : u₀ ≠ 0) (hr : 0 < r)
    (hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2)
    (hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω)) :
    (constantSpeedJacobian k τ u₀ Ω r ω).charpoly =
      X ^ 3 + C (2 / τ) * X ^ 2
        + C (2 * ω * (ω + 2 * Ω) + 4 * (ω + Ω) ^ 2) * X
        + C ((4 / τ) * (ω * (2 * ω + 3 * Ω))) := by
  apply Polynomial.funext
  intro t
  have hcp := Matrix.eval_charpoly (constantSpeedJacobian k τ u₀ Ω r ω) t
  have hmat := constantSpeedJacobian_at_orbit k τ u₀ Ω r ω hτ hu₀ hr hspeed hbal
  have hdet : (Matrix.scalar (Fin 3) t - !![0, 1, 0;
        -(2 * (ω * (ω + 2 * Ω))), 0, 2 * r * (ω + Ω);
        -2 * ω / (τ * r), -2 * (Ω + ω) / r, -2 / τ]) =
      !![t, -1, 0; 2 * (ω * (ω + 2 * Ω)), t, -(2 * r * (ω + Ω));
        2 * ω / (τ * r), 2 * (Ω + ω) / r, t + 2 / τ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    all_goals ring
  rw [hcp, hmat, hdet]
  eval_det
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp [hτ, hr.ne']
  ring

/-- Routh--Hurwitz spectral stability of either admissible rotation sense.
The strict determinant identity is
`a₁a₂-a₃=(4/τ)(ω+Ω)(ω+2Ω)`. -/
theorem constantSpeed_charpoly_roots_re_neg (k τ u₀ Ω r ω : ℝ)
    (hτ : 0 < τ) (hu₀ : u₀ ≠ 0) (hΩ : 0 ≤ Ω) (hr : 0 < r)
    (hsense : 0 < ω ∨ ω < -2 * Ω)
    (hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2)
    (hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω)) :
    ∀ z : ℂ, ((constantSpeedJacobian k τ u₀ Ω r ω).charpoly.map
      Complex.ofRealHom).eval z = 0 → z.re < 0 := by
  have hprod : 0 < ω * (2 * ω + 3 * Ω) := by
    rcases hsense with hω | hω
    · exact mul_pos hω (by linarith)
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hfac : 0 < (ω + Ω) * (ω + 2 * Ω) := by
    rcases hsense with hω | hω
    · exact mul_pos (by linarith) (by linarith)
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  intro z hzroot
  rw [charpoly_constantSpeedJacobian_at_orbit k τ u₀ Ω r ω hτ.ne' hu₀ hr hspeed hbal,
    ← Polynomial.eval₂_eq_eval_map] at hzroot
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X] at hzroot
  exact cubic_re_neg_of_routh_hurwitz (2 / τ)
    (2 * ω * (ω + 2 * Ω) + 4 * (ω + Ω) ^ 2)
    ((4 / τ) * (ω * (2 * ω + 3 * Ω))) z
    (div_pos two_pos hτ) (mul_pos (div_pos four_pos hτ) hprod) (by
      have hkey : (2 : ℝ) / τ * (2 * ω * (ω + 2 * Ω) + 4 * (ω + Ω) ^ 2)
          - (4 / τ) * (ω * (2 * ω + 3 * Ω)) =
          (4 / τ) * ((ω + Ω) * (ω + 2 * Ω)) := by
        field_simp
        ring
      rw [← sub_pos, hkey]
      exact mul_pos (div_pos four_pos hτ) hfac) hzroot

/-- Every characteristic root of a co-rotating circular orbit lies in the
open left half-plane. -/
theorem corotating_charpoly_roots_re_neg (k τ u₀ Ω r ω : ℝ)
    (hτ : 0 < τ) (hu₀ : u₀ ≠ 0) (hΩ : 0 ≤ Ω) (hr : 0 < r) (hω : 0 < ω)
    (hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2)
    (hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω)) :
    ∀ z : ℂ, ((constantSpeedJacobian k τ u₀ Ω r ω).charpoly.map
      Complex.ofRealHom).eval z = 0 → z.re < 0 :=
  constantSpeed_charpoly_roots_re_neg k τ u₀ Ω r ω hτ hu₀ hΩ hr (Or.inl hω) hspeed hbal

/-- Every characteristic root of a counter-rotating circular orbit lies in
the open left half-plane. -/
theorem counterrotating_charpoly_roots_re_neg (k τ u₀ Ω r ω : ℝ)
    (hτ : 0 < τ) (hu₀ : u₀ ≠ 0) (hΩ : 0 ≤ Ω) (hr : 0 < r) (hω : ω < -2 * Ω)
    (hspeed : r ^ 2 * ω ^ 2 = u₀ ^ 2)
    (hbal : 4 * k * r ^ 2 = ω * (ω + 2 * Ω)) :
    ∀ z : ℂ, ((constantSpeedJacobian k τ u₀ Ω r ω).charpoly.map
      Complex.ofRealHom).eval z = 0 → z.re < 0 :=
  constantSpeed_charpoly_roots_re_neg k τ u₀ Ω r ω hτ hu₀ hΩ hr (Or.inr hω) hspeed hbal

end Qatlib.Papers.HydroSpinLatt21.Rotation

end
