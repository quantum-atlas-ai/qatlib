/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.BesselCoefficientBridge
public import Qatlib.Papers.HydroSpinLatt21.GKModel.SignedPairPotential
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.HistoryLimit
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.OrbitForceReduction
public import Qatlib.Papers.HydroSpinLatt21.Rotation.CoriolisRadialBalance
public import Qatlib.Papers.HydroSpinLatt21.Rotation.PolarKinematics

@[expose] public section

/-!
# Consumers of the analytic HydroSpinLatt21 development

Concrete nondegenerate instances of the analytic Dev modules for
[Saenz2021HydroSpinLattices] Methods equations (8)-(16), (23)-(26) and
(31): signed pair-potential values and force signs, azimuthal wave-force
opposition and the non-gradient witness, the constant-profile instance of
the Bessel-to-GK bridge, exactness of the low-memory bound for a
Lipschitz-free kernel, circular-orbit projections, the tangential balance
reduction at explicit parameters, and the co- and counter-rotating equilibrium
thresholds of the rotating-frame radial equation. The final examples show
that the sign of the curvature coefficient alone does not fix the force
sign, closing the missing-premise demos. The axiom closures of the main
theorems are checked at the end.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped NNReal Topology

namespace QatlibTests.HydroSpinLatticeAnalyticRegression

open Qatlib.Papers.HydroSpinLatt21.GKModel
open Qatlib.Papers.HydroSpinLatt21.BesselModel
open Qatlib.Papers.HydroSpinLatt21.Rotation

/-- At a separated pair of phases the two Bessel profiles give the same
left force after accounting for their sign. -/
example : leftAzimuthForce 2 besselJ0Slope 1 1 5 (Real.pi / 2) 0 =
    leftAzimuthForce (-2) besselJ1Profile 1 1 5 (Real.pi / 2) 0 :=
  (azimuth_forces_eq_besselJ1 2 1 1 5 (Real.pi / 2) 0).1

/-- The full Bessel history exists for separated orbits with a neighbor
rotating at nonzero unit angular speed. -/
example : ∃ C ≥ 0, ∀ t : ℝ,
    MeasureTheory.IntegrableOn
      (fun u => leftAzimuthForce (-2) besselJ1Profile 1 1 5 (Real.pi / 2) (t - u) *
        Real.exp (-u)) (Set.Ioi 0) ∧
    |(∫ u in Set.Ioi (0 : ℝ),
        leftAzimuthForce (-2) besselJ1Profile 1 1 5 (Real.pi / 2) (t - u) * Real.exp (-u)) -
      leftAzimuthForce 2 besselJ0Slope 1 1 5 (Real.pi / 2) t| ≤ C := by
  obtain ⟨C, hC, h⟩ := left_bessel_memory_error 2 1 1 5 (Real.pi / 2) 1
    (by norm_num) (by norm_num) (by norm_num) id differentiable_id (by simp)
  exact ⟨C, hC, fun t => by simpa using h t 1 (by norm_num)⟩

/-- The right orbit has a full history for a neighbor rotating at unit speed. -/
example : ∃ C ≥ 0, ∀ t : ℝ,
    MeasureTheory.IntegrableOn
      (fun u => rightAzimuthForce (-2) besselJ1Profile 1 1 5 (t - u) (Real.pi / 2) *
        Real.exp (-u)) (Set.Ioi 0) ∧
    |(∫ u in Set.Ioi (0 : ℝ),
        rightAzimuthForce (-2) besselJ1Profile 1 1 5 (t - u) (Real.pi / 2) * Real.exp (-u)) -
      rightAzimuthForce 2 besselJ0Slope 1 1 5 t (Real.pi / 2)| ≤ C := by
  obtain ⟨C, hC, h⟩ := right_bessel_memory_error 2 1 1 5 (Real.pi / 2) 1
    (by norm_num) (by norm_num) (by norm_num) id differentiable_id (by simp)
  exact ⟨C, hC, fun t => by simpa using h t 1 (by norm_num)⟩

/-- With neighbors rotating in opposite directions, the same estimate
applies at each time as the receiving phase changes. -/
example : ∃ C ≥ 0, ∃ M ≥ 0, ∀ t : ℝ,
    |twoNeighborBesselForce 2 1 1 5 (2 * t) t 1 id (fun s => -s) -
      (besselGkPairForce 2 1 1 5 (2 * t) t + besselGkPairForce 2 1 1 5 (2 * t) (-t))| ≤
      C * (1 + 1) + 2 * besselForceRemainder 2 1 1 5 M := by
  obtain ⟨C, hC, M, hM, h⟩ := two_neighbor_bessel_approx_gk 2 1 1 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, M, hM, fun t => ?_⟩
  simpa only [id_eq, mul_one] using h id (fun s => -s) 1 1
    differentiable_id differentiable_id.neg (by simp) (by simp) (2 * t) t 1 one_pos

/-- The comparison applies to two distinct stationary states on a four-site
ring with a nonzero wave prefactor. The full history force vanishes for
horizontal phases, and their initial maximum phase mismatch is `π`. -/
example : ∃ M ≥ 0, ∃ K : ℝ≥0, ∀ T > (0 : ℝ), ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.pi ≤ gronwallBound Real.pi K (2 * besselForceRemainder 2 1 1 5 M) t := by
  let left (i : Fin 4) := i - 1
  let right (i : Fin 4) := i + 1
  let p (i : Fin 4) : ℝ := if i = 0 then 0 else Real.pi
  let q₀ : AngularState (Fin 4) := (p, 0)
  have hs (i : Fin 4) : Real.sin (p i) = 0 := by
    unfold p
    split <;> simp
  have hgk : gkLatticeRhs 2 1 1 5 1 1 1 left right (0 : AngularState (Fin 4)) = 0 := by
    simp [gkLatticeRhs, rayleighDrift, besselGkPairForce, gkPairForce, Pi.zero_def]
  have hd : dist q₀ 0 = Real.pi := by
    rw [dist_zero_right, Prod.norm_def]
    change max ‖p‖ ‖(0 : Fin 4 → ℝ)‖ = Real.pi
    rw [norm_zero, max_eq_left (norm_nonneg _)]
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2 fun i => ?_
      rw [Real.norm_eq_abs]
      unfold p
      split <;> simp [Real.pi_pos.le]
    · simpa [p, Real.norm_eq_abs, Real.pi_pos.le] using norm_le_pi_norm p 1
  obtain ⟨C, hC, M, hM, K, h⟩ :=
    dist_bessel_gk_trajectories left right 2 1 1 5 1 1 1 1 1 0 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
      (by norm_num) (by norm_num)
  refine ⟨M, hM, K, fun T hT t ht => ?_⟩
  have hbound := h 0 1 T Real.pi (fun _ => q₀) 0 0 hT
    continuousOn_const continuousOn_const
    (fun s _ => (hasDerivAt_const s q₀).hasDerivWithinAt)
    (fun s _ => by rw [Pi.zero_apply, hgk]; exact (hasDerivAt_const s 0).hasDerivWithinAt)
    (fun i => differentiable_const (q₀.1 i)) (fun _ _ => by simp)
    (fun _ _ _ => by simp [q₀]) (fun _ _ _ => by simp) (fun _ _ => rfl)
    (fun s _ i => by
      simp [q₀, twoNeighborBesselForce, averageOrbitForce, leftAzimuthForce, rightAzimuthForce,
        Real.sin_sub, hs])
    hd.le t ht
  simpa only [Pi.zero_apply, hd, add_zero, zero_add, mul_zero, zero_mul, one_mul, div_one, sub_zero]
    using hbound

/-- A radius-dependent family of stationary equal-phase states has zero
net Bessel history force at nonzero wave prefactor. Its phase mismatch
vanishes in the joint limit, giving a four-site uniform convergence example. -/
example {p : Filter ℝ} (r T : ℝ → ℝ) (hr : Tendsto r p (𝓝 0)) (hT : Tendsto T p (𝓝 0))
    (hparam : ∀ᶠ n in p, 0 < r n ∧ r n ≤ 5 / 4 ∧ 0 < T n) :
    TendstoUniformlyOn (fun (n : ℝ) (_ : ℝ) => (((fun _ => r n), 0) : AngularState (Fin 4)))
      (fun _ => 0) p (Set.Icc (0 : ℝ) 1) := by
  let left (i : Fin 4) := i - 1
  let right (i : Fin 4) := i + 1
  let state (φ : ℝ) : AngularState (Fin 4) := ((fun _ => φ), 0)
  let q (n : ℝ) : ℝ → AngularState (Fin 4) := fun _ => state (r n)
  have hzero : gkLatticeRhs 2 1 1 5 1 1 1 left right (0 : AngularState (Fin 4)) = 0 := by
    simp [gkLatticeRhs, rayleighDrift, besselGkPairForce, gkPairForce, Pi.zero_def]
  have hforce (ρ t T' φ : ℝ) :
      twoNeighborBesselForce 2 1 ρ 5 φ t T' (fun _ => φ) (fun _ => φ) = 0 := by
    have hopp : leftAzimuthForce (-2) besselJ1Profile 1 ρ 5 φ φ =
        -rightAzimuthForce (-2) besselJ1Profile 1 ρ 5 φ φ := by
      simp only [leftAzimuthForce, rightAzimuthForce, neg_mul]
    simp only [twoNeighborBesselForce, hopp, averageOrbitForce, neg_mul,
      MeasureTheory.integral_neg, neg_div, add_neg_cancel]
  have hd (n : ℝ) : dist (q n 0) 0 = |r n| := by
    rw [dist_zero_right, Prod.norm_def]
    change max ‖fun _ : Fin 4 => r n‖ ‖(0 : Fin 4 → ℝ)‖ = |r n|
    simp [Real.norm_eq_abs]
  have hinit : Tendsto (fun n => dist (q n 0) 0) p (𝓝 0) := by
    simpa only [hd, abs_zero] using hr.abs
  refine tendsto_uniformly_on_small_orbit left right 2 1 5 1 1 1 1 0 0 0 1
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) r T q 0 0 hr hT hinit
    ?_ continuousOn_const ?_ ?_
  · filter_upwards [hparam] with n hn
    refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
    refine ⟨continuousOn_const, fun s _ => (hasDerivAt_const s (state (r n))).hasDerivWithinAt,
      fun _ => differentiable_const (r n), fun _ _ => by simp [q, state], ?_, fun _ _ => rfl, ?_⟩
    · intro s _ i
      simp [q, state]
    · intro s _ i
      simp [q, state, hforce]
  · intro t _
    rw [Pi.zero_apply, hzero]
    exact (hasDerivAt_const t 0).hasDerivWithinAt
  · intro t _ i
    simp

#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.tendsto_uniformly_on_small_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.gk_acceleration_error_small_orbit
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.dist_bessel_gk_trajectories
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.two_neighbor_bessel_approx_gk
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.gk_acceleration_error_of_bessel_balance
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.left_bessel_memory_error
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.right_bessel_memory_error

/-- A four-site ring with a discontinuous prehistory can enter the
joint limit theorem. The lifted phases jump from `π` to zero at the
initial time. Each physical tangential force vanishes along this
trajectory, since the emitter and receiver phases stay horizontal. -/
example {p : Filter ℝ} (r T : ℝ → ℝ) (hr : Tendsto r p (𝓝 0)) (hT : Tendsto T p (𝓝 0))
    (hparam : ∀ᶠ n in p, 0 < r n ∧ r n ≤ 5 / 4 ∧ 0 < T n) :
    TendstoUniformlyOn (fun (_ : ℝ) (t : ℝ) =>
      (((fun _ => if t < 0 then Real.pi else 0), 0) : AngularState (Fin 4)))
      (fun _ => 0) p (Set.Icc (0 : ℝ) 1) := by
  let left (i : Fin 4) := i - 1
  let right (i : Fin 4) := i + 1
  let θ (t : ℝ) := if t < 0 then Real.pi else 0
  let q (t : ℝ) : AngularState (Fin 4) := (fun _ => θ t, 0)
  have hphase (t : ℝ) : Real.sin (θ t) = 0 := by
    unfold θ
    split <;> simp
  have hqzero (t : ℝ) (ht : 0 ≤ t) : q t = 0 := by
    simp [q, θ, not_lt.mpr ht, Pi.zero_def]
  have hcont : ContinuousOn q (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.congr (fun t ht => hqzero t ht.1)
  have hderiv (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivWithinAt q (0 : AngularState (Fin 4)) (Set.Ici t) t :=
    (hasDerivAt_const t (0 : AngularState (Fin 4))).hasDerivWithinAt.congr_of_mem
      (fun s hs => hqzero s (ht.1.trans hs)) le_rfl
  have hzero : gkLatticeRhs 2 1 1 5 1 1 1 left right (0 : AngularState (Fin 4)) = 0 := by
    simp [gkLatticeRhs, rayleighDrift, besselGkPairForce, gkPairForce, Pi.zero_def]
  have hforce (ρ t T' : ℝ) : twoNeighborBesselForce 2 1 ρ 5 0 t T' θ θ = 0 := by
    simp [twoNeighborBesselForce, averageOrbitForce, leftAzimuthForce, rightAzimuthForce, hphase]
  refine tendsto_uniformly_on_small_orbit_of_measurable_history left right 2 1 5 1 1 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) r T
    (fun _ => q) (fun _ _ => 0) 0 hr hT ?_ ?_ continuousOn_const ?_
  · simpa [hqzero _ le_rfl] using tendsto_const_nhds (x := (0 : ℝ)) (f := p)
  · filter_upwards [hparam] with n hn
    refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
    refine besselTrajectoryOn_of_tangential_balance (D := 1) hn.1.ne' (by norm_num)
      (by norm_num) hcont (fun t ht => by simpa using hderiv t ht) ?_ ?_ ?_
    · intro i
      change Measurable θ
      exact measurable_const.piecewise measurableSet_Iio measurable_const
    · intro t ht
      rfl
    · intro t ht i
      have hθ : θ t = 0 := by simp [θ, not_lt.mpr ht.1]
      simp [q, hθ, hforce]
  · intro t _
    rw [Pi.zero_apply, hzero]
    exact (hasDerivAt_const t 0).hasDerivWithinAt

#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.exists_rayleigh_speed_bound
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.abs_two_neighbor_bessel_force_le
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.dist_small_orbit_of_measurable_history
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.tendsto_uniformly_on_small_orbit_of_measurable_history

/-! ## Signed pair potential consumers -/

/-- The FM- antiphased pair value `2a` at a concrete mixed-sign
coefficient pair `(a, b) = (1, -1)`. -/
theorem pair_potential_anti_phase_concrete :
    gkPairPotential 1 (-1) 0 Real.pi = 2 := by
  rw [gk_pair_potential_anti_phase 1 (-1)]
  ring

/-- The AFM+ vertically opposed pair value `2b` at the same coefficients:
with `b = -1 < 0 < 1 = a`, the antiphased horizontal configuration is the
strictly smaller one, as the four-mode classification predicts. -/
theorem pair_potential_vertical_concrete :
    gkPairPotential 1 (-1) (Real.pi / 2) (-(Real.pi / 2)) = -2 := by
  rw [gk_pair_potential_vertical_opposition 1 (-1)]
  ring

/-- Missing-premise demo: positive curvature coefficient alone does not
force the pair force to be negative; the gradient coefficient decides at
the phase pair `(0, π/2)`. -/
theorem pair_force_sign_needs_gradient_sign :
    0 < gkPairForce 1 1 0 (Real.pi / 2) :=
  gk_pair_force_zero_pi_half_pos 1 1 (by norm_num)

/-- Missing-premise demo: with positive curvature, the force at
`(π/2, 0)` is strictly negative for every gradient coefficient. -/
theorem pair_force_negative_at_pi_half (b : ℝ) :
    gkPairForce 1 b (Real.pi / 2) 0 < 0 :=
  gk_pair_force_pi_half_zero_neg 1 b (by norm_num)

/-! ## Bessel model bridge consumers -/

/-- The two azimuthal wave forces are exactly opposite at the top
configuration, for the concrete profile `g(x) = e^{-x}` with `F = k = 1`,
`r = 1`, `L = 2`. -/
theorem wave_force_top_opposition_concrete :
    leftAzimuthForce 1 (fun x => Real.exp (-x)) 1 1 2 (Real.pi / 2) (Real.pi / 2)
        + rightAzimuthForce 1 (fun x => Real.exp (-x)) 1 1 2 (Real.pi / 2) (Real.pi / 2)
      = 0 := by
  obtain ⟨h1, h2⟩ :=
    azimuth_force_at_top 1 (fun x => Real.exp (-x)) 1 1 2 (by norm_num)
  rw [h1, h2]
  ring

/-- Non-gradient witness, concretely: with the profile `g(x) = e^{-x}`,
`F = k = 1`, `r = 1`, `L = 2`, the azimuthal wave forces cannot be the
gradient of any exchange-symmetric pair potential. -/
theorem wave_force_not_gradient_concrete :
    ¬ ∃ U : ℝ → ℝ → ℝ,
      IsSymmetricPairGradient U
        (fun φi φj => leftAzimuthForce 1 (fun x => Real.exp (-x)) 1 1 2 φi φj)
        (fun φi φj => rightAzimuthForce 1 (fun x => Real.exp (-x)) 1 1 2 φi φj) :=
  wave_force_not_symmetric_pair_gradient 1 (fun x => Real.exp (-x)) 1 1 2
    (by norm_num) (by simp [Real.exp_ne_zero])

/-- Nondegenerate instance of the Bessel-to-GK bridge: for the constant
profile `g ≡ 1` (derivative `gp ≡ 0`, so the Lipschitz constant `M2 = 0`
suffices) with `F = k = r = 1`, `L = 4`, the controlled-remainder bound
holds at every phase pair. -/
theorem wave_force_approx_gk_constant_profile (φi φj : ℝ) :
    |leftAzimuthForce 1 (fun _ => (1:ℝ)) 1 1 4 φi φj
        - (gkPairForce (1 * 1 * 1 * 0) (1 * 1 / 4 * 1) φi φj
          - 1 * 1 * Real.sin φi)|
      ≤ |(1:ℝ)| * (2 * |1| * 1 / 4
        + 2 * |0| * 1 * 1 ^ 2 / 4
        + 4 * |0| * 1 * 1 ^ 2 / 4 * (1 + 1 / 4)
        + 9 * 0 * (1 * 1) ^ 2 * (1 + 1 / 4)
        + 6 * 1 / 4 * (1 + 1 / 4) * (|1| + 3 * |0| * 1 * 1 + 9 * 0 * (1 * 1) ^ 2)) :=
  left_azimuth_force_approx_gk_force 1 (fun _ => (1:ℝ)) (fun _ => 0) 1 1 4 φi φj 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun y => hasDerivAt_const (c := (1:ℝ)) y)
    (fun z _ => by simp)

/-! ## Low-memory reduction consumers -/

/-- For a lag-independent kernel the Lipschitz constant `Λ = 0` is exact:
the memory bound forces the memory integral to equal the memory-free
value, so the low-memory reduction of equation (15) is an identity. -/
theorem memory_bound_constant_kernel_exact (T R c : ℝ) (hT : 0 < T) (hR : 0 ≤ R) :
    ∫ u in (0:ℝ)..R, c * Real.exp (-(u / T))
      = c * (T * (1 - Real.exp (-(R / T)))) := by
  have h := memory_integral_bound T R 0 hT hR (fun _ => c) le_rfl continuous_const
    (fun u _ => by simp)
  have hz0 : 0 * T ^ 2 * (1 - (1 + R / T) * Real.exp (-(R / T))) = 0 := by ring
  rw [hz0] at h
  have h0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  exact sub_eq_zero.mp h0

/-- The exponential memory weight integrates to the memory-free truncation
times `T` at concrete parameters. -/
theorem exp_integral_concrete (R : ℝ) :
    ∫ u in (0:ℝ)..R, Real.exp (-(u / 2)) = 2 * (1 - Real.exp (-(R / 2))) :=
  exp_integral 2 R (by norm_num)

/-- A kernel with unit slope attains the normalized memory error bound. -/
theorem affine_kernel_memory_error (T : ℝ) (hT : 0 < T) :
    (∫ u in Set.Ioi (0 : ℝ), (1 + u) * Real.exp (-(u / T))) / T - 1 = T := by
  obtain ⟨h₀, e₀⟩ := exp_weight_Ioi T hT
  obtain ⟨h₁, e₁⟩ := lag_exp_Ioi T hT
  simp_rw [add_mul, one_mul]
  rw [MeasureTheory.integral_add h₀ h₁, e₀, e₁]
  field_simp
  ring

/-! ## Orbit kinematics consumers -/

/-- The azimuthal projection of the orbit velocity is `r ω` at concrete
parameters. -/
theorem tangent_speed_concrete :
    planeDot (orbitVelVec 2 3 (Real.pi / 2)) (orbitAzimuth (Real.pi / 2)) = 6 := by
  rw [orbitVelVec_dot_azimuth 2 3 (Real.pi / 2)]
  norm_num

/-- The radial component of the orbit acceleration is `-r ω²` at
`(r, ω, ω̇) = (2, 3, 5)`, independent of the angular acceleration. -/
theorem radial_accel_concrete (φ : ℝ) :
    planeDot (orbitAccVec 2 3 5 φ) (radialUnit φ) = -(2 * 3 * 3) :=
  orbitAccVec_dot_radial 2 3 5 φ

/-- Concrete evaluation of the acceleration components at zero azimuth:
`(−rω², rω̇) = (−18, 10)`. -/
theorem accel_components_at_zero :
    (orbitAccVec 2 3 5 (0:ℝ)).1 = -(18:ℝ) ∧ (orbitAccVec 2 3 5 (0:ℝ)).2 = 10 := by
  constructor
  · simp only [orbitAccVec, Real.sin_zero, Real.cos_zero]
    ring
  · simp only [orbitAccVec, Real.sin_zero, Real.cos_zero]
    ring

/-- The tangential balance reduction (11) to (12) at concrete parameters
`m = 2`, `r = 1`, `D = 4`, `u₀ = 3`, `ω₀ = 3`, `ω = 3`, `Fθ = 1`: the
phase equation value is `1/2`. -/
theorem tangential_reduction_concrete :
    1 / (2 / 4) * (1 - (3:ℝ) ^ 2 / 3 ^ 2) * 3 + 1 / (2 * 1) = 1 / 2 := by
  have h := tangential_balance_reduction 2 1 4 (2 / 4) 3 3 (1 / 2) 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.symm

/-! ## Rotating-frame radial balance consumers -/

/-- The positive equilibrium radius of equation (31) at
`(ω, Ω, k) = (1, 1.5, 1)`, where `ω(ω + 2Ω) = 4`, is an exact
equilibrium. -/
theorem coriolis_equilibrium_concrete :
    coriolisRadialRHS (radialEquilibrium 1 1.5 1) 1 1.5 1 = 0 :=
  coriolisRadialRHS_at_equilibrium 1 1.5 1 (by norm_num) (by norm_num)

/-- Below the counter-rotation threshold: with `ω = -0.5`, `Ω = 0.3` we
have `|ω| = 0.5 < 0.6 = 2Ω`, so no positive radius is an equilibrium. -/
theorem coriolis_no_equilibrium_below_threshold (r : ℝ) (hr : 0 < r) :
    coriolisRadialRHS r (-0.5) 0.3 1 ≠ 0 :=
  coriolisRadialRHS_ne_zero_of_nonpos _ _ _ _ (by norm_num) hr (by norm_num)

/-- Above the counter-rotation threshold: with `ω = -1`, `Ω = 0.3` we
have `|ω| = 1 > 0.6 = 2Ω`, and a positive equilibrium radius exists. -/
theorem coriolis_equilibrium_above_counter_threshold :
    ∃ r : ℝ, 0 < r ∧ coriolisRadialRHS r (-1) (3 / 10 : ℝ) 1 = 0 := by
  have hiff := counter_rotating_equilibrium_iff (-(1:ℝ)) (3 / 10 : ℝ) 1
    (by norm_num) (by norm_num)
  have hlt : (-1:ℝ) < -2 * (3 / 10 : ℝ) := by norm_num
  exact hiff.mpr hlt

/-- The co-rotating equilibrium radius increases with the bath rotation,
at concrete rates `Ω = 0.3` and `Ω = 0.7`. -/
theorem coriolis_equilibrium_monotone_concrete :
    radialEquilibrium 1 0.3 1 ≤ radialEquilibrium 1 0.7 1 :=
  radialEquilibrium_mono_in_Ω 1 0.3 0.7 1 (by norm_num) (by norm_num) (by norm_num)

/-- The radial potential identity at `(ω, Ω, k) = (1, 1.5, 1)`, where the
equilibrium radius is `r* = 1`: `V(r) - V(1) = (r² - 1)²`. -/
theorem radial_potential_identity_concrete (r : ℝ) :
    radialPotential 1 1.5 1 r - radialPotential 1 1.5 1 (radialEquilibrium 1 1.5 1)
      = (r ^ 2 - 1) ^ 2 := by
  have h := radialPotential_min_identity 1 1.5 1 r (by norm_num) (by norm_num)
  have hs : radialEquilibrium 1 1.5 1 = 1 := by
    unfold radialEquilibrium
    rw [show (1 * (1 + 2 * (1.5:ℝ)) / (4 * 1)) = 1 from by norm_num, Real.sqrt_one]
  rw [h, hs]
  ring

/-! ## Physical Bessel profile consumers -/

/-- The `J₀` wave profile evaluates to `1` at the origin, matching
`Complex.besselJ_zero`. -/
theorem besselJ0_profile_zero : besselJ0Profile 0 = 1 := by
  simp [besselJ0Profile, Complex.besselJ_zero]

/-- The slope profile is differentiable everywhere, with the curvature
profile as its derivative — the derivative orders of equations (25), (26)
hold for the physical profile. -/
theorem besselJ0_slope_differentiable : Differentiable ℝ besselJ0Slope :=
  differentiable_besselJ0Slope

/-- Existence of a remainder constant for the instantiated bridge at a
concrete small-orbit parameter set. -/
theorem bessel_bridge_remainder_exists_concrete :
    ∃ M2 : ℝ, 0 ≤ M2 ∧
      |leftAzimuthForce 1 besselJ0Slope 1 1 4 0 1
        - (gkPairForce (1 * 1 * 1 * besselJ0Curv (1 * 4))
            (1 * 1 / 4 * besselJ0Slope (1 * 4)) 0 1
          - 1 * besselJ0Slope (1 * 4) * Real.sin 0)|
      ≤ |(1:ℝ)| * (2 * |besselJ0Slope (1 * 4)| * 1 / 4
        + 2 * |besselJ0Curv (1 * 4)| * 1 * 1 ^ 2 / 4
        + 4 * |besselJ0Curv (1 * 4)| * 1 * 1 ^ 2 / 4 * (1 + 1 / 4)
        + 9 * M2 * (1 * 1) ^ 2 * (1 + 1 / 4)
        + 6 * 1 / 4 * (1 + 1 / 4) * (|besselJ0Slope (1 * 4)|
            + 3 * |besselJ0Curv (1 * 4)| * 1 * 1
            + 9 * M2 * (1 * 1) ^ 2)) :=
  exists_bessel_remainder_bound 1 1 1 4 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Variable-radius polar kinematics: the azimuthal projection of the
acceleration carries the `2ṙω` term at concrete parameter values. -/
theorem polar_acc_azimuth_concrete :
    ∃ acc : ℝ × ℝ,
      HasDerivAt (polarVel (fun _ => 2) (fun _ => 0) (fun s => s) (fun _ => 1)) acc 1
        ∧ planeDot acc (radialUnit ((fun s => s) 1)) = 0 - 2 * 1 * 1
        ∧ planeDot acc (orbitAzimuth ((fun s => s) 1)) = 2 * 0 + 2 * 0 * 1 :=
  polar_acc_projections (fun _ => 2) (fun _ => 0) (fun s => s) (fun _ => 1) 1 0 0
    (hasDerivAt_const (c := (2:ℝ)) 1) (hasDerivAt_const (c := (0:ℝ)) 1)
    (hasDerivAt_id (1:ℝ)) (hasDerivAt_const (c := (1:ℝ)) 1)

/-- Coriolis radial component at a concrete rotating pair: with `r = 2`,
`ω = 3`, `Ω = 0.5` the radial Coriolis term is `2Ωrω = 6`. -/
theorem coriolis_radial_proj_concrete (t : ℝ) :
    planeDot (-(2 * (0.5:ℝ)) • rot90 (polarVel (fun _ => 2) (fun _ => 0)
        (fun s => s) (fun _ => 3) t)) (radialUnit ((fun s => s) t))
      = 2 * (0.5:ℝ) * 2 * 3 :=
  coriolis_force_radial_proj (fun _ => 2) (fun _ => 0) (fun s => s) (fun _ => 3) 0.5 t

/-- The radial balance assembly at concrete parameters: with `r(t) = 4t²-8t+5`
(so `r(1) = 1`, `ṙ(1) = 0`, `r̈(1) = 8`), `ω = 3`, `Ω = 0.5`, `k = 1`, `m = 2`,
the constitutive balance of equation (29) yields the radial acceleration
`r̈ = 8` of equation (31), i.e. `8 = 9 + 3 - 4`. -/
theorem radial_balance_eq31_concrete
    (hbal : (2:ℝ) * (8 - (4 * 1 ^ 2 - 8 * 1 + 5) * 3 * 3)
      = 2 * (2 * 0.5 * 3 * (4 * 1 ^ 2 - 8 * 1 + 5))
        - 2 * (4 * 1 * (4 * 1 ^ 2 - 8 * 1 + 5) ^ 3)) :
    8 = coriolisRadialRHS (4 * 1 ^ 2 - 8 * 1 + 5) 3 0.5 1 := by
  have hr : HasDerivAt (fun s : ℝ => 4 * s ^ 2 - 8 * s + 5) (8 * 1 - 8) 1 := by
    have hp2 := hasDerivAt_pow 2 (1:ℝ)
    have h4 := HasDerivAt.const_mul 4 hp2
    have h8 := (hasDerivAt_id (1:ℝ)).const_mul 8
    have hc := hasDerivAt_const (c := (5:ℝ)) (1:ℝ)
    exact (HasDerivAt.add (HasDerivAt.sub h4 h8) hc).congr_deriv (by norm_num)
  have hrd : HasDerivAt (fun s : ℝ => 8 * s - 8) 8 1 :=
    (HasDerivAt.sub ((hasDerivAt_id (1:ℝ)).const_mul 8)
      (hasDerivAt_const (c := (8:ℝ)) (1:ℝ))).congr_deriv (by norm_num)
  exact radial_balance_eq31 (fun s => 4 * s ^ 2 - 8 * s + 5) (fun s => 8 * s - 8)
    (fun s => 3 * s) (fun _ => 3) 1 8 0 0.5 1 2 hr hrd
    (((hasDerivAt_id (1:ℝ)).const_mul 3).congr_deriv (by norm_num))
    (hasDerivAt_const (c := (3:ℝ)) (1:ℝ)) (by norm_num) hbal

/-- Numerically, the assembly conclusion reads `8 = 9 + 3 - 4` and the
concrete balance hypothesis holds. -/
example : 8 = coriolisRadialRHS (4 * 1 ^ 2 - 8 * 1 + 5) 3 0.5 1
    ∧ (2:ℝ) * (8 - (4 * 1 ^ 2 - 8 * 1 + 5) * 3 * 3)
      = 2 * (2 * 0.5 * 3 * (4 * 1 ^ 2 - 8 * 1 + 5))
        - 2 * (4 * 1 * (4 * 1 ^ 2 - 8 * 1 + 5) ^ 3) := by
  constructor
  · unfold coriolisRadialRHS
    norm_num
  · norm_num

/-- The strict phase equation at a constant-radius instance: with `r = 1`,
`ω = 3`, `m = 2`, `D = 4`, `u₀ = 3`, `Fθ = 1`, `Ω = 0.5`, the angular
acceleration is `1/2`, the Rayleigh factor vanishing at `ω = ω₀ = 3`. -/
theorem azimuthal_eq32_concrete
    (hbal : (2:ℝ) * (1 * (1 / 2) + 2 * 0 * (1 / 2 + 5 / 2))
      = 4 * (1 - (1 * (1 / 2 + 5 / 2)) ^ 2 / 3 ^ 2) * (1 * (1 / 2 + 5 / 2)) + 1
        - 2 * (2 * 0.5 * 0)) :
    (1 / 2 : ℝ) = 1 / (2 / 4) * (1 - (1 / 2 + 5 / 2) ^ 2 / 3 ^ 2) * (1 / 2 + 5 / 2)
      + 1 / (2 * 1) - 2 * 0 / 1 * (0.5 + (1 / 2 + 5 / 2)) := by
  have hω : HasDerivAt (fun s : ℝ => s / 2 + 5 / 2) (1 / 2) 1 := by
    have h0 := HasDerivAt.add ((hasDerivAt_id (1:ℝ)).div_const 2)
      (hasDerivAt_const (c := (5 / 2:ℝ)) (1:ℝ))
    exact h0.congr_deriv (by norm_num)
  exact azimuthal_balance_eq32_strict 2 (fun _ => 1) (fun _ => 0) (fun s => 3 * s)
    (fun s => s / 2 + 5 / 2) 1 0 (1 / 2) 4 3 1 0.5 (2 / 4) 3
    (hasDerivAt_const (c := (1:ℝ)) (1:ℝ)) (hasDerivAt_const (c := (0:ℝ)) (1:ℝ))
    (((hasDerivAt_id (1:ℝ)).const_mul 3).congr_deriv (by norm_num))
    hω (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbal

/-- The pair-sum identity at a concrete profile: the two azimuthal forces
of a pair sum to a term proportional to `sin φⱼ - sin φᵢ`. -/
theorem pair_forces_sum_concrete :
    leftAzimuthForce 1 (fun x => Real.exp (-x)) 1 1 2 (Real.pi / 2) 0
        + rightAzimuthForce 1 (fun x => Real.exp (-x)) 1 1 2 (Real.pi / 2) 0
      = (1 * (fun x => Real.exp (-x)) (1 * pairDist 1 2 (Real.pi / 2) 0)
            / pairDist 1 2 (Real.pi / 2) 0) * 2 * (Real.sin 0 - Real.sin (Real.pi / 2)) :=
  pair_azimuth_forces_sum 1 (fun x => Real.exp (-x)) 1 1 2 (Real.pi / 2) 0

/-- The two-neighbour GK phase equation at a concrete instance: with
`m = 2`, `r = 1`, `D = 4`, `u₀ = 3`, `ω₀ = 3`, `ω = 3`, GK coefficients
`(a,b) = (1,-1)`, `(a',b') = (2,1)` and phases `(φL, φi, φR) = (0, π/2, π)`. -/
theorem gk_phase_equation_pair_concrete (ωdot : ℝ)
    (hbal : (2:ℝ) * (1 * ωdot)
      = 4 * (1 - (1 * 3) ^ 2 / 3 ^ 2) * (1 * 3)
        + gkPairForce 1 (-1) (Real.pi / 2) Real.pi
        + gkPairForce 2 1 0 (Real.pi / 2)) :
    ωdot = 1 / (2 / 4) * (1 - 3 ^ 2 / 3 ^ 2) * 3
      + (gkPairForce 1 (-1) (Real.pi / 2) Real.pi
          + gkPairForce 2 1 0 (Real.pi / 2)) / (2 * 1) :=
  gk_phase_equation_pair 2 1 4 (2 / 4) 3 3 ωdot 3 1 (-1) 2 1
    (Real.pi / 2) 0 Real.pi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hbal

/-! The goal endpoints of the analytic development, and their axiom
closures. -/
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.gk_pair_potential_min_iff_of_a_pos_b_pos
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.gk_pair_potential_min_iff_of_both_neg
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.left_azimuth_force_approx_gk_force
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.left_azimuth_force_bessel_approx_gk_force
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.exists_bessel_remainder_bound
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.hasDerivAt_besselJ_zero_neg_besselJ_one
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.wave_force_not_symmetric_pair_gradient
#print axioms Qatlib.Papers.HydroSpinLatt21.GKModel.gk_phase_equation_pair
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.memory_integral_bound
#print axioms Qatlib.Papers.HydroSpinLatt21.BesselModel.tangential_balance_reduction
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.coriolisRadialRHS_at_equilibrium
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.radialPotential_min_identity
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.polar_acc_projections
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.radial_balance_eq31
#print axioms Qatlib.Papers.HydroSpinLatt21.Rotation.azimuthal_balance_eq32_strict

end QatlibTests.HydroSpinLatticeAnalyticRegression

end
