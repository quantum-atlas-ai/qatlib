/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.BoundedSpeed
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.SmallOrbitLimit

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The joint limit with arbitrary measurable prehistory

[Saenz2021HydroSpinLattices], Methods equations (12)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
On a separated homogeneous two-neighbor lattice, the parts of the Bessel
memory integral before and after the initial time can be controlled by
different estimates. The past before the initial time needs measurability
only. The equations supply forward speed and acceleration bounds, so an
initial layer of length proportional to the square root of the memory
time has a vanishing effect in the joint limit.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open Filter MeasureTheory Set
open scoped NNReal Topology

/-- Before the cutoff in lag, use the phase speed estimate. After the
cutoff, use the bounded range of the true centered force. This bounds
the finite-memory error even when older phases are merely measurable. -/
theorem two_neighbor_delayed_force_error (F k L : ℝ) (hk : 0 < k) (hL : 0 < L) :
    ∃ C ≥ 0, ∃ K ≥ 0, ∃ B ≥ 0, ∀ {r : ℝ}, 0 < r → r ≤ L / 4 →
      ∀ {T d S : ℝ}, 0 < T → 0 < d → 0 ≤ S → ∀ (φ t : ℝ) (θL θR : ℝ → ℝ),
        Measurable θL → Measurable θR →
        (∀ u ∈ Icc 0 d, |θL (t - u) - θL t| ≤ S * u) →
        (∀ u ∈ Icc 0 d, |θR (t - u) - θR t| ≤ S * u) →
        |twoNeighborBesselForce F k r L φ t T θL θR -
          (besselGkPairForce F k r L φ (θL t) + besselGkPairForce F k r L φ (θR t))| ≤
          2 * ((C * S + 2 * K / d) * r * T) + B * r ^ 2 := by
  obtain ⟨C, hC, hLip⟩ := left_bessel_force_emitter_small_orbit F k L hk hL
  obtain ⟨K, hK, hCenter⟩ := centered_bessel_forces_le F k L hk hL
  obtain ⟨_, _, B, hB, hInstant⟩ := two_neighbor_force_error_small_orbit F k L hk hL
  refine ⟨C, hC, K, hK, B, hB, ?_⟩
  intro r hr hrL T d S hT hd hS φ t θL θR hθL hθR hLagL hLagR
  let E := (C * S + 2 * K / d) * r * T
  have hAvg (x : ℝ) (θ : ℝ → ℝ) (hθ : Measurable θ)
      (hLag : ∀ u ∈ Icc 0 d, |θ (t - u) - θ t| ≤ S * u) :
      |averageOrbitForce T (fun u => leftAzimuthForce F besselJ0Slope k r L x (θ (t - u))) -
        leftAzimuthForce F besselJ0Slope k r L x (θ t)| ≤ E := by
    let f := leftAzimuthForce F besselJ0Slope k r L x
    let κ := fun u => f (θ (t - u))
    have hf : LipschitzWith ⟨C * r, mul_nonneg hC hr.le⟩ f :=
      LipschitzWith.of_dist_le_mul fun y z => by
        rw [Real.dist_eq, Real.dist_eq]
        change _ ≤ C * r * |y - z|
        exact hLip r hr hrL x y z
    have hκ : Measurable κ := hf.continuous.measurable.comp (hθ.comp (measurable_const.sub measurable_id))
    have hLagForce (u : ℝ) (hu : 0 ≤ u) : |κ u - κ 0| ≤ (C * S + 2 * K / d) * r * u := by
      have hδ : 0 ≤ 2 * K / d := by positivity
      change |f (θ (t - u)) - f (θ (t - 0))| ≤ _
      rw [sub_zero]
      by_cases hshort : u ≤ d
      · calc
          _ ≤ C * r * |θ (t - u) - θ t| := hLip r hr hrL x _ _
          _ ≤ C * r * (S * u) := mul_le_mul_of_nonneg_left (hLag u ⟨hu, hshort⟩) (by positivity)
          _ = C * S * (r * u) := by ring
          _ ≤ (C * S + 2 * K / d) * (r * u) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hδ) (mul_nonneg hr.le hu)
          _ = _ := by ring
      · let bias := F * besselJ0Slope (k * L) * Real.sin x
        have htail : 2 * K ≤ (2 * K / d) * u := by
          calc
            _ = (2 * K / d) * d := by field_simp [hd.ne']
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_ge hshort) hδ
        calc
          _ = |(f (θ (t - u)) + bias) - (f (θ t) + bias)| := by congr 1; ring
          _ ≤ _ := abs_sub _ _
          _ ≤ K * r + K * r := add_le_add (hCenter r hr hrL x _).1 (hCenter r hr hrL x _).1
          _ = (2 * K) * r := by ring
          _ ≤ ((2 * K / d) * u) * r := mul_le_mul_of_nonneg_right htail hr.le
          _ = (2 * K / d) * (r * u) := by ring
          _ ≤ (C * S + 2 * K / d) * (r * u) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hC hS)) (mul_nonneg hr.le hu)
          _ = _ := by ring
    simpa only [averageOrbitForce, E, κ, f, sub_zero] using
      memory_average_error_of_measurable T _ hT κ hκ hLagForce
  let κL := fun u => rightAzimuthForce F besselJ0Slope k r L (θL (t - u)) φ
  let κR := fun u => leftAzimuthForce F besselJ0Slope k r L φ (θR (t - u))
  let fL := rightAzimuthForce F besselJ0Slope k r L (θL t) φ
  let fR := leftAzimuthForce F besselJ0Slope k r L φ (θR t)
  let gL := besselGkPairForce F k r L φ (θL t)
  let gR := besselGkPairForce F k r L φ (θR t)
  have hMemL : |averageOrbitForce T κL - fL| ≤ E := by
    simpa only [κL, fL, rightAzimuthForce_eq_left_swap_add_pi] using
      hAvg (φ + Real.pi) (fun s => θL s + Real.pi) (hθL.add_const _)
        (fun u hu => by simpa only [add_sub_add_right_eq_sub] using hLagL u hu)
  have hMemR : |averageOrbitForce T κR - fR| ≤ E := hAvg φ θR hθR hLagR
  have hConst (c : ℝ) : averageOrbitForce T (fun _ => c) = c := by
    unfold averageOrbitForce
    rw [integral_const_mul, (exp_weight_Ioi T hT).2, mul_div_cancel_right₀ _ hT.ne']
  have hSpatial : |(fL + fR) - (gL + gR)| ≤ B * r ^ 2 := by
    have hi := hInstant r hr hrL (fun _ => θL t) (fun _ => θR t) 0 0
      (differentiable_const _) (differentiable_const _) (fun _ => by simp) (fun _ => by simp) φ t T hT
    simp only [add_zero, mul_zero, zero_mul, zero_add, twoNeighborBesselForce, hConst,
      ← (azimuth_forces_eq_besselJ1 F k r L _ _).1, ← (azimuth_forces_eq_besselJ1 F k r L _ _).2] at hi
    exact hi
  simp_rw [twoNeighborBesselForce, ← (azimuth_forces_eq_besselJ1 F k r L _ _).1,
    ← (azimuth_forces_eq_besselJ1 F k r L _ _).2]
  change |(averageOrbitForce T κL + averageOrbitForce T κR) - (gL + gR)| ≤ 2 * E + B * r ^ 2
  calc
    _ = |((averageOrbitForce T κL - fL) + (averageOrbitForce T κR - fR)) +
        ((fL + fR) - (gL + gR))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (E + E) + B * r ^ 2 := add_le_add ((abs_add_le _ _).trans (add_le_add hMemL hMemR)) hSpatial
    _ = _ := by ring

/-- A trajectory of the angular equation with the genuine two-neighbor
Bessel history force and measurable phases on the whole emission axis. -/
structure BesselTrajectoryOn {ι : Type*} [Fintype ι] (F k r L m τ ω₀ T a b : ℝ)
    (left right : ι → ι) (q q' : ℝ → AngularState ι) : Prop where
  continuousOn : ContinuousOn q (Icc a b)
  hasDeriv : ∀ t ∈ Ico a b, HasDerivWithinAt q (q' t) (Ici t) t
  measurablePhase : ∀ i, Measurable (fun t => (q t).1 i)
  kinematics : ∀ t ∈ Ico a b, (q' t).1 = (q t).2
  acceleration : ∀ t ∈ Ico a b, ∀ i, (q' t).2 i = rayleighDrift τ ω₀ ((q t).2 i) +
    twoNeighborBesselForce F k r L ((q t).1 i) t T
      (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i)) / (m * r)

/-- The tangential Bessel balance gives the angular equation after the
source scalings of relaxation time and free orbital speed. -/
theorem besselTrajectoryOn_of_tangential_balance {ι : Type*} [Fintype ι]
    {F k r L m D τ ω₀ T a b : ℝ} {left right : ι → ι} {q q' : ℝ → AngularState ι}
    (hr : r ≠ 0) (hm : m ≠ 0) (hτ : τ = m / D)
    (hq : ContinuousOn q (Icc a b))
    (hq' : ∀ t ∈ Ico a b, HasDerivWithinAt q (q' t) (Ici t) t)
    (hPhase : ∀ i, Measurable (fun t => (q t).1 i))
    (hKin : ∀ t ∈ Ico a b, (q' t).1 = (q t).2)
    (hBalance : ∀ t ∈ Ico a b, ∀ i, m * (r * (q' t).2 i) =
      D * (1 - (r * (q t).2 i) ^ 2 / (r * ω₀) ^ 2) * (r * (q t).2 i) +
      twoNeighborBesselForce F k r L ((q t).1 i) t T
        (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i))) :
    BesselTrajectoryOn F k r L m τ ω₀ T a b left right q q' := by
  refine ⟨hq, hq', hPhase, hKin, fun t ht i => ?_⟩
  have hω : ω₀ = (r * ω₀) / r := by rw [mul_comm, mul_div_cancel_right₀ _ hr]
  simpa only [add_zero, rayleighDrift] using tangential_balance_reduction_pair m r D τ
    (r * ω₀) ω₀ ((q' t).2 i) ((q t).2 i)
    (twoNeighborBesselForce F k r L ((q t).1 i) t T
      (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i))) 0 hm hr hτ hω
    (by simpa only [add_zero] using hBalance t ht i)

/-- The forward phase difference is controlled by its angular velocity
on the interval between the two observations. -/
private theorem phase_sub_le_of_speed_bound {ι : Type*} [Fintype ι] {q q' : ℝ → AngularState ι}
    {a b R : ℝ} (hq : ContinuousOn q (Icc a b))
    (hq' : ∀ t ∈ Ico a b, HasDerivWithinAt q (q' t) (Ici t) t)
    (hkin : ∀ t ∈ Ico a b, (q' t).1 = (q t).2)
    (hvel : ∀ t ∈ Icc a b, ∀ i, |(q t).2 i| ≤ R)
    (i : ι) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    |(q s).1 i - (q t).1 i| ≤ R * (t - s) := by
  have hsubset : Icc s t ⊆ Icc a b := Icc_subset_Icc hs ht
  have hsub' : Ico s t ⊆ Ico a b := Ico_subset_Ico hs ht
  have hderiv (u : ℝ) (hu : u ∈ Ico s t) :
      HasDerivWithinAt (fun v => (q v).1 i) ((q u).2 i) (Ici u) u := by
    rw [← hkin u (hsub' hu)]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hasDerivWithinAt_pi.mp (hq' u (hsub' hu)).hasFDerivWithinAt.fst.hasDerivWithinAt i
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    ((continuousOn_pi.mp hq.fst i).mono hsubset) hderiv
    (fun u hu => by rw [Real.norm_eq_abs]; exact hvel u (hsubset (Ico_subset_Icc_self hu)) i)
    t ⟨hst, le_rfl⟩
  simpa only [Real.norm_eq_abs, abs_sub_comm] using h

/-- A common initial speed cap gives a uniform trajectory comparison with
no differentiated prehistory. The effect of the initial memory layer is
controlled by a multiple of `√T`, in addition to the residual proportional
to `T` and `r`. The Grönwall constants do not depend on either small scale. -/
theorem dist_small_orbit_of_measurable_history {ι : Type*} [Fintype ι]
    (left right : ι → ι) (F k L m τ ω₀ R₀ : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hm : 0 < m) (hτ : 0 < τ) (hω : 0 < ω₀) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∃ C ≥ 0, ∃ M ≥ 0, ∃ K : ℝ≥0,
      ∀ {r T a b : ℝ} {q q' g : ℝ → AngularState ι},
      0 < r → r ≤ L / 4 → 0 < T →
      BesselTrajectoryOn F k r L m τ ω₀ T a b left right q q' →
      ContinuousOn g (Icc a b) →
      (∀ t ∈ Ico a b, HasDerivWithinAt g (gkLatticeRhs F k 1 L m τ ω₀ left right (g t))
        (Ici t) t) →
      (∀ i, |(q a).2 i| ≤ R₀) → (∀ i, |(g a).2 i| ≤ R₀) →
      ∀ t ∈ Icc a b, dist (q t) (g t) ≤
        gronwallBound (dist (q a) (g a) + 2 * M * Real.sqrt T) K
          (A * T + C * Real.sqrt T + B * r) (b - a) := by
  obtain ⟨R, hR, hqSpeed, hgSpeed⟩ := exists_bessel_gk_speed_bound left right F k L m τ ω₀ R₀ hk hL hm hτ hω
  obtain ⟨D, hD, hBessel⟩ := abs_two_neighbor_bessel_force_le F k L hk hL
  obtain ⟨E, _, hGK⟩ := abs_gk_interaction_le F k L m hm
  obtain ⟨A, hA, C, hC, B, hB, hForce⟩ := two_neighbor_delayed_force_error F k L hk hL
  obtain ⟨K, hLip⟩ := gkLatticeRhs_lipschitz F k 1 L m τ ω₀ R left right
  let v := gkLatticeRhs F k 1 L m τ ω₀ left right
  have hDrift : Continuous (rayleighDrift τ ω₀) := by unfold rayleighDrift; fun_prop
  obtain ⟨N, hN, hn⟩ := (isCompact_Icc.image hDrift).isBounded.exists_pos_norm_le
  have hN' (x : ℝ) (hx : |x| ≤ R) : |rayleighDrift τ ω₀ x| ≤ N := by
    rw [← Real.norm_eq_abs]
    exact hn _ ⟨x, abs_le.mp hx, rfl⟩
  let M := max R (N + max (D / m) E)
  have hM : 0 ≤ M := hR.trans (le_max_left _ _)
  refine ⟨2 * A * R / m, by positivity, B / m, by positivity, 4 * C / m, by positivity, M, hM, K, ?_⟩
  intro r T a b q q' g hr hrL hT hq hg hg' hqInit hgInit t ht
  let d := Real.sqrt T
  let a' := a + d
  let δ := dist (q a) (g a) + 2 * M * d
  let ε := (2 * A * R / m) * T + (4 * C / m) * d + (B / m) * r
  have hd : 0 < d := Real.sqrt_pos.2 hT
  have hdT : d ^ 2 = T := Real.sq_sqrt hT.le
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have ha' : a ≤ a' := le_add_of_nonneg_right hd.le
  have hqR := hqSpeed hr hrL hT hq.continuousOn hq.hasDeriv hq.measurablePhase hqInit hq.acceleration
  have hgR := hgSpeed hg hg' hgInit
  have hNorm (z z' : AngularState ι) (hz : ∀ i, |z.2 i| ≤ R) (hKin : z'.1 = z.2)
      (hAcc : ∀ i, |z'.2 i| ≤ N + max (D / m) E) : ‖z'‖ ≤ M := by
    rw [Prod.norm_def, max_le_iff, hKin]
    exact ⟨(pi_norm_le_iff_of_nonneg hM).2 (fun i => (Real.norm_eq_abs _ ▸ hz i).trans
        (le_max_left _ _)),
      (pi_norm_le_iff_of_nonneg hM).2 (fun i => (Real.norm_eq_abs _ ▸ hAcc i).trans
        (le_max_right _ _))⟩
  have hqNorm (s : ℝ) (hs : s ∈ Ico a b) : ‖q' s‖ ≤ M := by
    refine hNorm (q s) (q' s) (hqR s (Ico_subset_Icc_self hs)) (hq.kinematics s hs) (fun i => ?_)
    rw [hq.acceleration s hs i]
    have hf := hBessel r hr hrL ((q s).1 i) s T hT _ _
      (hq.measurablePhase (left i)) (hq.measurablePhase (right i))
    have hf' : |twoNeighborBesselForce F k r L ((q s).1 i) s T
        (fun u => (q u).1 (left i)) (fun u => (q u).1 (right i)) / (m * r)| ≤ D / m := by
      rw [abs_div, abs_of_pos (mul_pos hm hr)]
      exact (div_le_div_of_nonneg_right hf (mul_pos hm hr).le).trans_eq
        (mul_div_mul_right _ _ hr.ne')
    exact (abs_add_le _ _).trans
      (add_le_add (hN' _ (hqR s (Ico_subset_Icc_self hs) i)) (hf'.trans (le_max_left _ _)))
  have hgNorm (s : ℝ) (hs : s ∈ Ico a b) : ‖v (g s)‖ ≤ M := by
    refine hNorm (g s) (v (g s)) (hgR s (Ico_subset_Icc_self hs)) rfl (fun i => ?_)
    exact (abs_add_le _ _).trans (add_le_add (hN' _ (hgR s (Ico_subset_Icc_self hs) i))
      ((hGK ((g s).1 i) ((g s).1 (left i)) ((g s).1 (right i))).trans (le_max_right _ _)))
  have hb₀ (s : ℝ) (hs : s ∈ Icc a b) (hsa : s ≤ a') : dist (q s) (g s) ≤ δ := by
    have hqD := norm_image_sub_le_of_norm_deriv_right_le_segment hq.continuousOn hq.hasDeriv hqNorm s hs
    have hgD := norm_image_sub_le_of_norm_deriv_right_le_segment hg hg' hgNorm s hs
    have htime : s - a ≤ d := by linarith only [show s ≤ a + d from hsa]
    have hqD' : dist (q s) (q a) ≤ M * d := by
      rw [dist_eq_norm]
      exact hqD.trans (mul_le_mul_of_nonneg_left htime hM)
    have hgD' : dist (g a) (g s) ≤ M * d := by
      rw [dist_comm, dist_eq_norm]
      exact hgD.trans (mul_le_mul_of_nonneg_left htime hM)
    calc
      _ ≤ dist (q s) (q a) + dist (q a) (g s) := dist_triangle _ _ _
      _ ≤ dist (q s) (q a) + (dist (q a) (g a) + dist (g a) (g s)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ ≤ δ := (add_le_add hqD' (add_le_add le_rfl hgD')).trans_eq (by dsimp [δ]; ring)
  by_cases ht₀ : t ≤ a'
  · refine (hb₀ t ht ht₀).trans ?_
    have h := gronwallBound_mono hδ hε K.coe_nonneg (show (0 : ℝ) ≤ b - a from sub_nonneg.mpr (ht.1.trans ht.2))
    simpa only [gronwallBound_x0] using h
  · have ht' : t ∈ Icc a' b := ⟨le_of_not_ge ht₀, ht.2⟩
    have hsubset : Icc a' b ⊆ Icc a b := Icc_subset_Icc_left ha'
    have hsub' : Ico a' b ⊆ Ico a b := Ico_subset_Ico_left ha'
    have hRadius := gk_lattice_rhs_eq_unit_radius F k r L m τ ω₀ left right hr.ne' hL.ne' hm.ne'
    have hResidual (s : ℝ) (hs : s ∈ Ico a' b) : dist (q' s) (v (q s)) ≤ ε := by
      change dist (q' s) (gkLatticeRhs F k 1 L m τ ω₀ left right (q s)) ≤ ε
      rw [← hRadius]
      apply gk_state_residual_le F k r L m τ ω₀ left right (q s) (q' s) hε (hq.kinematics s (hsub' hs))
      intro i
      have hPhase (j : ι) (u : ℝ) (hu : u ∈ Icc 0 d) :
          |(q (s - u)).1 j - (q s).1 j| ≤ R * u := by
        have hau : a ≤ s - u := by linarith only [show a + d ≤ s from hs.1, hu.2]
        have h := phase_sub_le_of_speed_bound hq.continuousOn hq.hasDeriv hq.kinematics hqR j
          hau (sub_le_self s hu.1) hs.2.le
        rwa [show s - (s - u) = u by ring] at h
      have hf := hForce hr hrL hT hd hR ((q s).1 i) s
        (fun u => (q u).1 (left i)) (fun u => (q u).1 (right i))
        (hq.measurablePhase (left i)) (hq.measurablePhase (right i)) (hPhase _) (hPhase _)
      rw [hq.acceleration s (hsub' hs) i]
      simp only [gkLatticeRhs, add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_pos (mul_pos hm hr)]
      refine (div_le_div_of_nonneg_right hf (mul_pos hm hr).le).trans_eq ?_
      dsimp only [ε]
      field_simp [hm.ne', hd.ne', hr.ne']
      rw [← hdT]
      ring
    have hExact (s : ℝ) (_ : s ∈ Ico a' b) : dist (v (g s)) (v (g s)) ≤ 0 := by simp
    have hBound :=
      dist_le_of_approx_trajectories_ODE_of_mem
        (v := fun _ => v) (s := fun _ => {x | ∀ i, |x.2 i| ≤ R})
        (fun _ _ => hLip) (hq.continuousOn.mono hsubset) (fun s hs => hq.hasDeriv s (hsub' hs))
        hResidual (fun s hs => hqR s (hsubset (Ico_subset_Icc_self hs)))
        (hg.mono hsubset) (fun s hs => hg' s (hsub' hs)) hExact
        (fun s hs => hgR s (hsubset (Ico_subset_Icc_self hs)))
        (hb₀ a' ⟨ha', ht'.1.trans ht'.2⟩ le_rfl) t ht'
    have hElapsed : t - a' ≤ b - a := sub_le_sub ht.2 ha'
    have hFinal : dist (q t) (g t) ≤ gronwallBound δ K ε (t - a') := by
      simpa only [add_zero] using hBound
    exact hFinal.trans (gronwallBound_mono hδ hε K.coe_nonneg hElapsed)

/-- The joint limit holds from convergent initial data, with no common
bound assumed on comparison velocities, no derivative bound on emissions
before the initial time, and no relation between the two vanishing scales.
The trajectories themselves are supplied as solutions on the comparison
interval. -/
theorem tendsto_uniformly_on_small_orbit_of_measurable_history {ι γ : Type*} [Fintype ι] {p : Filter γ}
    (left right : ι → ι) (F k L m τ ω₀ a b : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hm : 0 < m) (hτ : 0 < τ) (hω : 0 < ω₀)
    (r T : γ → ℝ) (q q' : γ → ℝ → AngularState ι) (g : ℝ → AngularState ι)
    (hr : Tendsto r p (𝓝 0)) (hT : Tendsto T p (𝓝 0))
    (hinit : Tendsto (fun n => dist (q n a) (g a)) p (𝓝 0))
    (hFamily : ∀ᶠ n in p, 0 < r n ∧ r n ≤ L / 4 ∧ 0 < T n ∧
      BesselTrajectoryOn F k (r n) L m τ ω₀ (T n) a b left right (q n) (q' n))
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (gkLatticeRhs F k 1 L m τ ω₀ left right (g t))
      (Ici t) t) :
    TendstoUniformlyOn q g p (Icc a b) := by
  let R₀ := ‖(g a).2‖ + 1
  obtain ⟨A, _, B, _, C, _, M, _, K, hBound⟩ :=
    dist_small_orbit_of_measurable_history left right F k L m τ ω₀ R₀ hk hL hm hτ hω
  have hgInit (i : ι) : |(g a).2 i| ≤ R₀ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ i).trans (le_add_of_nonneg_right zero_le_one)
  have hqInit (n : γ) (hh : dist (q n a) (g a) < 1) (i : ι) : |(q n a).2 i| ≤ R₀ := by
    rw [← Real.norm_eq_abs]
    have h := norm_le_pi_norm ((q n a).2 - (g a).2) i
    have hdiff : ‖(q n a).2 i - (g a).2 i‖ ≤ dist (q n a) (g a) := by
      rw [dist_eq_norm, Prod.norm_def]
      exact h.trans (le_max_right _ _)
    calc
      _ = ‖((q n a).2 i - (g a).2 i) + (g a).2 i‖ := by rw [sub_add_cancel]
      _ ≤ ‖(q n a).2 i - (g a).2 i‖ + ‖(g a).2 i‖ := norm_add_le _ _
      _ ≤ R₀ := (add_le_add (hdiff.trans hh.le) (norm_le_pi_norm _ i)).trans_eq (add_comm _ _)
  have hRoot : Tendsto (fun n => Real.sqrt (T n)) p (𝓝 0) := by simpa only [Real.sqrt_zero] using hT.sqrt
  have hInitial : Tendsto (fun n => dist (q n a) (g a) + 2 * M * Real.sqrt (T n)) p (𝓝 0) := by
    simpa using hinit.add (hRoot.const_mul (2 * M))
  have hResidual : Tendsto (fun n => A * T n + C * Real.sqrt (T n) + B * r n) p (𝓝 0) := by
    simpa using ((hT.const_mul A).add (hRoot.const_mul C)).add (hr.const_mul B)
  have hLimit := tendsto_gronwall_zero (K : ℝ) (b - a) hInitial hResidual
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hFamily, (tendsto_order.1 hinit).2 1 zero_lt_one,
    (tendsto_order.1 hLimit).2 η hη] with n hn hnear herr t ht
  obtain ⟨hrn, hsep, hTn, hqn⟩ := hn
  rw [dist_comm]
  exact (hBound hrn hsep hTn hqn hg hg' (hqInit n hnear) hgInit t ht).trans_lt herr

end Qatlib.Papers.HydroSpinLatt21.BesselModel
