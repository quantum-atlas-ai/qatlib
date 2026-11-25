/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.GkTrajectory
public import Qatlib.Papers.HydroSpinLatt21.BesselModel.SmallOrbit

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform speed bounds for the Bessel and generalized Kuramoto lattices

[Saenz2021HydroSpinLattices], Methods equations (12)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
In the homogeneous two-neighbor geometry, opposite phase biases cancel
before division by the angular inertia. The resulting angular forcing is
uniform in orbital radius, memory time, and the measurable emission
histories. Positive Rayleigh damping then gives a common invariant speed
interval for trajectories with bounded initial velocities.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open Filter MeasureTheory Set

/-- Every signed pair force is bounded independently of both lifted phases. -/
theorem abs_gk_pair_force_le (α β φ ψ : ℝ) :
    |gkPairForce α β φ ψ| ≤ 2 * (|α| + |β|) := by
  have hcos := (abs_sub _ _).trans (add_le_add (Real.abs_cos_le_one φ) (Real.abs_cos_le_one ψ))
  have hsin := (abs_sub _ _).trans (add_le_add (Real.abs_sin_le_one φ) (Real.abs_sin_le_one ψ))
  unfold gkPairForce
  calc
    _ ≤ |α * Real.sin φ * (Real.cos φ - Real.cos ψ)| +
        |β * Real.cos φ * (Real.sin φ - Real.sin ψ)| := abs_sub _ _
    _ ≤ |α| * 1 * (1 + 1) + |β| * 1 * (1 + 1) := by
      simp only [abs_mul]
      gcongr
      · exact Real.abs_sin_le_one _
      · exact Real.abs_cos_le_one _
    _ = _ := by ring

/-- The zero-radius single-phase bias is removed from each instantaneous
force with a remaining phase-independent bound proportional to radius.
The same constant bounds both orientations of the genuine pair forces. -/
theorem centered_bessel_forces_le (F k L : ℝ) (hk : 0 < k) (hL : 0 < L) :
    ∃ K ≥ 0, ∀ r, 0 < r → r ≤ L / 4 → ∀ φ ψ : ℝ,
      |leftAzimuthForce F besselJ0Slope k r L φ ψ +
          F * besselJ0Slope (k * L) * Real.sin φ| ≤ K * r ∧
      |rightAzimuthForce F besselJ0Slope k r L ψ φ -
          F * besselJ0Slope (k * L) * Real.sin φ| ≤ K * r := by
  obtain ⟨M, hM, hLip⟩ := exists_bridge_lipschitz_besselJ0Curv k (L / 4) L
  let B := besselSmallOrbitCoeff F k L M
  let K := 2 * (|F * k * besselJ0Curv (k * L)| + |F / L * besselJ0Slope (k * L)|)
  have hB : 0 ≤ B := by unfold B besselSmallOrbitCoeff; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hPair (r : ℝ) (hr : 0 < r) (φ ψ : ℝ) :
      |besselGkPairForce F k r L φ ψ| ≤ K * r := by
    unfold besselGkPairForce
    refine (abs_gk_pair_force_le _ _ _ _).trans_eq ?_
    rw [show F * k * r * besselJ0Curv (k * L) = (F * k * besselJ0Curv (k * L)) * r by ring,
        show F * r / L * besselJ0Slope (k * L) = (F / L * besselJ0Slope (k * L)) * r by ring]
    dsimp only [K]
    simp only [abs_mul, abs_of_pos hr]
    ring
  refine ⟨K + L / 4 * B, by positivity, fun r hr hrL φ ψ => ?_⟩
  have left (x y : ℝ) :
      |leftAzimuthForce F besselJ0Slope k r L x y +
          F * besselJ0Slope (k * L) * Real.sin x| ≤ (K + L / 4 * B) * r := by
    have herr := left_azimuth_force_quadratic_error F k r L x y M hL hr hrL hk hM
      (fun z hz => hLip z (hz.trans_eq (by ring)))
    let f := leftAzimuthForce F besselJ0Slope k r L x y
    let p := besselGkPairForce F k r L x y
    let bias := F * besselJ0Slope (k * L) * Real.sin x
    change |f + bias| ≤ _
    calc
      |f + bias| = |(f - (p - bias)) + p| := by congr 1; ring
      _ ≤ |f - (p - bias)| + |p| := abs_add_le _ _
      _ ≤ r ^ 2 * B + K * r := add_le_add herr (hPair r hr x y)
      _ ≤ (K + L / 4 * B) * r := by
        have h := mul_le_mul_of_nonneg_right hrL (mul_nonneg hB hr.le)
        linarith only [show r ^ 2 * B + K * r = K * r + r * (B * r) by ring,
          show (K + L / 4 * B) * r = K * r + (L / 4) * (B * r) by ring, h]
  refine ⟨left φ ψ, ?_⟩
  simpa only [rightAzimuthForce_eq_left_swap_add_pi, Real.sin_add_pi, mul_neg, ← sub_eq_add_neg]
    using left (φ + Real.pi) (ψ + Real.pi)

/-- Averaging a bounded measurable lag profile deviates from a constant
by at most the pointwise deviation bound. This uses the exact total mass
of the exponential kernel. -/
theorem abs_average_orbit_force_sub_le {T B c : ℝ} {κ : ℝ → ℝ} (hT : 0 < T)
    (hκ : Measurable κ) (hb : ∀ u, |κ u - c| ≤ B) :
    |averageOrbitForce T κ - c| ≤ B := by
  obtain ⟨hw, hi⟩ := exp_weight_Ioi T hT
  have hdiff : IntegrableOn (fun u => (κ u - c) * Real.exp (-(u / T))) (Ioi 0) := by
    refine (hw.const_mul B).mono' ((hκ.sub measurable_const).mul
      (exp_weight_cont T).measurable).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le
  have hconst : IntegrableOn (fun u => c * Real.exp (-(u / T))) (Ioi 0) := hw.const_mul c
  have hfull : IntegrableOn (fun u => κ u * Real.exp (-(u / T))) (Ioi 0) := by
    refine (hdiff.add hconst).congr (Eventually.of_forall fun u => ?_)
    change (κ u - c) * Real.exp (-(u / T)) + c * Real.exp (-(u / T)) = κ u * Real.exp (-(u / T))
    ring
  have hshift : averageOrbitForce T κ - c =
      (∫ u in Ioi (0 : ℝ), (κ u - c) * Real.exp (-(u / T))) / T := by
    unfold averageOrbitForce
    simp_rw [sub_mul]
    rw [integral_sub hfull hconst, integral_const_mul, hi, sub_div, mul_div_cancel_right₀ _ hT.ne']
  rw [hshift, abs_div, abs_of_pos hT, div_le_iff₀ hT]
  refine abs_integral_le_integral_abs.trans ?_
  have hmono := integral_mono_ae hdiff.abs (hw.const_mul B) (Eventually.of_forall fun u => by
    change |(κ u - c) * Real.exp (-(u / T))| ≤ B * Real.exp (-(u / T))
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hb u) (Real.exp_pos _).le)
  rwa [integral_const_mul, hi] at hmono

/-- The homogeneous two-neighbor Bessel history force is uniformly of
order radius, for arbitrary measurable histories and positive memory.
The opposite radius-independent phase biases cancel after averaging. -/
theorem abs_two_neighbor_bessel_force_le (F k L : ℝ) (hk : 0 < k) (hL : 0 < L) :
    ∃ K ≥ 0, ∀ r, 0 < r → r ≤ L / 4 → ∀ φ t T : ℝ, 0 < T →
      ∀ θL θR : ℝ → ℝ, Measurable θL → Measurable θR →
        |twoNeighborBesselForce F k r L φ t T θL θR| ≤ K * r := by
  obtain ⟨K, hK, hb⟩ := centered_bessel_forces_le F k L hk hL
  obtain ⟨C, hC, hLip⟩ := left_bessel_force_emitter_small_orbit F k L hk hL
  refine ⟨2 * K, by positivity, fun r hr hrL φ t T hT θL θR hθL hθR => ?_⟩
  let bias := F * besselJ0Slope (k * L) * Real.sin φ
  have hCont (x : ℝ) : Continuous (leftAzimuthForce F besselJ0Slope k r L x) :=
    (show LipschitzWith ⟨C * r, mul_nonneg hC hr.le⟩
      (leftAzimuthForce F besselJ0Slope k r L x) from
      LipschitzWith.of_dist_le_mul fun y z => by
        rw [Real.dist_eq, Real.dist_eq]
        change _ ≤ C * r * |y - z|
        exact hLip r hr hrL x y z).continuous
  let κL := fun u => rightAzimuthForce F besselJ0Slope k r L (θL (t - u)) φ
  let κR := fun u => leftAzimuthForce F besselJ0Slope k r L φ (θR (t - u))
  have hcL : Measurable κL := by
    simp only [κL, rightAzimuthForce_eq_left_swap_add_pi]
    exact (hCont _).measurable.comp ((hθL.comp (measurable_const.sub measurable_id)).add_const _)
  have hcR : Measurable κR :=
    (hCont _).measurable.comp (hθR.comp (measurable_const.sub measurable_id))
  have hLeft := abs_average_orbit_force_sub_le (B := K * r) (c := bias) hT hcL
    (fun u => (hb r hr hrL φ (θL (t - u))).2)
  have hRight := abs_average_orbit_force_sub_le (B := K * r) (c := -bias) hT hcR
    (fun u => by simpa only [sub_neg_eq_add] using (hb r hr hrL φ (θR (t - u))).1)
  simp_rw [twoNeighborBesselForce, ← (azimuth_forces_eq_besselJ1 F k r L _ _).1,
    ← (azimuth_forces_eq_besselJ1 F k r L _ _).2]
  change |averageOrbitForce T κL + averageOrbitForce T κR| ≤ _
  calc
    _ = |(averageOrbitForce T κL - bias) + (averageOrbitForce T κR - -bias)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := (add_le_add hLeft hRight).trans_eq (by ring)

/-- The generalized Kuramoto interaction acceleration has a uniform
phase-independent bound at unit radius, the radius-independent field. -/
theorem abs_gk_interaction_le (F k L m : ℝ) (hm : 0 < m) :
    ∃ K ≥ 0, ∀ φ ψ χ : ℝ,
      |(besselGkPairForce F k 1 L φ ψ + besselGkPairForce F k 1 L φ χ) / (m * 1)| ≤ K := by
  let α := F * k * 1 * besselJ0Curv (k * L)
  let β := F * 1 / L * besselJ0Slope (k * L)
  refine ⟨4 * (|α| + |β|) / m, by positivity, fun φ ψ χ => ?_⟩
  rw [abs_div, mul_one, abs_of_pos hm]
  apply div_le_div_of_nonneg_right _ hm.le
  exact (abs_add_le _ _).trans
    ((add_le_add (abs_gk_pair_force_le α β φ ψ) (abs_gk_pair_force_le α β φ χ)).trans_eq (by ring))

/-- A bounded additive acceleration preserves a symmetric speed interval
under positive Rayleigh relaxation. The interval depends on the initial
speed and forcing bounds and works for continuous time-dependent forcing
or arbitrary forcing for which the right derivative equation holds. -/
theorem exists_rayleigh_speed_bound (τ ω₀ K R₀ : ℝ) (hτ : 0 < τ) (hω : 0 < ω₀) (hK : 0 ≤ K) :
    ∃ R ≥ 0, ∀ {a b : ℝ} {v v' : ℝ → ℝ},
      ContinuousOn v (Icc a b) →
      (∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t) →
      |v a| ≤ R₀ →
      (∀ t ∈ Ico a b, |v' t - rayleighDrift τ ω₀ (v t)| ≤ K) →
      ∀ t ∈ Icc a b, |v t| ≤ R := by
  let R := max R₀ (2 * ω₀ + τ * (K + 1))
  have hRlarge : 2 * ω₀ + τ * (K + 1) ≤ R := le_max_right _ _
  have hRinit : R₀ ≤ R := le_max_left _ _
  have hRω : 2 * ω₀ ≤ R :=
    (le_add_of_nonneg_right (mul_nonneg hτ.le (by positivity))).trans hRlarge
  have hR : 0 < R := (by positivity : 0 < 2 * ω₀).trans_le hRω
  have hsq : 2 ≤ R ^ 2 / ω₀ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hω)).2
    have hh : (2 * ω₀) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hRω 2
    nlinarith only [hh, sq_nonneg ω₀]
  have hRτ : K + 1 ≤ R / τ := by
    apply (le_div_iff₀ hτ).2
    nlinarith only [hRlarge, hω]
  have hDrift : rayleighDrift τ ω₀ R < -K := by
    have h := mul_le_mul_of_nonneg_right (show 1 - R ^ 2 / ω₀ ^ 2 ≤ -1 by linarith) hR.le
    calc
      rayleighDrift τ ω₀ R = ((1 - R ^ 2 / ω₀ ^ 2) * R) / τ := by unfold rayleighDrift; ring
      _ ≤ (-1 * R) / τ := div_le_div_of_nonneg_right h hτ.le
      _ < -K := by rw [neg_one_mul, neg_div]; linarith only [hRτ]
  refine ⟨R, hR.le, fun {a b} {v v'} hv hv' ha hforce t ht => abs_le.2 ⟨?_, ?_⟩⟩
  · have hneg := image_le_of_deriv_right_lt_deriv_boundary
      (f := fun s => -v s) (f' := fun s => -v' s) (B := fun _ => R) (B' := fun _ => 0)
      hv.neg (fun s hs => (hv' s hs).neg) (by linarith only [(abs_le.mp ha).1, hRinit])
      (fun s => hasDerivAt_const s R) (fun s hs heq => by
        have hvR : v s = -R := by linarith only [heq]
        have hodd : rayleighDrift τ ω₀ (-R) = -rayleighDrift τ ω₀ R := by
          unfold rayleighDrift
          rw [neg_sq, mul_neg]
        have h := (abs_le.mp (hforce s hs)).1
        rw [hvR, hodd] at h
        linarith only [h, hDrift]) ht
    linarith only [hneg]
  · exact image_le_of_deriv_right_lt_deriv_boundary
      (B := fun _ => R) (B' := fun _ => 0) hv hv' ((abs_le.mp ha).2.trans hRinit)
      (fun s => hasDerivAt_const s R) (fun s hs heq => by
        have h := (abs_le.mp (hforce s hs)).2
        change v s = R at heq
        rw [heq] at h
        linarith only [h, hDrift]) ht

/-- Every component of the angular velocity inherits the right derivative
of the velocity component of a lattice state. -/
theorem hasDerivWithinAt_angular_velocity {ι : Type*} [Fintype ι]
    {q : ℝ → AngularState ι} {v : AngularState ι} {s : Set ℝ} {t : ℝ}
    (hq : HasDerivWithinAt q v s t) (i : ι) :
    HasDerivWithinAt (fun u => (q u).2 i) (v.2 i) s t :=
  by simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    hasDerivWithinAt_pi.mp hq.hasFDerivWithinAt.snd.hasDerivWithinAt i

/-- The speed interval bounds all existing Bessel-history and generalized
Kuramoto trajectories from the same initial speed cap. It applies to
measurable prehistories without any bound on their velocity. -/
theorem exists_bessel_gk_speed_bound {ι : Type*} [Fintype ι] (left right : ι → ι)
    (F k L m τ ω₀ R₀ : ℝ) (hk : 0 < k) (hL : 0 < L) (hm : 0 < m)
    (hτ : 0 < τ) (hω : 0 < ω₀) :
    ∃ R ≥ 0,
      (∀ {r T a b : ℝ} {q q' : ℝ → AngularState ι},
        0 < r → r ≤ L / 4 → 0 < T →
        ContinuousOn q (Icc a b) →
        (∀ t ∈ Ico a b, HasDerivWithinAt q (q' t) (Ici t) t) →
        (∀ i, Measurable (fun t => (q t).1 i)) →
        (∀ i, |(q a).2 i| ≤ R₀) →
        (∀ t ∈ Ico a b, ∀ i, (q' t).2 i = rayleighDrift τ ω₀ ((q t).2 i) +
          twoNeighborBesselForce F k r L ((q t).1 i) t T
            (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i)) / (m * r)) →
        ∀ t ∈ Icc a b, ∀ i, |(q t).2 i| ≤ R) ∧
      (∀ {a b : ℝ} {g : ℝ → AngularState ι},
        ContinuousOn g (Icc a b) →
        (∀ t ∈ Ico a b, HasDerivWithinAt g (gkLatticeRhs F k 1 L m τ ω₀ left right (g t))
          (Ici t) t) →
        (∀ i, |(g a).2 i| ≤ R₀) →
        ∀ t ∈ Icc a b, ∀ i, |(g t).2 i| ≤ R) := by
  obtain ⟨C, hC, hBessel⟩ := abs_two_neighbor_bessel_force_le F k L hk hL
  obtain ⟨B, hB, hGk⟩ := abs_gk_interaction_le F k L m hm
  let K := max (C / m) B
  obtain ⟨R, hR, hb⟩ := exists_rayleigh_speed_bound τ ω₀ K R₀ hτ hω (hB.trans (le_max_right _ _))
  refine ⟨R, hR, ?_, ?_⟩
  · intro r T a b q q' hr hrL hT hq hq' hθ hinit hacc t ht i
    refine hb (continuousOn_pi.mp hq.snd i) (fun s hs => hasDerivWithinAt_angular_velocity (hq' s hs) i)
      (hinit i) (fun s hs => ?_) t ht
    rw [hacc s hs i, add_sub_cancel_left, abs_div, abs_of_pos (mul_pos hm hr)]
    have hf := hBessel r hr hrL ((q s).1 i) s T hT _ _ (hθ (left i)) (hθ (right i))
    calc
      _ ≤ C * r / (m * r) := div_le_div_of_nonneg_right hf (mul_pos hm hr).le
      _ = C / m := by rw [mul_div_mul_right _ _ hr.ne']
      _ ≤ K := le_max_left _ _
  · intro a b g hg hg' hinit t ht i
    refine hb (continuousOn_pi.mp hg.snd i) (fun s hs => hasDerivWithinAt_angular_velocity (hg' s hs) i)
      (hinit i) (fun s hs => ?_) t ht
    simp only [gkLatticeRhs, add_sub_cancel_left]
    exact (hGk ((g s).1 i) ((g s).1 (left i)) ((g s).1 (right i))).trans (le_max_right _ _)

end Qatlib.Papers.HydroSpinLatt21.BesselModel
