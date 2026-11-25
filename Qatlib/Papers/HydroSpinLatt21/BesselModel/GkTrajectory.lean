/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselGkError

public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-time comparison of Bessel and generalized Kuramoto trajectories

[Saenz2021HydroSpinLattices], Methods equations (12)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
At every site of a homogeneous finite lattice with two neighbors, the
memory equation gives a residual in the angular acceleration. The
generalized Kuramoto vector field is Lipschitz on velocity-bounded
sets with no restriction on lifted phases. Grönwall's inequality
propagates the residual through the coupled system, for as long as both
curves stay within the given velocity bound.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open Set
open scoped NNReal

/-- Site-indexed lifted phases and angular velocities with their maximum norms. -/
abbrev AngularState (ι : Type*) := (ι → ℝ) × (ι → ℝ)

/-- Rayleigh's angular velocity drift from equation (23). -/
noncomputable def rayleighDrift (τ ω₀ w : ℝ) : ℝ :=
  1 / τ * (1 - w ^ 2 / ω₀ ^ 2) * w

/-- The finite lattice vector field, with both pair forces taken in the
receiving site's phase and divided by the angular inertia. -/
noncomputable def gkLatticeRhs {ι : Type*} (F k r L m τ ω₀ : ℝ) (left right : ι → ι)
    (q : AngularState ι) : AngularState ι :=
  (q.2, fun i => rayleighDrift τ ω₀ (q.2 i) +
    (besselGkPairForce F k r L (q.1 i) (q.1 (left i)) +
      besselGkPairForce F k r L (q.1 i) (q.1 (right i))) / (m * r))

/-- With the Rayleigh parameters fixed, the two generalized Kuramoto
coefficients scale with the angular inertia, so the vector field is
independent of the positive orbital radius. -/
theorem gk_lattice_rhs_eq_unit_radius {ι : Type*} (F k r L m τ ω₀ : ℝ)
    (left right : ι → ι) (hr : r ≠ 0) (hL : L ≠ 0) (hm : m ≠ 0) :
    gkLatticeRhs F k r L m τ ω₀ left right = gkLatticeRhs F k 1 L m τ ω₀ left right := by
  funext q
  unfold gkLatticeRhs
  congr 1
  funext i
  unfold besselGkPairForce gkPairForce
  field_simp [hr, hL, hm]

/-- Exact angular kinematics and a sitewise acceleration bound control the
full state residual in the product maximum norm. -/
theorem gk_state_residual_le {ι : Type*} [Fintype ι] (F k r L m τ ω₀ : ℝ)
    (left right : ι → ι) (q q' : AngularState ι) {ε : ℝ} (hε : 0 ≤ ε)
    (hkinematics : q'.1 = q.2)
    (hacc : ∀ i, |q'.2 i - (gkLatticeRhs F k r L m τ ω₀ left right q).2 i| ≤ ε) :
    dist q' (gkLatticeRhs F k r L m τ ω₀ left right q) ≤ ε := by
  rw [dist_eq_norm, Prod.norm_def, max_le_iff]
  constructor
  · change ‖q'.1 - q.2‖ ≤ ε
    simpa only [hkinematics, sub_self, norm_zero] using hε
  · refine (pi_norm_le_iff_of_nonneg hε).2 fun i => ?_
    change ‖q'.2 i - (gkLatticeRhs F k r L m τ ω₀ left right q).2 i‖ ≤ ε
    simpa only [Real.norm_eq_abs] using hacc i

/-- A product of a bounded trigonometric profile and a bounded profile gap
has a uniform difference bound in the two phases. -/
private theorem abs_profile_gap_sub_le (f g : ℝ → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (hfLip : ∀ x y, |f x - f y| ≤ |x - y|)
    (hgLip : ∀ x y, |g x - g y| ≤ |x - y|)
    {x x' y y' d : ℝ} (hx : |x - x'| ≤ d) (hy : |y - y'| ≤ d) :
    |f x * (g x - g y) - f x' * (g x' - g y')| ≤ 4 * d := by
  have hgap : |g x - g y| ≤ 2 := by
    calc
      |g x - g y| = |g x + -g y| := by rw [sub_eq_add_neg]
      _ ≤ |g x| + |-g y| := abs_add_le _ _
      _ ≤ 2 := by rw [abs_neg]; linarith only [hg x, hg y]
  have hgaps : |(g x - g y) - (g x' - g y')| ≤ d + d := by
    calc
      |(g x - g y) - (g x' - g y')| = |(g x - g x') + -(g y - g y')| := by
        congr 1
        ring
      _ ≤ |g x - g x'| + |-(g y - g y')| := abs_add_le _ _
      _ ≤ d + d := by
        rw [abs_neg]
        exact add_le_add ((hgLip _ _).trans hx) ((hgLip _ _).trans hy)
  have hd : 0 ≤ d := (abs_nonneg _).trans hx
  calc
    |f x * (g x - g y) - f x' * (g x' - g y')| =
        |(f x - f x') * (g x - g y) + f x' * ((g x - g y) - (g x' - g y'))| := by
      congr 1
      ring
    _ ≤ |(f x - f x') * (g x - g y)| + |f x' * ((g x - g y) - (g x' - g y'))| :=
      abs_add_le _ _
    _ ≤ d * 2 + 1 * (d + d) := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul ((hfLip _ _).trans hx) hgap (abs_nonneg _) hd)
        (mul_le_mul (hf _) hgaps (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- The signed generalized Kuramoto pair force is globally Lipschitz in the
receiving and emitting phases with the maximum of the phase differences. -/
theorem gkPairForce_abs_sub_le (α β : ℝ) {x x' y y' d : ℝ}
    (hx : |x - x'| ≤ d) (hy : |y - y'| ≤ d) :
    |gkPairForce α β x y - gkPairForce α β x' y'| ≤ 4 * (|α| + |β|) * d := by
  have hs := abs_profile_gap_sub_le Real.sin Real.cos
    Real.abs_sin_le_one Real.abs_cos_le_one
    Real.abs_sin_sub_sin_le Real.abs_cos_sub_cos_le hx hy
  have hc := abs_profile_gap_sub_le Real.cos Real.sin
    Real.abs_cos_le_one Real.abs_sin_le_one
    Real.abs_cos_sub_cos_le Real.abs_sin_sub_sin_le hx hy
  let ds := Real.sin x * (Real.cos x - Real.cos y) - Real.sin x' * (Real.cos x' - Real.cos y')
  let dc := Real.cos x * (Real.sin x - Real.sin y) - Real.cos x' * (Real.sin x' - Real.sin y')
  calc
    |gkPairForce α β x y - gkPairForce α β x' y'| = |α * ds + -(β * dc)| := by
      congr 1
      unfold gkPairForce ds dc
      ring
    _ ≤ |α * ds| + |-(β * dc)| := abs_add_le _ _
    _ ≤ |α| * (4 * d) + |β| * (4 * d) := by
      rw [abs_neg, abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
    _ = _ := by ring

/-- On a bounded velocity interval the Rayleigh drift has a uniform
Lipschitz constant, including arbitrary signs of its coefficients. -/
private theorem rayleigh_lipschitz (τ ω₀ R : ℝ) :
    ∃ K ≥ 0, ∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R,
      |rayleighDrift τ ω₀ x - rayleighDrift τ ω₀ y| ≤ K * |x - y| := by
  let f := rayleighDrift τ ω₀
  have hf : ContDiff ℝ 1 f := by
    unfold f rayleighDrift
    fun_prop
  have hcompact : IsCompact (deriv f '' Icc (-R) R) :=
    isCompact_Icc.image hf.continuous_deriv_one
  obtain ⟨K, hK, hb⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨K, hK.le, fun x hx y hy => ?_⟩
  have hd : ∀ z ∈ Icc (-R) R, ‖deriv f z‖ ≤ K :=
    fun z hz => hb _ ⟨z, hz, rfl⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => hf.differentiable (by norm_num) z) hd (convex_Icc _ _) hy hx
  simpa only [f, Real.norm_eq_abs] using h

/-- Each phase-coordinate difference is bounded by the maximum difference
over lattice phases and velocities. -/
private theorem phase_sub_le {ι : Type*} [Fintype ι] (x y : AngularState ι) (i : ι) :
    |x.1 i - y.1 i| ≤ ‖x - y‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (x.1 - y.1) i).trans (le_max_left _ _)

/-- Each angular-velocity difference is bounded by the maximum difference
over lattice phases and velocities. -/
private theorem velocity_sub_le {ι : Type*} [Fintype ι] (x y : AngularState ι) (i : ι) :
    |x.2 i - y.2 i| ≤ ‖x - y‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm (x.2 - y.2) i).trans (le_max_right _ _)

/-- A velocity bound suffices for a uniform Lipschitz bound on the finite
GK lattice field. The bound requires no restriction on the number of turns
of a phase or on the elapsed time. -/
theorem gkLatticeRhs_lipschitz {ι : Type*} [Fintype ι] (F k r L m τ ω₀ R : ℝ)
    (left right : ι → ι) :
    ∃ K : ℝ≥0, LipschitzOnWith K (gkLatticeRhs F k r L m τ ω₀ left right)
      {x | ∀ i, |x.2 i| ≤ R} := by
  obtain ⟨D, hD, hDrift⟩ := rayleigh_lipschitz τ ω₀ R
  let α := F * k * r * besselJ0Curv (k * L)
  let β := F * r / L * besselJ0Slope (k * L)
  let B := 4 * (|α| + |β|)
  let K : ℝ≥0 := ⟨1 + D + (B + B) / |m * r|, by
    have hB : 0 ≤ B := by dsimp [B]; positivity
    positivity⟩
  refine ⟨K, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm, Prod.norm_def, max_le_iff]
  let d := ‖x - y‖
  constructor
  · change ‖x.2 - y.2‖ ≤ (K : ℝ) * d
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg _))).2 fun i => ?_
    change ‖x.2 i - y.2 i‖ ≤ (K : ℝ) * d
    have hK : 1 ≤ (K : ℝ) := by
      change 1 ≤ 1 + D + (B + B) / |m * r|
      have hB : 0 ≤ B := by dsimp [B]; positivity
      linarith only [hD, show 0 ≤ (B + B) / |m * r| by positivity]
    rw [Real.norm_eq_abs]
    calc
      _ ≤ d := velocity_sub_le x y i
      _ = 1 * d := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  · refine (pi_norm_le_iff_of_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg _))).2 fun i => ?_
    let p (z : AngularState ι) (j : ι) := besselGkPairForce F k r L (z.1 i) (z.1 j)
    let u := rayleighDrift τ ω₀ (x.2 i) - rayleighDrift τ ω₀ (y.2 i)
    let v := (p x (left i) - p y (left i)) + (p x (right i) - p y (right i))
    have hu : |u| ≤ D * d :=
      (hDrift _ (abs_le.mp (hx i)) _ (abs_le.mp (hy i))).trans
        (mul_le_mul_of_nonneg_left (velocity_sub_le x y i) hD)
    have hp (j : ι) : |p x j - p y j| ≤ B * d :=
      gkPairForce_abs_sub_le α β (phase_sub_le x y i) (phase_sub_le x y j)
    have hv : |v| ≤ (B + B) * d := by
      exact (abs_add_le _ _).trans (by rw [add_mul]; exact add_le_add (hp _) (hp _))
    change ‖(rayleighDrift τ ω₀ (x.2 i) + (p x (left i) + p x (right i)) / (m * r)) -
      (rayleighDrift τ ω₀ (y.2 i) + (p y (left i) + p y (right i)) / (m * r))‖ ≤ (K : ℝ) * d
    rw [Real.norm_eq_abs]
    calc
      _ = |u + v / (m * r)| := by
        congr 1
        dsimp [u, v]
        ring
      _ ≤ |u| + |v / (m * r)| := abs_add_le _ _
      _ ≤ D * d + (B + B) * d / |m * r| := by
        rw [abs_div]
        exact add_le_add hu (div_le_div_of_nonneg_right hv (abs_nonneg _))
      _ ≤ (K : ℝ) * d := by
        change D * d + (B + B) * d / |m * r| ≤ (1 + D + (B + B) / |m * r|) * d
        calc
          _ ≤ d + (D * d + (B + B) * d / |m * r|) := le_add_of_nonneg_left (norm_nonneg _)
          _ = _ := by ring

/-- For uniformly bounded emission speeds and separated circular orbits,
any trajectories satisfying the full tangential history equation and the
generalized Kuramoto system stay within a Grönwall bound. The constants
are uniform in the trajectories, initial mismatch, and memory time.
Only the comparison interval needs the common velocity cap `R`.
The full history estimate uses the emission speed bound on the entire past. -/
theorem dist_bessel_gk_trajectories {ι : Type*} [Fintype ι]
    (left right : ι → ι) (F k r L m D τ u₀ ω₀ Ω R : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) (hm : 0 < m) (hΩ : 0 ≤ Ω)
    (hτ : τ = m / D) (hω₀ : ω₀ = u₀ / r) :
    ∃ C ≥ 0, ∃ M ≥ 0, ∃ K : ℝ≥0, ∀ (a b T δ : ℝ) (q q' g : ℝ → AngularState ι),
      0 < T →
      ContinuousOn q (Icc a b) → ContinuousOn g (Icc a b) →
      (∀ t ∈ Ico a b, HasDerivWithinAt q (q' t) (Ici t) t) →
      (∀ t ∈ Ico a b, HasDerivWithinAt g (gkLatticeRhs F k r L m τ ω₀ left right (g t))
        (Ici t) t) →
      (∀ i, Differentiable ℝ (fun t => (q t).1 i)) →
      (∀ i s, ‖deriv (fun t => (q t).1 i) s‖ ≤ Ω) →
      (∀ t ∈ Ico a b, ∀ i, |(q t).2 i| ≤ R) →
      (∀ t ∈ Ico a b, ∀ i, |(g t).2 i| ≤ R) →
      (∀ t ∈ Ico a b, (q' t).1 = (q t).2) →
      (∀ t ∈ Ico a b, ∀ i, m * (r * (q' t).2 i) =
        D * (1 - (r * (q t).2 i) ^ 2 / u₀ ^ 2) * (r * (q t).2 i) +
          twoNeighborBesselForce F k r L ((q t).1 i) t T
            (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i))) →
      dist (q a) (g a) ≤ δ →
      ∀ t ∈ Icc a b, dist (q t) (g t) ≤
        gronwallBound δ K ((C * (Ω + Ω) * T + 2 * besselForceRemainder F k r L M) / (m * r))
          (t - a) := by
  obtain ⟨C, hC, M, hM, hAcc⟩ :=
    gk_acceleration_error_of_bessel_balance F k r L m D τ u₀ ω₀ hL hr hrL hk hm hτ hω₀
  obtain ⟨K, hK⟩ := gkLatticeRhs_lipschitz F k r L m τ ω₀ R left right
  refine ⟨C, hC, M, hM, K, ?_⟩
  intro a b T δ q q' g hT hq hg hq' hg' hphase hspeed hqvel hgvel hkinematics hbalance hinit
  let ε := (C * (Ω + Ω) * T + 2 * besselForceRemainder F k r L M) / (m * r)
  let v := gkLatticeRhs F k r L m τ ω₀ left right
  have hε : 0 ≤ ε := by
    unfold ε besselForceRemainder
    positivity
  have hResidual (t : ℝ) (ht : t ∈ Ico a b) : dist (q' t) (v (q t)) ≤ ε := by
    apply gk_state_residual_le F k r L m τ ω₀ left right (q t) (q' t) hε (hkinematics t ht)
    intro i
    exact hAcc (fun s => (q s).1 (left i)) (fun s => (q s).1 (right i)) Ω Ω
      (hphase (left i)) (hphase (right i)) (hspeed (left i)) (hspeed (right i))
      ((q t).1 i) t T ((q t).2 i) ((q' t).2 i) hT (hbalance t ht i)
  have hExact (t : ℝ) (_ : t ∈ Ico a b) : dist (v (g t)) (v (g t)) ≤ 0 := by simp
  simpa only [add_zero] using
    (dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _ => v) (s := fun _ => {x | ∀ i, |x.2 i| ≤ R})
      (fun _ _ => hK) hq hq' hResidual hqvel hg hg' hExact hgvel hinit)

end Qatlib.Papers.HydroSpinLatt21.BesselModel
