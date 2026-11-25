/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.SmallOrbit

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform small-orbit and low-memory acceleration error

[Saenz2021HydroSpinLattices], Methods equations (12)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
The Bessel history and instantaneous projection errors are respectively
linear and quadratic in orbital radius. After cancellation of the two
single-phase terms and division by the angular inertia, the angular
acceleration error is bounded by a sum linear in memory time and radius.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open scoped Real NNReal

/-- The complete normalized Bessel history has a uniform force error
linear in radius, emitter speed, and memory time. -/
theorem left_memory_error_linear_radius (F k L : ℝ) (hk : 0 < k) (hL : 0 < L) :
    ∃ C ≥ 0, ∀ r, 0 < r → r ≤ L / 4 → ∀ (φ Ω : ℝ) (θ : ℝ → ℝ),
      Differentiable ℝ θ → (∀ s, ‖deriv θ s‖ ≤ Ω) → ∀ t T : ℝ, 0 < T →
      |averageOrbitForce T (fun u => leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u))) -
        leftAzimuthForce F besselJ0Slope k r L φ (θ t)| ≤ C * r * Ω * T := by
  obtain ⟨C, hC, hb⟩ := left_bessel_force_emitter_small_orbit F k L hk hL
  refine ⟨C, hC, ?_⟩
  intro r hr hrL φ Ω θ hθ hΩ t T hT
  let f := fun ψ => leftAzimuthForce F besselJ0Slope k r L φ ψ
  let κ := fun u => f (θ (t - u))
  let Cf : ℝ≥0 := ⟨C * r, mul_nonneg hC hr.le⟩
  have hf : LipschitzWith Cf f := LipschitzWith.of_dist_le_mul fun ψ χ => by
    rw [Real.dist_eq, Real.dist_eq]
    change |f ψ - f χ| ≤ C * r * |ψ - χ|
    exact hb r hr hrL φ ψ χ
  have hκ : Continuous κ := hf.continuous.comp (hθ.continuous.comp (continuous_const.sub continuous_id))
  have hLag (u : ℝ) (hu : 0 ≤ u) : |κ u - κ 0| ≤ (C * r * Ω) * u := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hθ z) (fun z _ => hΩ z) convex_univ (Set.mem_univ t) (Set.mem_univ (t - u))
    have h' : |θ (t - u) - θ t| ≤ Ω * u := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, show t - u - t = -u by ring, abs_neg,
        abs_of_nonneg hu] at h
      exact h
    change |f (θ (t - u)) - f (θ (t - 0))| ≤ _
    rw [sub_zero, mul_assoc]
    exact (hb r hr hrL φ (θ (t - u)) (θ t)).trans
      (mul_le_mul_of_nonneg_left h' (mul_nonneg hC hr.le))
  have hEq : (fun u => leftAzimuthForce (-F) besselJ1Profile k r L φ (θ (t - u))) = κ :=
    funext fun u => (azimuth_forces_eq_besselJ1 F k r L φ (θ (t - u))).1.symm
  rw [hEq]
  simpa only [averageOrbitForce, κ, f, sub_zero] using
    memory_average_error T (C * r * Ω) hT κ hκ hLag

/-- With two identical spacings and prefactors, the opposite one-phase
contributions cancel. The history and spatial force errors have separate
uniform radius scalings. -/
theorem two_neighbor_force_error_small_orbit (F k L : ℝ) (hk : 0 < k) (hL : 0 < L) :
    ∃ C ≥ 0, ∃ B ≥ 0, ∀ r, 0 < r → r ≤ L / 4 →
      ∀ (θL θR : ℝ → ℝ) (ΩLeft ΩRight : ℝ),
      Differentiable ℝ θL → Differentiable ℝ θR →
      (∀ s, ‖deriv θL s‖ ≤ ΩLeft) → (∀ s, ‖deriv θR s‖ ≤ ΩRight) →
      ∀ φ t T : ℝ, 0 < T →
        |twoNeighborBesselForce F k r L φ t T θL θR -
          (besselGkPairForce F k r L φ (θL t) + besselGkPairForce F k r L φ (θR t))|
          ≤ C * r * (ΩLeft + ΩRight) * T + B * r ^ 2 := by
  obtain ⟨C, hC, hMem⟩ := left_memory_error_linear_radius F k L hk hL
  obtain ⟨M, hM, hMbound⟩ := exists_bridge_lipschitz_besselJ0Curv k (L / 4) L
  have hM' (z : ℝ) (hz : |z - k * L| ≤ k * L) :
      |besselJ0Curv z - besselJ0Curv (k * L)| ≤ M * |z - k * L| :=
    hMbound z (hz.trans_eq (by ring))
  let b := besselSmallOrbitCoeff F k L M
  have hb : 0 ≤ b := by unfold b besselSmallOrbitCoeff; positivity
  refine ⟨C, hC, 2 * b, by positivity, ?_⟩
  intro r hr hrL θL θR ΩL ΩR hθL hθR hΩL hΩR φ t T hT
  let bias := F * besselJ0Slope (k * L) * Real.sin φ
  let gL := besselGkPairForce F k r L φ (θL t) + bias
  let gR := besselGkPairForce F k r L φ (θR t) - bias
  let hL' := averageOrbitForce T (fun u => rightAzimuthForce (-F) besselJ1Profile k r L
    (θL (t - u)) φ)
  let hR' := averageOrbitForce T (fun u => leftAzimuthForce (-F) besselJ1Profile k r L
    φ (θR (t - u)))
  let fL := rightAzimuthForce F besselJ0Slope k r L (θL t) φ
  let fR := leftAzimuthForce F besselJ0Slope k r L φ (θR t)
  let shifted := fun s => θL s + π
  have hshift (s : ℝ) : HasDerivAt shifted (deriv θL s) s := (hθL s).hasDerivAt.add_const π
  have hMemL : |hL' - fL| ≤ C * r * ΩL * T := by
    have h := hMem r hr hrL (φ + π) ΩL shifted (fun s => (hshift s).differentiableAt)
      (fun s => by rw [(hshift s).deriv]; exact hΩL s) t T hT
    simpa only [hL', fL, rightAzimuthForce_eq_left_swap_add_pi, shifted] using h
  have hMemR : |hR' - fR| ≤ C * r * ΩR * T := hMem r hr hrL φ ΩR θR hθR hΩR t T hT
  have hForceL : |fL - gL| ≤ r ^ 2 * b := by
    have h := left_azimuth_force_quadratic_error F k r L (φ + π) (θL t + π) M
      hL hr hrL hk hM hM'
    have hturn : besselGkPairForce F k r L (φ + π) (θL t + π) =
        besselGkPairForce F k r L φ (θL t) := by
      simp only [besselGkPairForce, gkPairForce, Real.sin_add_pi, Real.cos_add_pi]
      ring
    rw [hturn, Real.sin_add_pi, mul_neg, sub_neg_eq_add] at h
    simpa only [fL, gL, bias, rightAzimuthForce_eq_left_swap_add_pi] using h
  have hForceR : |fR - gR| ≤ r ^ 2 * b :=
    left_azimuth_force_quadratic_error F k r L φ (θR t) M hL hr hrL hk hM hM'
  have heL := (abs_sub_le hL' fL gL).trans (add_le_add hMemL hForceL)
  have heR := (abs_sub_le hR' fR gR).trans (add_le_add hMemR hForceR)
  change |(hL' + hR') -
    (besselGkPairForce F k r L φ (θL t) + besselGkPairForce F k r L φ (θR t))| ≤ _
  calc
    _ = |(hL' - gL) + (hR' - gR)| := by
      congr 1
      dsimp only [gL, gR]
      ring
    _ ≤ |hL' - gL| + |hR' - gR| := abs_add_le _ _
    _ ≤ _ := add_le_add heL heR
    _ = _ := by ring

/-- At fixed spacing, wavenumber, force amplitude, and mass, the angular
acceleration residual goes to zero linearly in radius and in memory time
for uniformly bounded emitter speeds. The Rayleigh parameters stay in the
drift and obey the same exact conversion as in the tangential equation. -/
theorem gk_acceleration_error_small_orbit (F k L m : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hm : 0 < m) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∀ r, 0 < r → r ≤ L / 4 →
      ∀ (θL θR : ℝ → ℝ) (ΩL ΩR : ℝ), Differentiable ℝ θL → Differentiable ℝ θR →
      (∀ s, ‖deriv θL s‖ ≤ ΩL) → (∀ s, ‖deriv θR s‖ ≤ ΩR) →
      ∀ φ t T ω ωdot D τ u₀ ω₀ : ℝ, 0 < T → τ = m / D → ω₀ = u₀ / r →
      m * (r * ωdot) = D * (1 - (r * ω) ^ 2 / u₀ ^ 2) * (r * ω) +
        twoNeighborBesselForce F k r L φ t T θL θR →
      |ωdot - (1 / τ * (1 - ω ^ 2 / ω₀ ^ 2) * ω +
        (besselGkPairForce F k r L φ (θL t) + besselGkPairForce F k r L φ (θR t)) /
          (m * r))| ≤ A * (ΩL + ΩR) * T + B * r := by
  obtain ⟨A, hA, B, hB, hbound⟩ := two_neighbor_force_error_small_orbit F k L hk hL
  refine ⟨A / m, by positivity, B / m, by positivity, ?_⟩
  intro r hr hrL θL θR ΩL ΩR hθL hθR hΩL hΩR φ t T ω ωdot D τ u₀ ω₀ hT hτ hω₀ hbal
  have h := tangential_balance_reduction_pair m r D τ u₀ ω₀ ωdot ω
    (twoNeighborBesselForce F k r L φ t T θL θR) 0 hm.ne' hr.ne' hτ hω₀ (by simpa using hbal)
  rw [add_zero] at h
  rw [h, add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_pos (mul_pos hm hr)]
  exact (div_le_div_of_nonneg_right (hbound r hr hrL θL θR ΩL ΩR hθL hθR hΩL hΩR φ t T hT)
    (mul_pos hm hr).le).trans_eq (by field_simp [hm.ne', hr.ne'])

end Qatlib.Papers.HydroSpinLatt21.BesselModel
