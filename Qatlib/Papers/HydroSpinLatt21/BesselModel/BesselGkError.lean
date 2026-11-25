/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.BesselModel.BesselMemory

import Mathlib.Tactic.Ring

/-!
# The two-neighbor generalized Kuramoto approximation with memory

[Saenz2021HydroSpinLattices], equations (14)–(26),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
For two neighbors at the same separation and with the same force
prefactor, the opposite single-phase terms cancel. The force acting on
the center uses the derivative of each pair potential with respect to
the center's phase. The bound combines memory error and the
instantaneous force expansion before division by the angular inertia.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open MeasureTheory
open scoped Real

/-- The signed generalized Kuramoto force on the receiver with the
Bessel coefficients of equations (25) and (26). -/
noncomputable def besselGkPairForce (F k r L φ ψ : ℝ) : ℝ :=
  gkPairForce (F * k * r * besselJ0Curv (k * L))
    (F * r / L * besselJ0Slope (k * L)) φ ψ

/-- The phase-independent instantaneous force remainder for a bound
`M` on the local Lipschitz constant of `J₀''`. -/
noncomputable def besselForceRemainder (F k r L M : ℝ) : ℝ :=
  |F| * (2 * |besselJ0Slope (k * L)| * r / L
    + 2 * |besselJ0Curv (k * L)| * k * r ^ 2 / L
    + 4 * |besselJ0Curv (k * L)| * k * r ^ 2 / L * (1 + r / L)
    + 9 * M * (k * r) ^ 2 * (1 + r / L)
    + 6 * r / L * (1 + r / L) * (|besselJ0Slope (k * L)|
        + 3 * |besselJ0Curv (k * L)| * k * r
        + 9 * M * (k * r) ^ 2))

/-- A simultaneous half turn leaves a signed pair force unchanged. -/
private theorem gkPairForce_add_pi (α β φ ψ : ℝ) :
    gkPairForce α β (φ + π) (ψ + π) = gkPairForce α β φ ψ := by
  simp only [gkPairForce, Real.sin_add_pi, Real.cos_add_pi]
  ring

/-- The right receiving orbit has the same instantaneous error bound as
the left. Its single-phase contribution has the opposite sign. -/
theorem right_azimuth_force_bessel_approx_gk_force (F k r L φ ψ M : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) (hM : 0 ≤ M)
    (hlip : ∀ z, |z - k * L| ≤ 4 * k * r →
      |besselJ0Curv z - besselJ0Curv (k * L)| ≤ M * |z - k * L|) :
    |rightAzimuthForce F besselJ0Slope k r L φ ψ -
      (besselGkPairForce F k r L ψ φ + F * besselJ0Slope (k * L) * Real.sin ψ)|
      ≤ besselForceRemainder F k r L M := by
  have h := left_azimuth_force_bessel_approx_gk_force F k r L (ψ + π) (φ + π) M
    hL hr hrL hk hM hlip
  rw [gkPairForce_add_pi, Real.sin_add_pi, mul_neg, sub_neg_eq_add] at h
  rw [rightAzimuthForce_eq_left_swap_add_pi]
  exact h

/-- The exponentially weighted past of a force profile with lag as its
input, normalized by the total memory mass `T`. -/
noncomputable def averageOrbitForce (T : ℝ) (forceAtLag : ℝ → ℝ) : ℝ :=
  (∫ u in Set.Ioi (0 : ℝ), forceAtLag u * Real.exp (-(u / T))) / T

/-- Both histories exert forces on the receiver at its present phase.
The left neighbor is the emitter of the right-orbit force and conversely. -/
noncomputable def twoNeighborBesselForce (F k r L φ t T : ℝ) (θLeft θRight : ℝ → ℝ) : ℝ :=
  averageOrbitForce T (fun u => rightAzimuthForce (-F) besselJ1Profile k r L
    (θLeft (t - u)) φ)
    + averageOrbitForce T (fun u => leftAzimuthForce (-F) besselJ1Profile k r L
      φ (θRight (t - u)))

/-- The two-neighbor history force has a uniform error relative to the
two generalized Kuramoto pair forces. The left and right emission speeds
contribute separately and the receiving phase can take its value at any time. -/
theorem two_neighbor_bessel_approx_gk (F k r L : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) :
    ∃ C ≥ 0, ∃ M ≥ 0, ∀ (θLeft θRight : ℝ → ℝ) (ΩLeft ΩRight : ℝ),
      Differentiable ℝ θLeft → Differentiable ℝ θRight →
      (∀ s, ‖deriv θLeft s‖ ≤ ΩLeft) → (∀ s, ‖deriv θRight s‖ ≤ ΩRight) →
      ∀ φ t T : ℝ, 0 < T →
        |twoNeighborBesselForce F k r L φ t T θLeft θRight -
          (besselGkPairForce F k r L φ (θLeft t) + besselGkPairForce F k r L φ (θRight t))|
          ≤ C * (ΩLeft + ΩRight) * T + 2 * besselForceRemainder F k r L M := by
  obtain ⟨CL, hCL, hl⟩ := uniform_left_bessel_memory_error F k r L hL hr hrL
  obtain ⟨CR, hCR, hr'⟩ := uniform_right_bessel_memory_error F k r L hL hr hrL
  obtain ⟨M, hM, hlip⟩ := exists_bridge_lipschitz_besselJ0Curv k r L
  refine ⟨CL + CR, add_nonneg hCL hCR, M, hM, ?_⟩
  intro θL θR ΩL ΩR hθL hθR hΩL hΩR φ t T hT
  let bias := F * besselJ0Slope (k * L) * Real.sin φ
  let rL := besselGkPairForce F k r L φ (θL t) + bias
  let rR := besselGkPairForce F k r L φ (θR t) - bias
  let eL := averageOrbitForce T (fun u => rightAzimuthForce (-F) besselJ1Profile k r L
    (θL (t - u)) φ)
  let eR := averageOrbitForce T (fun u => leftAzimuthForce (-F) besselJ1Profile k r L
    φ (θR (t - u)))
  let fL := rightAzimuthForce F besselJ0Slope k r L (θL t) φ
  let fR := leftAzimuthForce F besselJ0Slope k r L φ (θR t)
  let remainder := besselForceRemainder F k r L M
  have hLagL : |eL - fL| ≤ CR * ΩL * T := (hr' φ ΩL θL hθL hΩL t T hT).2
  have hLagR : |eR - fR| ≤ CL * ΩR * T := (hl φ ΩR θR hθR hΩR t T hT).2
  have hForceL : |fL - rL| ≤ remainder :=
    right_azimuth_force_bessel_approx_gk_force F k r L (θL t) φ M hL hr hrL hk hM hlip
  have hForceR : |fR - rR| ≤ remainder :=
    left_azimuth_force_bessel_approx_gk_force F k r L φ (θR t) M hL hr hrL hk hM hlip
  have hErrL : |eL - rL| ≤ (CL + CR) * ΩL * T + remainder := by
    have hΩ : 0 ≤ ΩL := (norm_nonneg _).trans (hΩL t)
    have hcr : CR * ΩL * T ≤ (CL + CR) * ΩL * T :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) hΩ) hT.le
    exact (abs_sub_le eL fL rL).trans (add_le_add (hLagL.trans hcr) hForceL)
  have hErrR : |eR - rR| ≤ (CL + CR) * ΩR * T + remainder := by
    have hΩ : 0 ≤ ΩR := (norm_nonneg _).trans (hΩR t)
    have hcl : CL * ΩR * T ≤ (CL + CR) * ΩR * T :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCR) hΩ) hT.le
    exact (abs_sub_le eR fR rR).trans (add_le_add (hLagR.trans hcl) hForceR)
  change |(eL + eR) -
      (besselGkPairForce F k r L φ (θL t) + besselGkPairForce F k r L φ (θR t))|
    ≤ (CL + CR) * (ΩL + ΩR) * T + 2 * remainder
  calc
    _ = |(eL - rL) + (eR - rR)| := by
      congr 1
      dsimp only [rL, rR]
      ring
    _ ≤ |eL - rL| + |eR - rR| := abs_add_le _ _
    _ ≤ _ := add_le_add hErrL hErrR
    _ = _ := by ring

/-- In the two-neighbor tangential equation of a homogeneous lattice
site, replacing its history force by the instantaneous generalized
Kuramoto pair forces changes the angular acceleration by at most the
force remainder divided by the positive angular inertia `m r`. -/
theorem gk_acceleration_error_of_bessel_balance (F k r L m D τ u₀ ω₀ : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) (hm : 0 < m)
    (hτ : τ = m / D) (hω₀ : ω₀ = u₀ / r) :
    ∃ C ≥ 0, ∃ M ≥ 0, ∀ (θLeft θRight : ℝ → ℝ) (ΩLeft ΩRight : ℝ),
      Differentiable ℝ θLeft → Differentiable ℝ θRight →
      (∀ s, ‖deriv θLeft s‖ ≤ ΩLeft) → (∀ s, ‖deriv θRight s‖ ≤ ΩRight) →
      ∀ φ t T ω ωdot : ℝ, 0 < T →
      m * (r * ωdot) = D * (1 - (r * ω) ^ 2 / u₀ ^ 2) * (r * ω) +
        twoNeighborBesselForce F k r L φ t T θLeft θRight →
      |ωdot - (1 / τ * (1 - ω ^ 2 / ω₀ ^ 2) * ω +
        (besselGkPairForce F k r L φ (θLeft t) + besselGkPairForce F k r L φ (θRight t)) /
          (m * r))| ≤
        (C * (ΩLeft + ΩRight) * T + 2 * besselForceRemainder F k r L M) / (m * r) := by
  obtain ⟨C, hC, M, hM, hbound⟩ := two_neighbor_bessel_approx_gk F k r L hL hr hrL hk
  refine ⟨C, hC, M, hM, ?_⟩
  intro θL θR ΩL ΩR hθL hθR hΩL hΩR φ t T ω ωdot hT hBalance
  have h := tangential_balance_reduction_pair m r D τ u₀ ω₀ ωdot ω
    (twoNeighborBesselForce F k r L φ t T θL θR) 0 hm.ne' hr.ne' hτ hω₀ (by simpa using hBalance)
  rw [add_zero] at h
  rw [h, add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_pos (mul_pos hm hr)]
  exact div_le_div_of_nonneg_right
    (hbound θL θR ΩL ΩR hθL hθR hΩL hΩR φ t T hT) (mul_pos hm hr).le

end Qatlib.Papers.HydroSpinLatt21.BesselModel
