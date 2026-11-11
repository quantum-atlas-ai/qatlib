/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WaveEquation17.MainResults.PerturbationCore
import Qatlib.Papers.WaveEquation17.MainResults.SpectralGap

set_option backward.isDefEq.respectTransparency false

/-!
# WaveEquation17.MainResults.LaplacianPerturbation

Fixed arXiv:1711.05394v4, Theorem 3, equations (82)--(88).

Theorem 3 specialises Theorem 2 to the perturbation `-λ²(∇²)²`.  Writing `Lap` for the
Laplacian, the source uses two additional facts:

* equation (85), obtained from Theorem 1 applied to `ψ = Div⁻¹ φ̇`:
  `∑ⱼ ‖ψⱼ(0)‖² ≤ (ℓ/π)² ‖φ̇(0)‖²`;
* equation (88), `∇² ψ(0) = 0`.

Together they replace the two factors in (57) by `‖∇²φ(0)‖` and
`‖φ(0)‖² + (ℓ/π)²‖φ̇(0)‖²`, yielding (83).  The finite-dimensional statement below
uses a contraction `P` to read off the `φ` component, exactly as equation (81) reads
(80) as an estimate for `φε - φ0`.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate

namespace Qatlib.Papers.WaveEquation17.MainResults

/-- Theorem 3 of the source, equation (83): for the Laplacian perturbation the
perturbation error is bounded by the initial Laplacian and the initial data,
`‖φε(t) - φ0(t)‖ ≤ √(2tε‖∇²φ(0)‖) (‖φ(0)‖² + (ℓ²/π²)‖φ̇(0)‖²)^{1/4}`.

The assumptions `hdecomp` and `horth` express the block decomposition
`S(0) = (φ, ψ)` with the `φ` block orthogonal to the `ψ` block; `hLapψ` is (88).
The estimate (85) is not assumed: it is derived from Theorem 1 applied to
`div ψ = φ̇`, with `ψ` having no divergenceless component.  The final factor is
written as `√√(‖φ(0)‖² + (ℓ/π)²‖φ̇(0)‖²)`, the fourth root appearing in (83). -/
theorem theorem3_laplacian_perturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (H0 Lap P div : E →L[ℂ] E)
    (hH0 : IsSelfAdjointCLM H0) (hLap : IsSelfAdjointCLM Lap)
    (hcomm : ∀ x : E, H0 (Lap x) = Lap (H0 x))
    (hP : ‖P‖ ≤ 1)
    {Sε S0 : ℝ → E} {ε t ℓ : ℝ} (φ ψ φdot : E)
    (hSε : ∀ τ, HasDerivAt Sε
      (-(Complex.I) • (H0 (Sε τ) + (ε : ℂ) • Lap (Sε τ))) τ)
    (hS0 : ∀ τ, HasDerivAt S0 (-(Complex.I) • (H0 (S0 τ))) τ)
    (hinit : Sε 0 = S0 0)
    (hdecomp : S0 0 = φ + ψ)
    (horth : inner ℂ φ ψ = 0)
    (hLapψ : Lap ψ = 0)
    (hgap : ∀ v : E, v ∈ (LinearMap.ker div.toLinearMap)ᗮ →
      (Real.pi / ℓ) ^ 2 * ‖v‖ ^ 2 ≤ ‖div v‖ ^ 2)
    (hdivψ : div ψ = φdot)
    (hψorth : ψ ∈ (LinearMap.ker div.toLinearMap)ᗮ)
    (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ‖P (Sε t) - P (S0 t)‖ ≤
      Real.sqrt (2 * t * ε * ‖Lap φ‖) *
        Real.sqrt (Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2)) := by
  have hpsi : ‖ψ‖ ≤ (ℓ / Real.pi) * ‖φdot‖ := by
    have h := theorem1_divergence_bound div ℓ hℓ hgap ψ hψorth
    rwa [hdivψ] at h
  have hmain := theorem2_wave_perturbation hH0 hLap hcomm hSε hS0 hinit hε ht
  have hproj : ‖P (Sε t) - P (S0 t)‖ ≤ ‖Sε t - S0 t‖ := by
    rw [← map_sub]
    calc
      ‖P (Sε t - S0 t)‖ ≤ ‖P‖ * ‖Sε t - S0 t‖ := P.le_opNorm _
      _ ≤ 1 * ‖Sε t - S0 t‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ = ‖Sε t - S0 t‖ := one_mul _
  have hnorm_phi_psi : ‖S0 0‖ ^ 2 = ‖φ‖ ^ 2 + ‖ψ‖ ^ 2 := by
    rw [hdecomp, norm_add_sq (𝕜 := ℂ)]
    have hzero : RCLike.re (inner ℂ φ ψ) = 0 := by rw [horth]; simp
    rw [hzero]
    ring
  have hpsi_sq : ‖ψ‖ ^ 2 ≤ (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2 := by
    have hnonneg : 0 ≤ (ℓ / Real.pi) * ‖φdot‖ :=
      mul_nonneg (div_nonneg hℓ.le Real.pi_pos.le) (norm_nonneg _)
    nlinarith [hpsi, norm_nonneg ψ, hnonneg]
  have hS0_sq : ‖S0 0‖ ^ 2 ≤ ‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2 := by
    rw [hnorm_phi_psi]
    linarith
  have hS0_le : ‖S0 0‖ ≤
      Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) := by
    have h := Real.sqrt_le_sqrt hS0_sq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hLap_S0 : ‖Lap (S0 0)‖ = ‖Lap φ‖ := by
    rw [hdecomp, map_add, hLapψ, add_zero]
  have hmain' : ‖Sε t - S0 t‖ ≤
      Real.sqrt (2 * t * ε * ‖S0 0‖ * ‖Lap φ‖) := by
    simpa [hinit, hLap_S0] using hmain
  have hstep : Real.sqrt (2 * t * ε * ‖S0 0‖ * ‖Lap φ‖) ≤
      Real.sqrt (2 * t * ε *
        Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) * ‖Lap φ‖) := by
    apply Real.sqrt_le_sqrt
    have hcoef : 0 ≤ 2 * t * ε := by positivity
    have h1 : 2 * t * ε * ‖S0 0‖ ≤
        2 * t * ε * Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hS0_le hcoef
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hEq : Real.sqrt (2 * t * ε *
        Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) * ‖Lap φ‖) =
      Real.sqrt (2 * t * ε * ‖Lap φ‖) *
        Real.sqrt (Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2)) := by
    rw [show 2 * t * ε *
        Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) * ‖Lap φ‖ =
        (2 * t * ε * ‖Lap φ‖) *
          Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) by ring]
    rw [Real.sqrt_mul (by positivity)]
  calc
    ‖P (Sε t) - P (S0 t)‖ ≤ ‖Sε t - S0 t‖ := hproj
    _ ≤ Real.sqrt (2 * t * ε * ‖S0 0‖ * ‖Lap φ‖) := hmain'
    _ ≤ Real.sqrt (2 * t * ε *
        Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2) * ‖Lap φ‖) := hstep
    _ = Real.sqrt (2 * t * ε * ‖Lap φ‖) *
        Real.sqrt (Real.sqrt (‖φ‖ ^ 2 + (ℓ / Real.pi) ^ 2 * ‖φdot‖ ^ 2)) := hEq

end Qatlib.Papers.WaveEquation17.MainResults
