/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWalkDiff01.MainResults.SpectralAmp

@[expose] public section

/-!
# The time-averaged probability of reaching the opposite root

For nonzero coupling, every eigenspace of the tridiagonal column
Hamiltonian has dimension one. The spectral transition formula can
therefore be averaged with distinct energies, and the endpoint parity
bound gives the lower estimate of Section IV.
-/

set_option autoImplicit false

noncomputable section

open Matrix Filter
open scoped InnerProductSpace Topology
open Qatlib.Papers.QWalkDiff01.MainResults

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- Distinct basis vectors have distinct eigenvalues for the irreducible
tridiagonal Hamiltonian at nonzero coupling. -/
theorem reduced_spectrum_injective (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    Function.Injective (reducedHamiltonian_isHermitian n γ).eigenvalues := by
  let h := reducedHamiltonian_isHermitian n γ
  let B := h.eigenvectorBasis
  intro r s heq
  by_contra hrs
  have hs := h.mulVec_eigenvectorBasis s
  rw [← heq] at hs
  obtain ⟨c, hc⟩ := eigenspace_subsingleton hγ (h.mulVec_eigenvectorBasis r)
    hs (basis_ne_zero n γ r)
  have hvec : B s = c • B r := by
    have he := congrArg (WithLp.toLp 2) hc
    simpa [B] using he
  have horth : ⟪B r, B s⟫_ℝ = 0 := B.orthonormal.2 hrs
  have hself : ⟪B r, B r⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, B.orthonormal.1, one_pow]
  rw [hvec, inner_smul_right, hself, mul_one] at horth
  rw [horth, zero_smul] at hc
  exact basis_ne_zero n γ s hc

/-- The time average of the actual root-to-root probability approaches
a limit at least the reciprocal of the number of columns. -/
theorem endpoint_time_average_ge (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    let a := EuclideanSpace.single (leftRoot n) (1 : ℝ)
    let c := EuclideanSpace.single (rightRoot n) (1 : ℝ)
    let B := (reducedHamiltonian_isHermitian n γ).eigenvectorBasis
    Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
        ‖(quantumPropagator n γ t *ᵥ (fun j => (a j : ℂ))) (rightRoot n)‖ ^ 2)
      atTop (𝓝 (limitingDistribution B a c)) ∧
      1 / ((2 * n + 1 : ℕ) : ℝ) ≤ limitingDistribution B a c := by
  let a := EuclideanSpace.single (leftRoot n) (1 : ℝ)
  let c := EuclideanSpace.single (rightRoot n) (1 : ℝ)
  let h := reducedHamiltonian_isHermitian n γ
  let B := h.eigenvectorBasis
  change Tendsto
    (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
      ‖(quantumPropagator n γ t *ᵥ (fun j => (a j : ℂ))) (rightRoot n)‖ ^ 2)
    atTop (𝓝 (limitingDistribution B a c)) ∧
    1 / ((2 * n + 1 : ℕ) : ℝ) ≤ limitingDistribution B a c
  refine ⟨?_, reducedHamiltonian_rightRoot_lower_bound n γ hγ⟩
  have hprob (t : ℝ) :
      ‖(quantumPropagator n γ t *ᵥ (fun j => (a j : ℂ))) (rightRoot n)‖ ^ 2 =
        eigenTransitionProb (fun r => ⟪B r, a⟫_ℝ * ⟪B r, c⟫_ℝ) h.eigenvalues t := by
    rw [propagator_right_root_spectral, normSq_spectralAmplitude]
    simp [B, c, EuclideanSpace.inner_single_right]
  simp_rw [hprob]
  exact timeAverage_limitingDistribution n B a c h.eigenvalues
    (reduced_spectrum_injective n γ hγ)

end Qatlib.Papers.QWalkDiff01.MainResults
