/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
public import Qatlib.Papers.QWalkDiff01.MainResults.QuantumPropagation
public import Qatlib.Papers.QWalkDiff01.MainResults.SpectralReduction
public import Qatlib.Papers.QWalkDiff01.MainResults.TimeAverage

@[expose] public section

/-!
# The reduced propagator as a finite spectral sum

Section IV, Eqs. (15)–(16) uses the finite eigenbasis expansion of the
transition amplitude before averaging its squared modulus. For a real
initial column vector, the real symmetric eigensystem yields real
coefficients. The actual complex propagator supplies their phases.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QWalkDiff01.MainResults
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- The right-root amplitude of the actual reduced propagator on a
real initial vector is the finite eigenbasis expansion of Section IV. -/
theorem propagator_right_root_spectral (n : ℕ) (γ t : ℝ)
    (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    (quantumPropagator n γ t *ᵥ (fun j => (a j : ℂ))) (rightRoot n) =
      spectralAmplitude
        (fun r =>
          ⟪(reducedHamiltonian_isHermitian n γ).eigenvectorBasis r, a⟫_ℝ *
            ((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r) (rightRoot n))
        (reducedHamiltonian_isHermitian n γ).eigenvalues t := by
  let hH := reducedHamiltonian_isHermitian n γ
  let B := hH.eigenvectorBasis
  let E := hH.eigenvalues
  let c (r : Fin (2 * n + 1)) : ℝ := ⟪B r, a⟫_ℝ
  let u (r j : Fin (2 * n + 1)) : ℂ := (B r j : ℂ)
  change _ = spectralAmplitude (fun r => c r * B r (rightRoot n)) E t
  have hcast (x : ℝ) : algebraMap ℝ ℂ x = (x : ℂ) := rfl
  have heigen (r : Fin (2 * n + 1)) :
      reducedHamiltonianC n γ *ᵥ u r = (E r : ℂ) • u r := by
    funext j
    have h := congrFun (hH.mulVec_eigenvectorBasis r) j
    have hh := congrArg (algebraMap ℝ ℂ) h
    rw [RingHom.map_mulVec] at hh
    change (reducedHamiltonianC n γ *ᵥ u r) j =
      (algebraMap ℝ ℂ) (E r * B r j) at hh
    rw [map_mul] at hh
    simpa only [hcast, u, Pi.smul_apply, smul_eq_mul] using hh
  have hexpand : (fun j => (a j : ℂ)) = ∑ r, (c r : ℂ) • u r := by
    funext j
    let project : EuclideanSpace ℝ (Fin (2 * n + 1)) →ₗ[ℝ] ℝ :=
      PiLp.projₗ 2 (fun _ : Fin (2 * n + 1) => ℝ) j
    have h := congrArg project (B.sum_repr' a)
    rw [map_sum] at h
    simp only [map_smul] at h
    change (∑ r, c r * B r j) = a j at h
    have hh := congrArg (algebraMap ℝ ℂ) h.symm
    rw [map_sum] at hh
    simp only [map_mul] at hh
    simpa only [hcast, u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh
  have hprop :
      quantumPropagator n γ t = HamiltonianEvolution (reducedHamiltonianC n γ) t := by
    rw [quantumPropagator, HamiltonianEvolution, neg_mul]
  have hphase (r : Fin (2 * n + 1)) :
      (-Complex.I * (t : ℂ)) * (E r : ℂ) = -(((E r * t : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [hexpand, Matrix.mulVec_sum, hprop]
  simp only [Finset.sum_apply, spectralAmplitude]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.mulVec_smul,
    hamiltonianEvolution_eigenvector (reducedHamiltonianC n γ) (u r) (E r) t (heigen r),
    hphase]
  simp only [Pi.smul_apply, smul_eq_mul, u, Complex.ofReal_mul]
  ring

end Qatlib.Papers.QWalkDiff01.MainResults
