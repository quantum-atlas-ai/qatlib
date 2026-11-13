/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Thermal.GibbsSpectral
import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Hamiltonian

/-!
# Gibbs states of the Rydberg Hamiltonian

The definitions `rydbergGibbs` and `rydbergEigenvalues` specialize the finite Gibbs construction
to the secondary Rydberg Hamiltonian. The quality ratio `rydbergQuality` compares the Gibbs
energy with a reference matrix's energy and has an explicit spectral expression at positive
temperature. See [CrostaSaubanereHuber2026].

## Main statements

* `actual_rydberg_gibbs`: proves physicality and the spectral energy formula at positive
  temperature.
* `actual_quality_spectral`: expresses the quality ratio using Boltzmann weights.
* `actual_quality_energy`: recovers the Gibbs energy from the quality ratio when the reference
  energy is negative.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Hamiltonian
open Qatlib.Papers.RydbergMaxCut26.Thermal.Spectral

namespace Qatlib.Papers.RydbergMaxCut26.Thermal.Rydberg

/-- The normalized Gibbs matrix of the secondary Rydberg Hamiltonian at parameter `T`. -/
def rydbergGibbs {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  gibbsState (secondaryHamiltonian ends w) T

/-- The real eigenvalues of the Hermitian secondary Rydberg Hamiltonian. -/
def rydbergEigenvalues {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : Reg n → ℝ :=
  (show (secondaryHamiltonian ends w).IsHermitian from secondary_hermitian ends w).eigenvalues

/-- At positive temperature, the Rydberg partition function is positive and the Gibbs matrix is
positive semidefinite with trace one; its secondary energy equals the Boltzmann-weighted
mean of the Rydberg eigenvalues. -/
theorem actual_rydberg_gibbs {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ) (hT : 0<T) :
    0<partition (secondaryHamiltonian ends w) T ∧
      (rydbergGibbs ends w T).PosSemidef ∧ (rydbergGibbs ends w T).trace=1 ∧
      energy (secondaryHamiltonian ends w) (rydbergGibbs ends w T)=
        (∑ i,rydbergEigenvalues ends w i*Real.exp (-rydbergEigenvalues ends w i/T))/
          (∑ i,Real.exp (-rydbergEigenvalues ends w i/T)) := by
  have hH : (secondaryHamiltonian ends w).IsHermitian := secondary_hermitian ends w
  have h := positive_temperature_gibbs (secondaryHamiltonian ends w) hH T hT
  refine ⟨h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
  rw [energy,Matrix.trace_mul_comm]
  exact h.2.2.2.2

/-- The ratio of the secondary energy of the Rydberg Gibbs matrix to that of the reference
matrix `ρ0`. -/
def rydbergQuality {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ)
    (ρ0 : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  energy (secondaryHamiltonian ends w) (rydbergGibbs ends w T)/energy (secondaryHamiltonian ends w) ρ0

/-- At positive temperature, the Rydberg quality ratio is the Boltzmann-weighted mean eigenvalue
divided by the secondary energy of the reference matrix. -/
theorem actual_quality_spectral {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ) (hT : 0<T)
    (ρ0 : Matrix (Reg n) (Reg n) ℂ) :
    rydbergQuality ends w T ρ0=
      ((∑ i,rydbergEigenvalues ends w i*Real.exp (-rydbergEigenvalues ends w i/T))/
        (∑ i,Real.exp (-rydbergEigenvalues ends w i/T)))/energy (secondaryHamiltonian ends w) ρ0 := by
  rw [rydbergQuality,(actual_rydberg_gibbs ends w T hT).2.2.2]

/-- When the reference secondary energy is negative, multiplying `rydbergQuality` by that energy
recovers the Gibbs secondary energy; see [CrostaSaubanereHuber2026]. -/
theorem actual_quality_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ)
    (ρ0 : Matrix (Reg n) (Reg n) ℂ) (hE0 : energy (secondaryHamiltonian ends w) ρ0<0) :
    rydbergQuality ends w T ρ0*energy (secondaryHamiltonian ends w) ρ0=
      energy (secondaryHamiltonian ends w) (rydbergGibbs ends w T) := by
  rw [rydbergQuality]
  exact div_mul_cancel₀ _ hE0.ne

end Qatlib.Papers.RydbergMaxCut26.Thermal.Rydberg
