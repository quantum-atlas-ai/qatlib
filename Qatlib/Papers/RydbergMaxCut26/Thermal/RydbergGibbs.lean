/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Thermal.GibbsSpectral
import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Hamiltonian
set_option warningAsError false
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

def rydbergGibbs {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  gibbsState (secondaryHamiltonian ends w) T

def rydbergEigenvalues {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : Reg n → ℝ :=
  (show (secondaryHamiltonian ends w).IsHermitian from secondary_hermitian ends w).eigenvalues

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

def rydbergQuality {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ)
    (ρ0 : Matrix (Reg n) (Reg n) ℂ) : ℝ :=
  energy (secondaryHamiltonian ends w) (rydbergGibbs ends w T)/energy (secondaryHamiltonian ends w) ρ0

theorem actual_quality_spectral {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ) (hT : 0<T)
    (ρ0 : Matrix (Reg n) (Reg n) ℂ) :
    rydbergQuality ends w T ρ0=
      ((∑ i,rydbergEigenvalues ends w i*Real.exp (-rydbergEigenvalues ends w i/T))/
        (∑ i,Real.exp (-rydbergEigenvalues ends w i/T)))/energy (secondaryHamiltonian ends w) ρ0 := by
  rw [rydbergQuality,(actual_rydberg_gibbs ends w T hT).2.2.2]

theorem actual_quality_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (T : ℝ)
    (ρ0 : Matrix (Reg n) (Reg n) ℂ) (hE0 : energy (secondaryHamiltonian ends w) ρ0<0) :
    rydbergQuality ends w T ρ0*energy (secondaryHamiltonian ends w) ρ0=
      energy (secondaryHamiltonian ends w) (rydbergGibbs ends w T) := by
  rw [rydbergQuality]
  exact div_mul_cancel₀ _ hE0.ne

end Qatlib.Papers.RydbergMaxCut26.Thermal.Rydberg
