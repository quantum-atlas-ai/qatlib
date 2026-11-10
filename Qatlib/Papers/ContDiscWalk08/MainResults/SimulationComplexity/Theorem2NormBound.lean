/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

def scaledHamiltonian (D : WalkSetup I) : Matrix I I ℂ :=
  (((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H

def hParam (D : WalkSetup I) : ℝ :=
  ‖D.H‖ / D.absNorm

def discreteWalkSimulation (D : WalkSetup I) (τ : ℕ) : Matrix I I ℂ :=
  D.Tᴴ * (minusRotation * (Complex.I • walkOperator D) ^ τ * plusRotation) * D.T

theorem rotation_core :
    (1 + Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ)) *
        (1 - Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ))
      = (2 : ℂ) • (1 : Matrix (I × I) (I × I) ℂ) := by
  have hXX : (Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ)) *
        (Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ)) = (-1 : ℂ) • 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, swap_mul_self]; norm_num
  have h : (1 + Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ)) *
        (1 - Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ))
      = 1 - (Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ)) *
            (Complex.I • (SwapGate : Matrix (I × I) (I × I) ℂ)) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [h, hXX]
  module

theorem invSqrtTwo_sq_mul_two :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    have hcast : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)
        = (((Real.sqrt 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [show (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((Real.sqrt 2 : ℂ))⁻¹ from by push_cast; ring]
  rw [← mul_inv, hsq]
  norm_num

theorem plusRotation_mul_minusRotation :
    (plusRotation : Matrix (I × I) (I × I) ℂ) * minusRotation = 1 := by
  unfold plusRotation minusRotation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, rotation_core, smul_smul,
    invSqrtTwo_sq_mul_two, one_smul]

theorem minusRotation_mul_plusRotation :
    (minusRotation : Matrix (I × I) (I × I) ℂ) * plusRotation = 1 := by
  exact mul_eq_one_comm.mp plusRotation_mul_minusRotation

theorem scaledHamiltonian_isHermitian (D : WalkSetup I) :
    (scaledHamiltonian D).IsHermitian := by
  unfold scaledHamiltonian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  rw [show (star (((D.absNorm)⁻¹ : ℝ) : ℂ)) = (((D.absNorm)⁻¹ : ℝ) : ℂ) from by simp,
    D.isHermitian.eq]

theorem discreteWalkSimulation_zero (D : WalkSetup I) :
    discreteWalkSimulation D 0 = 1 := by
  unfold discreteWalkSimulation
  rw [pow_zero, Matrix.mul_one, minusRotation_mul_plusRotation, Matrix.mul_one,
    D.isometry]

theorem theorem2_zero_steps (D : WalkSetup I) :
    ‖discreteWalkSimulation D 0 - HamiltonianEvolution (scaledHamiltonian D) 0‖
      ≤ (hParam D) ^ 2 * (1 + (Real.pi / 2 - 1) * hParam D * (0 : ℝ)) := by
  rw [discreteWalkSimulation_zero, hamiltonianEvolution_zero, sub_self, norm_zero]
  have h2 : 0 ≤ (hParam D) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ 1 + (Real.pi / 2 - 1) * hParam D * (0 : ℝ) := by
    have hz : (Real.pi / 2 - 1) * hParam D * (0 : ℝ) = 0 := by ring
    rw [hz]; norm_num
  exact mul_nonneg h2 h3

end Qatlib.Papers.ContDiscWalk08.MainResults.SimulationComplexity
