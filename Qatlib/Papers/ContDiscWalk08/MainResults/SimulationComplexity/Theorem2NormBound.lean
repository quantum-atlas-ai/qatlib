/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.Theorem1Eigenpairs

/-!
# Compressed simulation at zero steps

The definitions `scaledHamiltonian`, `hParam`, and `discreteWalkSimulation` specify the
normalized Hamiltonian and a compressed rotated walk expression associated with Theorem 2 of
[Childs2010]. The module proves inverse identities for the swap rotations and verifies the
simulation bound at zero steps.

## Main statements

* `scaledHamiltonian_isHermitian`: normalization preserves Hermiticity.
* `discreteWalkSimulation_zero`: the zero-step expression is the identity.
* `theorem2_zero_steps`: the stated error bound holds at zero steps.

## References

* [Childs, 2010][Childs2010]
-/

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

/-- Defines the Hamiltonian scaled by the reciprocal of `D.absNorm`. -/
def scaledHamiltonian (D : WalkSetup I) : Matrix I I ℂ :=
  (((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H

/-- Defines the ratio of the norm of `D.H` to `D.absNorm`. -/
def hParam (D : WalkSetup I) : ℝ :=
  ‖D.H‖ / D.absNorm

/-- Defines the compression by `D.T` of the rotated `τ`th power of `Complex.I • walkOperator D`. -/
def discreteWalkSimulation (D : WalkSetup I) (τ : ℕ) : Matrix I I ℂ :=
  D.Tᴴ * (minusRotation * (Complex.I • walkOperator D) ^ τ * plusRotation) * D.T

/-- The product of the two unnormalized swap rotations `1 + iS` and `1 - iS` equals twice the
identity. -/
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

/-- The square of the complex coercion of `1 / √2`, multiplied by two, equals one. -/
theorem invSqrtTwo_sq_mul_two :
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2 = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    have hcast : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)
        = (((Real.sqrt 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [show (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((Real.sqrt 2 : ℂ))⁻¹ from by push_cast; ring]
  rw [← mul_inv, hsq]
  norm_num

/-- The normalized plus rotation followed by the minus rotation is the identity. -/
theorem plusRotation_mul_minusRotation :
    (plusRotation : Matrix (I × I) (I × I) ℂ) * minusRotation = 1 := by
  unfold plusRotation minusRotation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, rotation_core, smul_smul,
    invSqrtTwo_sq_mul_two, one_smul]

/-- The normalized minus rotation followed by the plus rotation is the identity. -/
theorem minusRotation_mul_plusRotation :
    (minusRotation : Matrix (I × I) (I × I) ℂ) * plusRotation = 1 := by
  exact mul_eq_one_comm.mp plusRotation_mul_minusRotation

/-- The normalized Hamiltonian `scaledHamiltonian D` is Hermitian. -/
theorem scaledHamiltonian_isHermitian (D : WalkSetup I) :
    (scaledHamiltonian D).IsHermitian := by
  unfold scaledHamiltonian
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  rw [show (star (((D.absNorm)⁻¹ : ℝ) : ℂ)) = (((D.absNorm)⁻¹ : ℝ) : ℂ) from by simp,
    D.isHermitian.eq]

/-- The compressed discrete walk simulation at zero steps is the identity. -/
theorem discreteWalkSimulation_zero (D : WalkSetup I) :
    discreteWalkSimulation D 0 = 1 := by
  unfold discreteWalkSimulation
  rw [pow_zero, Matrix.mul_one, minusRotation_mul_plusRotation, Matrix.mul_one,
    D.isometry]

/-- The error bound in the form of Theorem 2 of [Childs2010] holds at zero steps for the
normalized Hamiltonian. -/
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
