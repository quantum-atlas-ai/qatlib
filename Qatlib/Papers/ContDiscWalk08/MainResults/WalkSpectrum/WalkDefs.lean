/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.TwoLevelLower
import Qatlib.Concepts.AmplitudeCore.InvFreePhase.Qubitization
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.InvFreePhase
open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem swap_conjTranspose :
    (SwapGate : Matrix (I × I) (I × I) ℂ)ᴴ = SwapGate := by
  rw [SwapGate]
  exact permMatrix_conjTranspose Prod.swap_swap

theorem swap_mul_self :
    SwapGate * SwapGate = (1 : Matrix (I × I) (I × I) ℂ) := by
  rw [SwapGate]
  exact permMatrix_mul_self Prod.swap_swap

theorem swap_mem_unitary :
    (SwapGate : Matrix (I × I) (I × I) ℂ) ∈ Matrix.unitaryGroup (I × I) ℂ :=
  swapGate_unitary

structure WalkSetup (I : Type*) [Fintype I] [DecidableEq I] where

  H : Matrix I I ℂ

  isHermitian : H.IsHermitian

  absNorm : ℝ

  absNorm_pos : 0 < absNorm

  T : Matrix (I × I) I ℂ

  isometry : Tᴴ * T = 1

  gram : Tᴴ * SwapGate * T = (((absNorm)⁻¹ : ℝ) : ℂ) • H

def vertexReflection (D : WalkSetup I) : Matrix (I × I) (I × I) ℂ :=
  (2 : ℂ) • (D.T * D.Tᴴ) - 1

def walkOperator (D : WalkSetup I) : Matrix (I × I) (I × I) ℂ :=
  Complex.I • (SwapGate * vertexReflection D)

def plusRotation : Matrix (I × I) (I × I) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ((1 : Matrix (I × I) (I × I) ℂ) + Complex.I • SwapGate)

def minusRotation : Matrix (I × I) (I × I) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ((1 : Matrix (I × I) (I × I) ℂ) - Complex.I • SwapGate)

theorem vertexReflection_mul_T (D : WalkSetup I) :
    vertexReflection D * D.T = D.T := by
  unfold vertexReflection
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc,
    D.isometry, Matrix.mul_one]
  module

theorem vertexReflection_conjTranspose (D : WalkSetup I) :
    (vertexReflection D)ᴴ = vertexReflection D := by
  unfold vertexReflection
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp

theorem vertexReflection_mul_self (D : WalkSetup I) :
    vertexReflection D * vertexReflection D = 1 := by
  unfold vertexReflection
  have hP : (D.T * D.Tᴴ) * (D.T * D.Tᴴ) = D.T * D.Tᴴ := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc D.T D.Tᴴ D.T, D.isometry, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP]
  module

theorem walkOperator_mem_unitary (D : WalkSetup I) :
    walkOperator D ∈ Matrix.unitaryGroup (I × I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold walkOperator
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, swap_conjTranspose,
    vertexReflection_conjTranspose]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (star Complex.I) * Complex.I = 1 from by
    rw [show (star Complex.I) = -Complex.I from by simp]
    rw [neg_mul, Complex.I_mul_I]
    ring]
  rw [one_smul]
  calc (vertexReflection D * SwapGate) * (SwapGate * vertexReflection D)
      = vertexReflection D * (SwapGate * (SwapGate * vertexReflection D)) :=
        Matrix.mul_assoc _ _ _
    _ = vertexReflection D * ((SwapGate * SwapGate) * vertexReflection D) :=
        congrArg (fun z => vertexReflection D * z)
          (Matrix.mul_assoc SwapGate SwapGate (vertexReflection D)).symm
    _ = vertexReflection D * (1 * vertexReflection D) := by rw [swap_mul_self]
    _ = vertexReflection D * vertexReflection D := by rw [Matrix.one_mul]
    _ = 1 := vertexReflection_mul_self D

theorem walkOperator_mulVec_T (D : WalkSetup I) (v : QState I) :
    walkOperator D *ᵥ (D.T *ᵥ v) = Complex.I • (SwapGate *ᵥ (D.T *ᵥ v)) := by
  unfold walkOperator
  rw [Matrix.smul_mulVec]
  rw [show (SwapGate * vertexReflection D) *ᵥ (D.T *ᵥ v)
      = SwapGate *ᵥ (vertexReflection D *ᵥ (D.T *ᵥ v)) from by
    rw [← Matrix.mulVec_mulVec]]
  have hfix : vertexReflection D *ᵥ (D.T *ᵥ v) = D.T *ᵥ v := by
    rw [Matrix.mulVec_mulVec, vertexReflection_mul_T]
  rw [hfix]

theorem gram_mulVec (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v) :
    (D.Tᴴ * SwapGate * D.T) *ᵥ v = (lam : ℂ) • v := by
  rw [D.gram]
  exact heig

theorem walkOperator_mulVec_swap (D : WalkSetup I) (lam : ℝ) (v : QState I)
    (heig : ((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v = (lam : ℂ) • v) :
    walkOperator D *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))
      = (2 * Complex.I * (lam : ℂ)) • (SwapGate *ᵥ (D.T *ᵥ v))
        - Complex.I • (D.T *ᵥ v) := by
  unfold walkOperator
  rw [Matrix.smul_mulVec]
  rw [show (SwapGate * vertexReflection D) *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))
      = SwapGate *ᵥ (vertexReflection D *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))) from by
    rw [← Matrix.mulVec_mulVec]]
  have hcore : vertexReflection D *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))
      = (2 * (lam : ℂ)) • (D.T *ᵥ v) - SwapGate *ᵥ (D.T *ᵥ v) := by
    unfold vertexReflection
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 : (D.T * D.Tᴴ) *ᵥ (SwapGate *ᵥ (D.T *ᵥ v)) = (lam : ℂ) • (D.T *ᵥ v) := by
      have hstep : D.Tᴴ *ᵥ (SwapGate *ᵥ (D.T *ᵥ v)) = (D.Tᴴ * SwapGate * D.T) *ᵥ v := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      calc (D.T * D.Tᴴ) *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))
          = D.T *ᵥ (D.Tᴴ *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))) := by
            rw [← Matrix.mulVec_mulVec]
        _ = D.T *ᵥ ((D.Tᴴ * SwapGate * D.T) *ᵥ v) := by rw [hstep]
        _ = D.T *ᵥ (((((D.absNorm)⁻¹ : ℝ) : ℂ) • D.H) *ᵥ v) := by rw [D.gram]
        _ = D.T *ᵥ ((lam : ℂ) • v) := by rw [heig]
        _ = (lam : ℂ) • (D.T *ᵥ v) := by rw [Matrix.mulVec_smul]
    rw [h1, smul_smul]
  rw [hcore]
  rw [Matrix.mulVec_sub]
  rw [show SwapGate *ᵥ ((2 * (lam : ℂ)) • (D.T *ᵥ v))
      = (2 * (lam : ℂ)) • (SwapGate *ᵥ (D.T *ᵥ v)) from by rw [Matrix.mulVec_smul]]
  rw [show SwapGate *ᵥ (SwapGate *ᵥ (D.T *ᵥ v))
      = (SwapGate * SwapGate) *ᵥ (D.T *ᵥ v) from by rw [Matrix.mulVec_mulVec]]
  rw [swap_mul_self, Matrix.one_mulVec]
  rw [smul_sub, smul_smul]
  rw [show Complex.I * ((2 : ℂ) * (lam : ℂ)) = 2 * Complex.I * (lam : ℂ) from by ring]

end Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum
