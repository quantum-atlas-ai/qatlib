/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.JordanTwoProjectorsStat
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib
open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QMAAmplify09.MainResults.TwoProjectorRotation

def reflection {D : ℕ} (P : Operator D) : Operator D := (2 : ℂ) • P - 1

def rotationBlock (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ), -(s : ℂ); (s : ℂ), (c : ℂ)]

def reflectionBlock (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(c : ℂ), (s : ℂ); (s : ℂ), -(c : ℂ)]

def involutionBlock : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem reflectionBlock_mul_involution (c s : ℝ) :
    reflectionBlock c s * involutionBlock = rotationBlock c s := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [reflectionBlock, involutionBlock, rotationBlock]

theorem det_rotationBlock (c s : ℝ) :
    (rotationBlock c s).det = (c : ℂ) ^ 2 + (s : ℂ) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [rotationBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

theorem rotationBlock_mulVec_eigen_plus {c s θ : ℝ} (hc : c = Real.cos θ)
    (hs : s = Real.sin θ) :
    rotationBlock c s *ᵥ ![1, -Complex.I] = Complex.exp (θ * Complex.I) • ![1, -Complex.I] := by
  subst hc hs
  rw [Complex.exp_ofReal_mul_I]
  ext i <;> fin_cases i <;>
    simp [rotationBlock, Matrix.mulVec, dotProduct] <;>
    ring_nf <;> (try rw [Complex.I_sq]) <;> (try rw [Complex.I_mul_I]) <;> ring

theorem rotationBlock_mulVec_eigen_minus {c s θ : ℝ} (hc : c = Real.cos θ)
    (hs : s = Real.sin θ) :
    rotationBlock c s *ᵥ ![1, Complex.I] =
      Complex.exp (-θ * Complex.I) • ![1, Complex.I] := by
  subst hc hs
  have hexp : Complex.exp (-↑θ * Complex.I) = Complex.exp ((-θ : ℝ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp, Complex.exp_ofReal_mul_I]
  ext i <;> fin_cases i <;>
    simp [rotationBlock, Matrix.mulVec, dotProduct] <;>
    ring_nf <;> (try rw [Complex.I_sq]) <;> (try rw [Complex.I_mul_I]) <;> ring

theorem block_rotation_action {D : ℕ} (P Q : Operator D)
    (k : ℕ) (u v : Fin k → QState (Fin D)) (d : Fin k → ℝ)
    (horth_u : ∀ i j, Inner (u i) (u j) = if i = j then 1 else 0)
    (huv : ∀ i j, Inner (u i) (v j) = 0)
    (hPact : ∀ x : QState (Fin D), P *ᵥ x = ∑ j, Inner (u j) x • u j)
    (hQu : ∀ i, Q *ᵥ (u i) = d i • u i + Real.sqrt (d i * (1 - d i)) • v i)
    (hQv : ∀ i, Q *ᵥ (v i) = Real.sqrt (d i * (1 - d i)) • u i + (1 - d i) • v i)
    (i : Fin k) (a b : ℂ) :
    reflection Q *ᵥ (reflection P *ᵥ (a • u i + b • v i)) =
      (a * ((2 * (d i) - 1 : ℝ) : ℂ) - b * ((2 * Real.sqrt (d i * (1 - d i)) : ℝ) : ℂ)) • u i +
        (a * ((2 * Real.sqrt (d i * (1 - d i)) : ℝ) : ℂ) +
          b * ((2 * (d i) - 1 : ℝ) : ℂ)) • v i := by

  have hPu : P *ᵥ u i = u i := by
    rw [hPact (u i)]
    rw [Finset.sum_eq_single i]
    · rw [horth_u i i]
      simp
    · intro j _ hji
      rw [horth_u j i, if_neg hji]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hPv : P *ᵥ v i = 0 := by
    rw [hPact (v i)]
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [huv j i]
    simp

  have hF0 : reflection P *ᵥ (a • u i + b • v i) = a • u i - b • v i := by
    rw [reflection, sub_mulVec, smul_mulVec, one_mulVec, mulVec_add, mulVec_smul,
      mulVec_smul, hPu, hPv]
    simp only [smul_zero, add_zero]
    module

  have hcs : ∀ (r : ℝ) (y : QState (Fin D)), r • y = (r : ℂ) • y := fun r y => by
    ext j
    simp [RCLike.real_smul_eq_coe_mul]
  have hQu' : Q *ᵥ u i = (d i : ℂ) • u i + ((Real.sqrt (d i * (1 - d i)) : ℝ) : ℂ) • v i := by
    rw [hQu i, hcs, hcs]
  have hQv' : Q *ᵥ v i = ((Real.sqrt (d i * (1 - d i)) : ℝ) : ℂ) • u i + ((1 - d i : ℝ) : ℂ) • v i := by
    rw [hQv i, hcs, hcs]

  have hF1u : reflection Q *ᵥ u i =
      ((2 * (d i) - 1 : ℝ) : ℂ) • u i + ((2 * Real.sqrt (d i * (1 - d i)) : ℝ) : ℂ) • v i := by
    rw [reflection, sub_mulVec, smul_mulVec, one_mulVec, hQu']
    push_cast
    simp only [smul_add, smul_smul]
    module
  have hF1v : reflection Q *ᵥ v i =
      ((2 * Real.sqrt (d i * (1 - d i)) : ℝ) : ℂ) • u i +
        ((1 - 2 * (d i) : ℝ) : ℂ) • v i := by
    rw [reflection, sub_mulVec, smul_mulVec, one_mulVec, hQv']
    push_cast
    simp only [smul_add, smul_smul]
    module
  rw [hF0, mulVec_sub, mulVec_smul, mulVec_smul, hF1u, hF1v]
  push_cast
  simp only [smul_add, smul_smul]
  module

theorem oneDimensional_action {D : ℕ} (P Q : Operator D) (x : QState (Fin D))
    (p q : ℂ)
    (hP : P *ᵥ x = p • x) (hQ : Q *ᵥ x = q • x) :
    reflection Q *ᵥ (reflection P *ᵥ x) = ((2 * q - 1) * (2 * p - 1)) • x := by
  have hF0 : reflection P *ᵥ x = (2 * p - 1) • x := by
    rw [reflection, sub_mulVec, smul_mulVec, one_mulVec, hP]
    module
  rw [hF0, reflection, sub_mulVec, smul_mulVec, one_mulVec, mulVec_smul, hQ]
  module

theorem oneDimensional_eigenvalue_pm_one {p q : ℂ} (hp : p = 0 ∨ p = 1)
    (hq : q = 0 ∨ q = 1) :
    (2 * q - 1) * (2 * p - 1) = 1 ∨ (2 * q - 1) * (2 * p - 1) = -1 := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> norm_num

end Qatlib.Papers.QMAAmplify09.MainResults.TwoProjectorRotation
