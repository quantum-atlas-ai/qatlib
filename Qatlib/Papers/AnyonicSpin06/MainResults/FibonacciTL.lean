/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Qatlib.Papers.AnyonicSpin06.MainResults.TemperleyLieb
import Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciDensity

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciTL

open Qatlib.Papers.AnyonicSpin06.MainResults.TemperleyLieb
open Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciDensity

lemma exp_I_add_exp_neg_I (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) + Complex.exp (-(Complex.I * (θ : ℂ)))
      = 2 * (Real.cos θ : ℂ) := by
  have h1 : Complex.exp (Complex.I * (θ : ℂ))
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h2 : Complex.exp (-(Complex.I * (θ : ℂ)))
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [h1, h2]
  ring

theorem A5_sq_add_inv :
    A5 ^ 2 + (A5 ^ 2)⁻¹ = -(goldenRatio : ℂ) := by
  have hsq : A5 ^ 2 = Complex.exp (Complex.I * ((6 * Real.pi / 5 : ℝ) : ℂ)) := by
    unfold A5
    rw [sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hinv : (A5 ^ 2)⁻¹
      = Complex.exp (-(Complex.I * ((6 * Real.pi / 5 : ℝ) : ℂ))) := by
    rw [hsq, ← Complex.exp_neg]
  rw [hinv, hsq, exp_I_add_exp_neg_I]
  have hcos : Real.cos (6 * Real.pi / 5) = -Real.cos (Real.pi / 5) := by
    rw [show 6 * Real.pi / 5 = Real.pi / 5 + Real.pi by ring, Real.cos_add_pi]
  rw [hcos, Real.cos_pi_div_five]
  unfold goldenRatio
  push_cast
  ring

theorem A5_fib_rel : A5 ^ 4 + (goldenRatio : ℂ) * A5 ^ 2 + 1 = 0 := by
  have h := A5_sq_add_inv
  have hA5 : A5 ≠ 0 := by
    unfold A5
    exact Complex.exp_ne_zero _
  have hA2 : A5 ^ 2 ≠ 0 := pow_ne_zero 2 hA5
  have hmul : A5 ^ 2 * (A5 ^ 2 + (A5 ^ 2)⁻¹) = A5 ^ 2 * (-(goldenRatio : ℂ)) := by
    rw [h]
  have hsimp : A5 ^ 2 * (A5 ^ 2 + (A5 ^ 2)⁻¹) = A5 ^ 4 + 1 := by
    rw [mul_add, mul_inv_cancel₀ hA2, ← pow_add]
  rw [hsimp] at hmul
  linear_combination hmul

theorem Rmat_eq_smul_phi1 : Rmat = (A5 ^ 7) • phi1 A5 (goldenRatio : ℂ) := by
  have hA5 : A5 ≠ 0 := by unfold A5; exact Complex.exp_ne_zero _
  have hkey : A5 ^ 7 * (A5 + A5⁻¹ * (goldenRatio : ℂ)) = -(A5 ^ 4) := by
    have h1 : A5 ^ 7 * (A5 + A5⁻¹ * (goldenRatio : ℂ))
        = A5 ^ 8 + (goldenRatio : ℂ) * A5 ^ 6 := by
      field_simp
    have h2 : A5 ^ 8 + (goldenRatio : ℂ) * A5 ^ 6 = -(A5 ^ 4) := by
      have h := A5_fib_rel
      linear_combination (A5 ^ 4) * h
    rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rmat, phi1, TLgen1, Matrix.smul_apply, hkey]
  ring

lemma goldenRatio_mul_tau : goldenRatio * tau = 1 := by
  unfold goldenRatio tau
  have h5 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

theorem Fmat_mul_TLgen1_mul_Fmat :
    Fmat * TLgen1 (goldenRatio : ℂ) * Fmat
      = TLgen2 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) := by
  have hd : (goldenRatio : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < goldenRatio := by unfold goldenRatio; positivity
    exact_mod_cast ne_of_gt h
  have hdt : (goldenRatio : ℂ) * (tau : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, goldenRatio_mul_tau]
    norm_num
  have hs : (Real.sqrt tau : ℂ) * (Real.sqrt tau : ℂ) = (tau : ℂ) := by
    rw [← Complex.ofReal_mul, sqrt_tau_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fmat, TLgen1, TLgen2, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [mul_comm (tau : ℂ) (goldenRatio : ℂ), hdt, one_mul]
    exact eq_inv_of_mul_eq_one_right hdt
  · rw [mul_comm (tau : ℂ) (goldenRatio : ℂ), hdt, one_mul]
  · rw [mul_assoc, hdt, mul_one]
  · ring

lemma smul_mul_smul (a b : ℂ) (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    (a • M) * (b • N) = (a * b) • (M * N) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem Fmat_conj_phi1 :
    Fmat * phi1 A5 (goldenRatio : ℂ) * Fmat
      = phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) := by
  have hF : Fmat * Fmat = 1 := F_sq
  unfold phi1 phi2
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [Fmat_mul_TLgen1_mul_Fmat, hF]

theorem S2_eq_smul_phi2 :
    S2 = (A5 ^ 7) • phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) := by
  unfold S2
  rw [Rmat_eq_smul_phi1, Matrix.mul_smul, Matrix.smul_mul, Fmat_conj_phi1]

theorem S1_S2_braid : S1 * S2 * S1 = S2 * S1 * S2 := by
  have hA : A5 ≠ 0 := by unfold A5; exact Complex.exp_ne_zero _
  have hd : (goldenRatio : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < goldenRatio := by unfold goldenRatio; positivity
    exact_mod_cast ne_of_gt h
  have hdt : (goldenRatio : ℂ) * (tau : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, goldenRatio_mul_tau]
    norm_num
  have hinv : ((goldenRatio : ℂ))⁻¹ = (tau : ℂ) := inv_eq_of_mul_eq_one_right hdt
  have hs : (Real.sqrt tau : ℂ) * (Real.sqrt tau : ℂ) = (tau : ℂ) := by
    rw [← Complex.ofReal_mul, sqrt_tau_sq]
  have htau2 : (tau : ℂ) ^ 2 + (tau : ℂ) = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_add, tau_sq_add]
    norm_num
  have hc : (Real.sqrt tau : ℂ) ^ 2 = 1 - ((goldenRatio : ℂ))⁻¹ ^ 2 := by
    rw [hinv, pow_two, hs]
    linear_combination htau2
  have hdA : (goldenRatio : ℂ) = -(A5 ^ 2 + (A5⁻¹) ^ 2) := by
    have h := A5_sq_add_inv
    rw [← inv_pow] at h
    rw [h]
    ring
  have hbr : phi1 A5 (goldenRatio : ℂ) * phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ)
      * phi1 A5 (goldenRatio : ℂ)
      = phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) * phi1 A5 (goldenRatio : ℂ)
        * phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) :=
    phi_braid hA hd hc hdA
  have hS1 : S1 = (A5 ^ 7) • phi1 A5 (goldenRatio : ℂ) := Rmat_eq_smul_phi1
  have hS2 : S2 = (A5 ^ 7) • phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) :=
    S2_eq_smul_phi2
  have e1 : S1 * S2 * S1
      = ((A5 ^ 7 * A5 ^ 7) * A5 ^ 7)
        • (phi1 A5 (goldenRatio : ℂ) * phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ)
            * phi1 A5 (goldenRatio : ℂ)) := by
    rw [hS1, hS2, smul_mul_smul, smul_mul_smul]
  have e2 : S2 * S1 * S2
      = ((A5 ^ 7 * A5 ^ 7) * A5 ^ 7)
        • (phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ) * phi1 A5 (goldenRatio : ℂ)
            * phi2 A5 (goldenRatio : ℂ) (Real.sqrt tau : ℂ)) := by
    rw [hS1, hS2, smul_mul_smul, smul_mul_smul]
  rw [e1, e2, hbr]

end Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciTL
