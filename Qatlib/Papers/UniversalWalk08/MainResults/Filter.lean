/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk08.MainResults.WalkModel.MomentumStates
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
set_option warningAsError false

namespace Qatlib.Papers.UniversalWalk08.MainResults.Filter

open Matrix

set_option autoImplicit false

def transferMatrix (a : ℝ) (y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ) - y, -1; 1, 0]

theorem transferMatrix_det (a : ℝ) (y : ℂ) : (transferMatrix a y).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [transferMatrix]

theorem transferMatrix_trace (a : ℝ) (y : ℂ) :
    transferMatrix a y 0 0 + transferMatrix a y 1 1 = (a : ℂ) - y := by
  simp [transferMatrix]

theorem transferMatrix_sq (a : ℝ) (y : ℂ) :
    transferMatrix a y * transferMatrix a y =
      ((a : ℂ) - y) • transferMatrix a y - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transferMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def ampVec (u0 u1 : ℂ) : Fin 2 → ℂ := ![u1, u0]

theorem transferMatrix_mulVec (a : ℝ) (y : ℂ) (u0 u1 : ℂ) :
    (transferMatrix a y).mulVec (ampVec u0 u1) =
      ampVec u1 ((a : ℂ) * u1 - y * u1 - u0) := by
  funext i
  fin_cases i <;>
    simp [transferMatrix, ampVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem transferMatrix_pow_mulVec (a : ℝ) (y : ℂ) (u : ℕ → ℂ)
    (hrec : ∀ n, u (n + 2) = ((a : ℂ) - y) * u (n + 1) - u n) :
    ∀ n, (transferMatrix a y ^ n).mulVec (ampVec (u 0) (u 1)) =
      ampVec (u n) (u (n + 1)) := by
  intro n
  induction n with
  | zero => simp [ampVec]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    rw [transferMatrix_mulVec]
    have h := hrec n
    simp only [ampVec] at h ⊢
    rw [h]
    congr 1
    ring

noncomputable def filterY (k : ℝ) : ℂ :=
  Complex.I * Complex.exp (((2 * k : ℝ) : ℂ) * Complex.I) *
    ((Real.cos (2 * k) : ℂ) / (Real.sin k : ℂ))

theorem cos_neg_pi_div_two : Real.cos (-(Real.pi / 2)) = 0 := by
  rw [Real.cos_neg, Real.cos_pi_div_two]

theorem cos_neg_three_pi_div_two : Real.cos (-(3 * Real.pi / 2)) = 0 := by
  rw [Real.cos_neg, show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
    Real.cos_add, Real.cos_pi_div_two, Real.cos_pi, Real.sin_pi_div_two, Real.sin_pi]
  ring

theorem sin_neg_three_pi_div_two : Real.sin (-(3 * Real.pi / 2)) = 1 := by
  rw [Real.sin_neg, show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring,
    Real.sin_add, Real.sin_pi_div_two, Real.cos_pi, Real.cos_pi_div_two, Real.sin_pi]
  ring

theorem filterY_working_momentum : filterY (-(Real.pi / 4)) = 0 := by
  unfold filterY
  have hcos : Real.cos (2 * (-(Real.pi / 4))) = 0 := by
    rw [show 2 * (-(Real.pi / 4)) = -(Real.pi / 2) by ring, cos_neg_pi_div_two]
  rw [hcos]
  simp

theorem filterY_second_momentum : filterY (-(3 * Real.pi / 4)) = 0 := by
  unfold filterY
  have hcos : Real.cos (2 * (-(3 * Real.pi / 4))) = 0 := by
    rw [show 2 * (-(3 * Real.pi / 4)) = -(3 * Real.pi / 2) by ring,
      cos_neg_three_pi_div_two]
  rw [hcos]
  simp

theorem sin_neg_pi_div_four : Real.sin (-(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  rw [Real.sin_neg, Real.sin_pi_div_four]

theorem sin_working_momentum_ne_zero : Real.sin (-(Real.pi / 4)) ≠ 0 := by
  rw [sin_neg_pi_div_four]
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  intro h
  have : Real.sqrt 2 / 2 = 0 := by linarith [neg_eq_zero.mp h]
  linarith [hpos]

theorem sqrt_two_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem ofReal_sqrt_two_div_two :
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) = (Real.sqrt 2 : ℂ) / 2 := by
  push_cast
  ring

noncomputable def workingEigenPlus : ℂ :=
  ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I)

noncomputable def workingEigenMinus : ℂ :=
  ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I)

theorem workingEigenPlus_sq : workingEigenPlus ^ 2 = Complex.I := by
  unfold workingEigenPlus
  rw [ofReal_sqrt_two_div_two, mul_pow, div_pow, sqrt_two_sq_complex]
  have h1I : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    rw [add_sq, Complex.I_sq]; ring
  rw [h1I]
  ring

theorem workingEigenMinus_sq : workingEigenMinus ^ 2 = -Complex.I := by
  unfold workingEigenMinus
  rw [ofReal_sqrt_two_div_two, mul_pow, div_pow, sqrt_two_sq_complex]
  have h1I : (1 - Complex.I) ^ 2 = -(2 * Complex.I) := by
    rw [sub_sq, Complex.I_sq]; ring
  rw [h1I]
  ring

theorem sqrt_two_mul_workingEigenPlus :
    (Real.sqrt 2 : ℂ) * workingEigenPlus = 1 + Complex.I := by
  unfold workingEigenPlus
  rw [ofReal_sqrt_two_div_two]
  have h2 := sqrt_two_sq_complex
  rw [show (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2 * (1 + Complex.I)) =
      ((Real.sqrt 2 : ℂ)) ^ 2 / 2 * (1 + Complex.I) by ring]
  rw [h2]
  ring

theorem sqrt_two_mul_workingEigenMinus :
    (Real.sqrt 2 : ℂ) * workingEigenMinus = 1 - Complex.I := by
  unfold workingEigenMinus
  rw [ofReal_sqrt_two_div_two]
  have h2 := sqrt_two_sq_complex
  rw [show (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I)) =
      ((Real.sqrt 2 : ℂ)) ^ 2 / 2 * (1 - Complex.I) by ring]
  rw [h2]
  ring

theorem workingEigenPlus_charpoly :
    workingEigenPlus ^ 2 - (Real.sqrt 2 : ℂ) * workingEigenPlus + 1 = 0 := by
  rw [workingEigenPlus_sq, sqrt_two_mul_workingEigenPlus]
  ring

theorem workingEigenMinus_charpoly :
    workingEigenMinus ^ 2 - (Real.sqrt 2 : ℂ) * workingEigenMinus + 1 = 0 := by
  rw [workingEigenMinus_sq, sqrt_two_mul_workingEigenMinus]
  ring

theorem normSq_sqrt_two_div_two :
    Complex.normSq ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.normSq_ofReal]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.sqrt_nonneg 2]

theorem normSq_one_add_I : Complex.normSq (1 + Complex.I) = 2 := by
  simp [Complex.normSq_apply]
  norm_num

theorem normSq_one_sub_I : Complex.normSq (1 - Complex.I) = 2 := by
  simp [Complex.normSq_apply]
  norm_num

theorem workingEigenPlus_normSq : Complex.normSq workingEigenPlus = 1 := by
  unfold workingEigenPlus
  rw [Complex.normSq_mul, normSq_sqrt_two_div_two, normSq_one_add_I]
  norm_num

theorem workingEigenMinus_normSq : Complex.normSq workingEigenMinus = 1 := by
  unfold workingEigenMinus
  rw [Complex.normSq_mul, normSq_sqrt_two_div_two, normSq_one_sub_I]
  norm_num

theorem workingEigen_mul : workingEigenPlus * workingEigenMinus = 1 := by
  unfold workingEigenPlus workingEigenMinus
  rw [ofReal_sqrt_two_div_two]
  have h2 := sqrt_two_sq_complex
  rw [show (Real.sqrt 2 : ℂ) / 2 * (1 + Complex.I) * ((Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I)) =
      ((Real.sqrt 2 : ℂ)) ^ 2 / 4 * ((1 + Complex.I) * (1 - Complex.I)) by ring]
  have h1 : (1 + Complex.I) * (1 - Complex.I) = 2 := by
    rw [show (1 + Complex.I) * (1 - Complex.I) = 1 - Complex.I ^ 2 by ring]
    rw [Complex.I_sq]; ring
  rw [h1, h2]
  ring

theorem transferMatrix_eigenvector (a : ℝ) (y lam : ℂ)
    (h : lam ^ 2 - ((a : ℂ) - y) * lam + 1 = 0) :
    (transferMatrix a y).mulVec ![lam, 1] = lam • ![lam, 1] := by
  funext i
  fin_cases i
  · simp [transferMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination -h
  · simp [transferMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem transferMatrix_pow_eigenvector (a : ℝ) (y lam : ℂ)
    (h : lam ^ 2 - ((a : ℂ) - y) * lam + 1 = 0) :
    ∀ n, ((transferMatrix a y) ^ n).mulVec ![lam, 1] = lam ^ n • ![lam, 1] := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    rw [Matrix.mulVec_smul, transferMatrix_eigenvector a y lam h, smul_smul, pow_succ]

section RealGrowth

def transferReal (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, -1; 1, 0]

noncomputable def realEigenPlus (a : ℝ) : ℝ :=
  (a + Real.sqrt (a ^ 2 - 4)) / 2

theorem realEigenPlus_charpoly {a : ℝ} (ha : 2 < a) :
    realEigenPlus a ^ 2 - a * realEigenPlus a + 1 = 0 := by
  unfold realEigenPlus
  have h4 : 0 ≤ a ^ 2 - 4 := by nlinarith
  have hs : Real.sqrt (a ^ 2 - 4) ^ 2 = a ^ 2 - 4 := Real.sq_sqrt h4
  field_simp
  nlinarith [hs]

theorem one_lt_realEigenPlus {a : ℝ} (ha : 2 < a) : 1 < realEigenPlus a := by
  unfold realEigenPlus
  have h4 : (0 : ℝ) < a ^ 2 - 4 := by nlinarith
  have hs0 : 0 < Real.sqrt (a ^ 2 - 4) := Real.sqrt_pos.2 h4
  have hlt : a - 2 < Real.sqrt (a ^ 2 - 4) := by
    rw [← Real.sqrt_sq (by nlinarith : (0 : ℝ) ≤ a - 2)]
    apply Real.sqrt_lt_sqrt (by nlinarith)
    nlinarith
  linarith

theorem transferReal_growth {a : ℝ} (ha : 2 < a) (n : ℕ) :
    (transferReal a ^ n).mulVec ![realEigenPlus a, 1] =
      realEigenPlus a ^ n • ![realEigenPlus a, 1] := by
  have hchar : realEigenPlus a ^ 2 - a * realEigenPlus a + 1 = 0 :=
    realEigenPlus_charpoly ha
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    have hstep : (transferReal a).mulVec ![realEigenPlus a, 1] =
        realEigenPlus a • ![realEigenPlus a, 1] := by
      funext i
      fin_cases i
      · simp [transferReal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linear_combination -hchar
      · simp [transferReal, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [Matrix.mulVec_smul, hstep, smul_smul, pow_succ]

end RealGrowth

end Qatlib.Papers.UniversalWalk08.MainResults.Filter
