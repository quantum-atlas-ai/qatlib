/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence

open Qatlib.Papers.AdiabStateGen03.MainResults

variable {n : ℕ}

theorem two_sq_sum_ge_half (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    1 / 2 ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem sqrtGate_modulus_ge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 1) :
    1 / Real.sqrt 2 ≤ ‖(a : ℂ) + (b : ℂ) * Complex.I‖ := by
  have hsq : 1 / 2 ≤ a ^ 2 + b ^ 2 := two_sq_sum_ge_half a b ha hb h
  rw [Complex.norm_add_mul_I]
  have hsqrt : 1 / Real.sqrt 2 = Real.sqrt (1 / 2) := by
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, one_div]
  rw [hsqrt]
  exact Real.sqrt_le_sqrt hsq

theorem toOp_adjoint_eq (P : Ham n) (hP : Pᴴ = P) :
    ContinuousLinearMap.adjoint (toOp P) = toOp P := by
  have h : Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) (star P)
      = star (Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) P) := map_star _ _
  simpa [toOp, Matrix.star_eq_conjTranspose, hP, ContinuousLinearMap.star_eq_adjoint] using h.symm

theorem toOp_mul_self (P : Ham n) (hidem : P * P = P) :
    toOp P * toOp P = toOp P := by
  have h : Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) (P * P)
      = Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) P
        * Matrix.toEuclideanCLM (n := Dim n) (𝕜 := ℂ) P := map_mul _ _ _
  rw [hidem] at h
  exact h.symm

theorem projection_norm_le_one (P : Ham n) (hP : Pᴴ = P) (hidem : P * P = P) :
    ‖toOp P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro x
  by_cases hx : toOp P x = 0
  · rw [hx, norm_zero]
    positivity
  · have hself : ContinuousLinearMap.adjoint (toOp P) = toOp P :=
      toOp_adjoint_eq P hP
    have hmul : toOp P * toOp P = toOp P := toOp_mul_self P hidem
    have hinner : (⟪toOp P x, toOp P x⟫_ℂ).re = (⟪x, toOp P x⟫_ℂ).re := by
      have h3 : ⟪toOp P x, toOp P x⟫_ℂ = ⟪x, toOp P (toOp P x)⟫_ℂ := by
        have h4 := ContinuousLinearMap.adjoint_inner_right (toOp P) x (toOp P x)
        rw [hself] at h4
        exact h4.symm
      have h5 : toOp P (toOp P x) = toOp P x := by
        rw [← ContinuousLinearMap.mul_apply, hmul]
      rw [h3, h5]
    have hnorm : ‖toOp P x‖ ^ 2 = (⟪x, toOp P x⟫_ℂ).re := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (toOp P x)]
      exact hinner
    have hCS : (⟪x, toOp P x⟫_ℂ).re ≤ ‖x‖ * ‖toOp P x‖ := by
      calc (⟪x, toOp P x⟫_ℂ).re ≤ ‖⟪x, toOp P x⟫_ℂ‖ := Complex.re_le_norm _
        _ ≤ ‖x‖ * ‖toOp P x‖ := norm_inner_le_norm x (toOp P x)
    have hpos : 0 < ‖toOp P x‖ := norm_pos_iff.mpr hx
    nlinarith [norm_nonneg x, norm_nonneg (toOp P x)]

end Qatlib.Papers.AdiabStateGen03.MainResults.Equivalence
