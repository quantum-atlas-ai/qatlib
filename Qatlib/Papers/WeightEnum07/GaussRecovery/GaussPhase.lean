/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeightEnum07.GaussRecovery

variable {F : Type*} [Field F] [Fintype F]

theorem gaussSum_normSq {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : AddChar.IsPrimitive ψ) :
    Complex.normSq (gaussSum χ ψ) = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card (R' := ℂ) hχ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm : ((Complex.normSq (gaussSum χ ψ) : ℝ) : ℂ) = (Fintype.card F : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [Complex.star_def, mul_comm] using h
  exact_mod_cast hnorm

theorem gaussSum_norm {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : AddChar.IsPrimitive ψ) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, gaussSum_normSq hχ hψ]
  calc ‖gaussSum χ ψ‖ = Real.sqrt (‖gaussSum χ ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg (gaussSum χ ψ))).symm
    _ = Real.sqrt (Fintype.card F) := by rw [hsq]

def gaussPhase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℝ := Complex.arg (gaussSum χ ψ)

theorem gaussSum_eq_norm_mul_exp {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : AddChar.IsPrimitive ψ) :
    gaussSum χ ψ = ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) *
      Complex.exp (Complex.I * gaussPhase χ ψ) := by
  have h := Complex.norm_mul_exp_arg_mul_I (gaussSum χ ψ)
  rw [gaussSum_norm hχ hψ] at h
  rw [gaussPhase]
  calc gaussSum χ ψ
      = ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) *
          Complex.exp (Complex.arg (gaussSum χ ψ) * Complex.I) := h.symm
    _ = ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) *
          Complex.exp (Complex.I * Complex.arg (gaussSum χ ψ)) := by
        congr 1
        rw [mul_comm]

def gaussPhaseCost (ε : ℝ) (Q : ℕ) : ℝ := (1 / ε) * (Real.log Q) ^ 2

theorem gaussSum_approx_error {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : AddChar.IsPrimitive ψ) {γhat : ℝ} (hε : |γhat - gaussPhase χ ψ| ≤ 1) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ) * Complex.exp (Complex.I * γhat) -
        gaussSum χ ψ‖ ≤
      2 * Real.sqrt (Fintype.card F) * |γhat - gaussPhase χ ψ| := by
  rw [gaussSum_eq_norm_mul_exp hχ hψ]
  have hfac : ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) * Complex.exp (Complex.I * γhat) -
        ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) * Complex.exp (Complex.I * gaussPhase χ ψ)
      = ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * γhat) - Complex.exp (Complex.I * gaussPhase χ ψ)) := by
    ring
  rw [hfac, norm_mul]
  have hnorm1 : ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)‖ = Real.sqrt (Fintype.card F) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hnorm1]
  have hexp : Complex.exp (Complex.I * γhat) - Complex.exp (Complex.I * gaussPhase χ ψ)
      = Complex.exp (Complex.I * gaussPhase χ ψ) *
        (Complex.exp (Complex.I * ((γhat - gaussPhase χ ψ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hexp, norm_mul]
  have hunit : ‖Complex.exp (Complex.I * gaussPhase χ ψ)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hunit, one_mul]
  have hbound : ‖Complex.exp (Complex.I * ((γhat - gaussPhase χ ψ : ℝ) : ℂ)) - 1‖
      ≤ 2 * |γhat - gaussPhase χ ψ| := by
    have hx : ‖Complex.I * ((γhat - gaussPhase χ ψ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hε
    have hle := Complex.norm_exp_sub_one_le hx
    have hnormI : ‖Complex.I * ((γhat - gaussPhase χ ψ : ℝ) : ℂ)‖ =
        |γhat - gaussPhase χ ψ| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnormI] at hle
    exact hle
  calc Real.sqrt (Fintype.card F) *
        ‖Complex.exp (Complex.I * ((γhat - gaussPhase χ ψ : ℝ) : ℂ)) - 1‖
      ≤ Real.sqrt (Fintype.card F) * (2 * |γhat - gaussPhase χ ψ|) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (Fintype.card F) * |γhat - gaussPhase χ ψ| := by ring

end Qatlib.Papers.WeightEnum07.GaussRecovery
