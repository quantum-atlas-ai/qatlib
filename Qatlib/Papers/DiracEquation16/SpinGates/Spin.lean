/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CliffordWalk.Euler
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiracEquation16.SpinGates

open Matrix NormedSpace

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sCoeff : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def Smat (α β : Matrix ι ι ℂ) : Matrix ι ι ℂ := sCoeff • (β + α)

lemma sCoeff_sq : sCoeff * sCoeff = (1 / 2 : ℂ) := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold sCoeff
  rw [← mul_inv, h]
  norm_num

lemma beta_add_alpha_sq {α β : Matrix ι ι ℂ} (hα : α * α = 1) (hβ : β * β = 1)
    (hac : α * β = -(β * α)) : (β + α) * (β + α) = (2 : ℂ) • 1 := by
  rw [add_mul, mul_add, mul_add, hβ, hα, hac, two_smul]
  abel

theorem Smat_mul_Smat {α β : Matrix ι ι ℂ} (hα : α * α = 1) (hβ : β * β = 1)
    (hac : α * β = -(β * α)) : Smat α β * Smat α β = 1 := by
  unfold Smat
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, beta_add_alpha_sq hα hβ hac,
    sCoeff_sq, smul_smul, show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]

lemma sandwich {x y : Matrix ι ι ℂ} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = -(y * x)) : (x + y) * x * (x + y) = (2 : ℂ) • y := by
  rw [add_mul, add_mul, mul_add, mul_add]
  have h1 : (x * x) * x = x := by rw [hx, one_mul]
  have h2 : (x * x) * y = y := by rw [hx, one_mul]
  have h3 : (y * x) * x = y := by rw [mul_assoc y x x, hx, mul_one]
  have h4 : (y * x) * y = -x := by
    rw [mul_assoc y x y, hxy, mul_neg, ← mul_assoc, hy, one_mul]
  rw [h1, h2, h3, h4, two_smul]
  abel

theorem Smat_mul_alpha_mul {α β : Matrix ι ι ℂ} (hα : α * α = 1) (hβ : β * β = 1)
    (hac : α * β = -(β * α)) : Smat α β * α * Smat α β = β := by
  unfold Smat
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, add_comm β α,
    sandwich hα hβ hac, sCoeff_sq, smul_smul,
    show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]

theorem Smat_mul_beta_mul {α β : Matrix ι ι ℂ} (hα : α * α = 1) (hβ : β * β = 1)
    (hac : α * β = -(β * α)) : Smat α β * β * Smat α β = α := by
  unfold Smat
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sandwich hβ hα (by rw [hac, neg_neg]), sCoeff_sq, smul_smul,
    show ((1 / 2 : ℂ) * 2) = 1 by norm_num, one_smul]

omit [Fintype ι] [DecidableEq ι] in

theorem Smat_hermitian {α β : Matrix ι ι ℂ} (hα : αᴴ = α) (hβ : βᴴ = β) :
    (Smat α β)ᴴ = Smat α β := by
  unfold Smat
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hα, hβ]
  congr 1
  unfold sCoeff
  simp

end Abstract

section ExpConj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exp_conj_of_sq_one (U A : Matrix ι ι ℂ) (hU : U * U = 1) :
    exp (U * A * U) = U * exp A * U := by
  have h := Matrix.exp_units_conj (⟨U, U, hU, hU⟩ : (Matrix ι ι ℂ)ˣ) A
  simpa using h

end ExpConj

section Rotation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Q_eq_exp_alpha {α β D : Matrix ι ι ℂ} (hα : α * α = 1) (hβ : β * β = 1)
    (hac : α * β = -(β * α)) (hD : Commute D (Smat α β)) (θ : ℂ) :
    Smat α β * exp (-θ • (β * D)) * Smat α β = exp (-θ • (α * D)) := by
  have hS2 : Smat α β * Smat α β = 1 := Smat_mul_Smat hα hβ hac
  have hconj : Smat α β * β * Smat α β = α := Smat_mul_beta_mul hα hβ hac
  have hmiddle : Smat α β * (β * D) * Smat α β = α * D := by
    rw [← mul_assoc (Smat α β) β D, mul_assoc (Smat α β * β) D (Smat α β),
      hD.eq, ← mul_assoc, hconj]
  have hMM : Smat α β * (-θ • (β * D)) * Smat α β = -θ • (α * D) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hmiddle]
  rw [← hMM, ← exp_conj_of_sq_one (Smat α β) (-θ • (β * D)) hS2]

end Rotation

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_of_skew {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (θ : ℂ)
    (hθ : star θ = -θ) : (exp (θ • H))ᴴ * exp (θ • H) = 1 := by
  have hstar : (exp (θ • H))ᴴ = exp (-θ • H) := by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH, hθ]
  rw [hstar]
  have hcomm : Commute (-θ • H) (θ • H) := by
    show (-θ • H) * (θ • H) = (θ • H) * (-θ • H)
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_smul]
    congr 1
    ring
  have h0 : (-θ • H) + (θ • H) = 0 := by
    rw [← add_smul, neg_add_cancel, zero_smul]
  rw [← Matrix.exp_add_of_commute (-θ • H) (θ • H) hcomm, h0]
  exact NormedSpace.exp_zero

theorem T_unitary {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (dt : ℝ) :
    (exp ((Complex.I * (dt : ℂ)) • H))ᴴ * exp ((Complex.I * (dt : ℂ)) • H) = 1 := by
  have hθ : star (Complex.I * (dt : ℂ)) = -(Complex.I * (dt : ℂ)) := by
    apply Complex.ext <;> simp
  exact unitary_of_skew hH _ hθ

theorem unitary_conj {U T : Matrix ι ι ℂ} (hU2 : U * U = 1) (hUH : Uᴴ = U)
    (hT : Tᴴ * T = 1) : (U * T * U)ᴴ * (U * T * U) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hUH]
  calc (U * (Tᴴ * U)) * ((U * T) * U)
      = U * (Tᴴ * (U * U)) * T * U := by noncomm_ring
    _ = U * (Tᴴ * 1) * T * U := by rw [hU2]
    _ = U * Tᴴ * T * U := by rw [mul_one]
    _ = U * (Tᴴ * T) * U := by noncomm_ring
    _ = U * 1 * U := by rw [hT]
    _ = 1 := by rw [mul_one, hU2]

theorem Q_unitary {α β : Matrix ι ι ℂ} (hα : α * α = 1) (hβ : β * β = 1)
    (hac : α * β = -(β * α)) (hαH : αᴴ = α) (hβH : βᴴ = β)
    {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (dt : ℝ) :
    (Smat α β * exp ((Complex.I * (dt : ℂ)) • H) * Smat α β)ᴴ *
      (Smat α β * exp ((Complex.I * (dt : ℂ)) • H) * Smat α β) = 1 :=
  unitary_conj (Smat_mul_Smat hα hβ hac) (Smat_hermitian hαH hβH) (T_unitary hH dt)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_mul {A B : Matrix ι ι ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc (Bᴴ * Aᴴ) * (A * B) = Bᴴ * (Aᴴ * A) * B := by noncomm_ring
    _ = Bᴴ * 1 * B := by rw [hA]
    _ = Bᴴ * B := by rw [mul_one]
    _ = 1 := hB

end Unitary

namespace FourD

def beta4 : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

def alphaX4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

def alphaY4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -Complex.I; 0, 0, Complex.I, 0; 0, -Complex.I, 0, 0;
     Complex.I, 0, 0, 0]

def alphaZ4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0]

lemma beta4_sq : beta4 * beta4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [beta4, Matrix.mul_apply, Fin.sum_univ_four]

lemma alphaX4_sq : alphaX4 * alphaX4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaX4, Matrix.mul_apply, Fin.sum_univ_four]

lemma alphaY4_sq : alphaY4 * alphaY4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaY4, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

lemma alphaZ4_sq : alphaZ4 * alphaZ4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaZ4, Matrix.mul_apply, Fin.sum_univ_four]

lemma alphaX4_anticomm : alphaX4 * beta4 = -(beta4 * alphaX4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaX4, beta4, Matrix.mul_apply, Fin.sum_univ_four]

lemma alphaY4_anticomm : alphaY4 * beta4 = -(beta4 * alphaY4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaY4, beta4, Matrix.mul_apply, Fin.sum_univ_four]

lemma alphaZ4_anticomm : alphaZ4 * beta4 = -(beta4 * alphaZ4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaZ4, beta4, Matrix.mul_apply, Fin.sum_univ_four]

lemma beta4_hermitian : beta4ᴴ = beta4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beta4]

lemma alphaX4_hermitian : alphaX4ᴴ = alphaX4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alphaX4]

lemma alphaY4_hermitian : alphaY4ᴴ = alphaY4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alphaY4, Complex.conj_I]

lemma alphaZ4_hermitian : alphaZ4ᴴ = alphaZ4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alphaZ4]

theorem Sx_mul_Sx : Smat alphaX4 beta4 * Smat alphaX4 beta4 = 1 :=
  Smat_mul_Smat alphaX4_sq beta4_sq alphaX4_anticomm

theorem Sy_mul_Sy : Smat alphaY4 beta4 * Smat alphaY4 beta4 = 1 :=
  Smat_mul_Smat alphaY4_sq beta4_sq alphaY4_anticomm

theorem Sz_mul_Sz : Smat alphaZ4 beta4 * Smat alphaZ4 beta4 = 1 :=
  Smat_mul_Smat alphaZ4_sq beta4_sq alphaZ4_anticomm

theorem Sx_conj_alpha : Smat alphaX4 beta4 * alphaX4 * Smat alphaX4 beta4 = beta4 :=
  Smat_mul_alpha_mul alphaX4_sq beta4_sq alphaX4_anticomm

theorem Sy_conj_alpha : Smat alphaY4 beta4 * alphaY4 * Smat alphaY4 beta4 = beta4 :=
  Smat_mul_alpha_mul alphaY4_sq beta4_sq alphaY4_anticomm

theorem Sz_conj_alpha : Smat alphaZ4 beta4 * alphaZ4 * Smat alphaZ4 beta4 = beta4 :=
  Smat_mul_alpha_mul alphaZ4_sq beta4_sq alphaZ4_anticomm

theorem Sx_hermitian : (Smat alphaX4 beta4)ᴴ = Smat alphaX4 beta4 :=
  Smat_hermitian alphaX4_hermitian beta4_hermitian

theorem Sy_hermitian : (Smat alphaY4 beta4)ᴴ = Smat alphaY4 beta4 :=
  Smat_hermitian alphaY4_hermitian beta4_hermitian

theorem Sz_hermitian : (Smat alphaZ4 beta4)ᴴ = Smat alphaZ4 beta4 :=
  Smat_hermitian alphaZ4_hermitian beta4_hermitian

theorem Qx_eq_exp_alpha (D : Matrix (Fin 4) (Fin 4) ℂ) (hD : Commute D (Smat alphaX4 beta4))
    (θ : ℂ) :
    Smat alphaX4 beta4 * exp (-θ • (beta4 * D)) * Smat alphaX4 beta4 =
      exp (-θ • (alphaX4 * D)) :=
  Q_eq_exp_alpha alphaX4_sq beta4_sq alphaX4_anticomm hD θ

theorem Qy_eq_exp_alpha (D : Matrix (Fin 4) (Fin 4) ℂ) (hD : Commute D (Smat alphaY4 beta4))
    (θ : ℂ) :
    Smat alphaY4 beta4 * exp (-θ • (beta4 * D)) * Smat alphaY4 beta4 =
      exp (-θ • (alphaY4 * D)) :=
  Q_eq_exp_alpha alphaY4_sq beta4_sq alphaY4_anticomm hD θ

theorem Qz_eq_exp_alpha (D : Matrix (Fin 4) (Fin 4) ℂ) (hD : Commute D (Smat alphaZ4 beta4))
    (θ : ℂ) :
    Smat alphaZ4 beta4 * exp (-θ • (beta4 * D)) * Smat alphaZ4 beta4 =
      exp (-θ • (alphaZ4 * D)) :=
  Q_eq_exp_alpha alphaZ4_sq beta4_sq alphaZ4_anticomm hD θ

theorem Qx_unitary {H : Matrix (Fin 4) (Fin 4) ℂ} (hH : Hᴴ = H) (dt : ℝ) :
    (Smat alphaX4 beta4 * exp ((Complex.I * (dt : ℂ)) • H) * Smat alphaX4 beta4)ᴴ *
      (Smat alphaX4 beta4 * exp ((Complex.I * (dt : ℂ)) • H) * Smat alphaX4 beta4) = 1 :=
  Q_unitary alphaX4_sq beta4_sq alphaX4_anticomm alphaX4_hermitian beta4_hermitian hH dt

theorem Qy_unitary {H : Matrix (Fin 4) (Fin 4) ℂ} (hH : Hᴴ = H) (dt : ℝ) :
    (Smat alphaY4 beta4 * exp ((Complex.I * (dt : ℂ)) • H) * Smat alphaY4 beta4)ᴴ *
      (Smat alphaY4 beta4 * exp ((Complex.I * (dt : ℂ)) • H) * Smat alphaY4 beta4) = 1 :=
  Q_unitary alphaY4_sq beta4_sq alphaY4_anticomm alphaY4_hermitian beta4_hermitian hH dt

theorem Qz_unitary {H : Matrix (Fin 4) (Fin 4) ℂ} (hH : Hᴴ = H) (dt : ℝ) :
    (Smat alphaZ4 beta4 * exp ((Complex.I * (dt : ℂ)) • H) * Smat alphaZ4 beta4)ᴴ *
      (Smat alphaZ4 beta4 * exp ((Complex.I * (dt : ℂ)) • H) * Smat alphaZ4 beta4) = 1 :=
  Q_unitary alphaZ4_sq beta4_sq alphaZ4_anticomm alphaZ4_hermitian beta4_hermitian hH dt

theorem alphaY4_alphaZ4_anticomm : alphaY4 * alphaZ4 = -(alphaZ4 * alphaY4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alphaY4, alphaZ4, Matrix.mul_apply, Fin.sum_univ_four]

end FourD

end Qatlib.Papers.DiracEquation16.SpinGates
