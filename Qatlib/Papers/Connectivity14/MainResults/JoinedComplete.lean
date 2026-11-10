/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.Connectivity14.MainResults.TwoLevel

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped Matrix Matrix.Norms.L2Operator

namespace Qatlib.Papers.Connectivity14.MainResults

def joinedDelta (N : ℝ) : ℝ := Real.sqrt (2 / N)

def joinedEff3 (N : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(-1 : ℂ), -((joinedDelta N : ℝ) : ℂ), 0;
     -((joinedDelta N : ℝ) : ℂ), (-1 : ℂ), 0;
     0, 0, (-1 : ℂ)]

def halfSqrt : ℝ := (Real.sqrt 2)⁻¹

def jPsi0 : Fin 3 → ℂ := ![(halfSqrt : ℂ), (halfSqrt : ℂ), 0]

def jPsi1 : Fin 3 → ℂ := ![0, 0, 1]

def jPsi2 : Fin 3 → ℂ := ![-(halfSqrt : ℂ), (halfSqrt : ℂ), 0]

def joinedInit : Fin 3 → ℂ := ![0, (halfSqrt : ℂ), (halfSqrt : ℂ)]

theorem halfSqrt_sq : halfSqrt ^ 2 = 2⁻¹ := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num)]
  unfold halfSqrt
  rw [inv_pow, Real.sq_sqrt (by norm_num)]

theorem joinedEff3_eigen_psi0 (N : ℝ) :
    joinedEff3 N *ᵥ jPsi0 = ((-1 - joinedDelta N : ℝ) : ℂ) • jPsi0 := by
  ext i
  fin_cases i <;>
    simp [joinedEff3, jPsi0, Matrix.mulVec] <;> ring

theorem joinedEff3_eigen_psi1 (N : ℝ) :
    joinedEff3 N *ᵥ jPsi1 = ((-1 : ℝ) : ℂ) • jPsi1 := by
  ext i
  fin_cases i <;> simp [joinedEff3, jPsi1, Matrix.mulVec]

theorem joinedEff3_eigen_psi2 (N : ℝ) :
    joinedEff3 N *ᵥ jPsi2 = ((-1 + joinedDelta N : ℝ) : ℂ) • jPsi2 := by
  ext i
  fin_cases i <;>
    simp [joinedEff3, jPsi2, Matrix.mulVec] <;> ring

theorem joinedInit_decomp :
    joinedInit =
      (2⁻¹ : ℂ) • jPsi0 + (halfSqrt : ℂ) • jPsi1 + (2⁻¹ : ℂ) • jPsi2 := by
  ext i
  fin_cases i <;>
    simp [joinedInit, jPsi0, jPsi1, jPsi2] <;> ring

theorem joined_evolution_mulVec (N t : ℝ) :
    HamiltonianEvolution (joinedEff3 N) t *ᵥ joinedInit =
      (2⁻¹ : ℂ) •
          (Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 - joinedDelta N : ℝ) : ℂ)) • jPsi0) +
        (halfSqrt : ℂ) •
          (Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ)) • jPsi1) +
        (2⁻¹ : ℂ) •
          (Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 + joinedDelta N : ℝ) : ℂ)) • jPsi2) := by
  rw [joinedInit_decomp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_smul,
    hamiltonianEvolution_eigenvector _ _ _ _ (joinedEff3_eigen_psi0 N),
    hamiltonianEvolution_eigenvector _ _ _ _ (joinedEff3_eigen_psi1 N),
    hamiltonianEvolution_eigenvector _ _ _ _ (joinedEff3_eigen_psi2 N)]

theorem joined_amplitude_closed (N t : ℝ) :
    (2⁻¹ : ℂ) *
        (Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 - joinedDelta N : ℝ) : ℂ)) *
            (halfSqrt : ℂ) +
          Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 + joinedDelta N : ℝ) : ℂ)) *
            (-(halfSqrt : ℂ))) =
      Complex.I * Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ)) *
        ((halfSqrt : ℂ) * ((Real.sin (joinedDelta N * t) : ℝ) : ℂ)) := by
  have ha : (-Complex.I * (t : ℂ)) * ((-1 - joinedDelta N : ℝ) : ℂ) =
      (-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ) + ((joinedDelta N * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hb : (-Complex.I * (t : ℂ)) * ((-1 + joinedDelta N : ℝ) : ℂ) =
      (-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ) + ((-(joinedDelta N * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ha, hb, Complex.exp_add, Complex.exp_add, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem joined_amplitude (N t : ℝ) :
    (HamiltonianEvolution (joinedEff3 N) t *ᵥ joinedInit) 0 =
      Complex.I * Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ)) *
        ((halfSqrt : ℂ) * ((Real.sin (joinedDelta N * t) : ℝ) : ℂ)) := by
  rw [joined_evolution_mulVec]
  have h0 : jPsi0 0 = (halfSqrt : ℂ) := rfl
  have h1 : jPsi1 0 = (0 : ℂ) := rfl
  have h2 : jPsi2 0 = (-(halfSqrt : ℂ)) := rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, h1, h2, mul_zero, add_zero]
  rw [← mul_add]
  exact joined_amplitude_closed N t

theorem joined_success_prob (N t : ℝ) :
    ‖(HamiltonianEvolution (joinedEff3 N) t *ᵥ joinedInit) 0‖ ^ 2 =
      2⁻¹ * Real.sin (joinedDelta N * t) ^ 2 := by
  rw [joined_amplitude, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hexp : ‖Complex.exp ((-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ))‖ = 1 := by
    rw [show (-Complex.I * (t : ℂ)) * ((-1 : ℝ) : ℂ) = ((t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, one_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, sq_abs, sq_abs, halfSqrt_sq]

theorem joined_peak_time (N : ℝ) (hN : 0 < N) :
    joinedDelta N * (Real.pi / 2 * Real.sqrt (N / 2)) = Real.pi / 2 := by
  have hprod : joinedDelta N * Real.sqrt (N / 2) = 1 := by
    unfold joinedDelta
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / N)]
    have h : 2 / N * (N / 2) = 1 := by
      field_simp
    rw [h, Real.sqrt_one]
  calc joinedDelta N * (Real.pi / 2 * Real.sqrt (N / 2))
      = Real.pi / 2 * (joinedDelta N * Real.sqrt (N / 2)) := by ring
    _ = Real.pi / 2 := by rw [hprod]; ring

theorem joined_success_at_peak (N : ℝ) (hN : 0 < N) :
    ‖(HamiltonianEvolution (joinedEff3 N) (Real.pi / 2 * Real.sqrt (N / 2)) *ᵥ
        joinedInit) 0‖ ^ 2 = 2⁻¹ := by
  rw [joined_success_prob, joined_peak_time N hN, Real.sin_pi_div_two]
  norm_num

theorem joined_runtime_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun N : ℝ => Real.pi / 2 * Real.sqrt (N / 2))
      (fun N : ℝ => Real.sqrt N) := by
  have hcongr : (fun N : ℝ => Real.pi / 2 * Real.sqrt (N / 2))
      =ᶠ[Filter.atTop] (fun N : ℝ => (Real.pi / 2 / Real.sqrt 2) * Real.sqrt N) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with N hN
    rw [Real.sqrt_div (le_of_lt hN) 2]
    ring
  have hc : (Real.pi / 2 / Real.sqrt 2) ≠ 0 := by positivity
  have hbase : (fun N : ℝ => (Real.pi / 2 / Real.sqrt 2) * Real.sqrt N)
      =Θ[Filter.atTop] (fun N : ℝ => Real.sqrt N) :=
    (Asymptotics.isTheta_refl (fun N : ℝ => Real.sqrt N) Filter.atTop).const_mul_left hc
  exact ⟨hbase.1.congr' hcongr.symm (Filter.EventuallyEq.refl _ _),
    hbase.2.congr' (Filter.EventuallyEq.refl _ _) hcongr.symm⟩

def joinedH5 (N : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![(-1 : ℂ), -((joinedDelta N : ℝ) : ℂ), -(((2 / N : ℝ) : ℂ)), 0, 0;
     -((joinedDelta N : ℝ) : ℂ), (-1 : ℂ), -((joinedDelta N : ℝ) : ℂ), 0, 0;
     -(((2 / N : ℝ) : ℂ)), -((joinedDelta N : ℝ) : ℂ), 0, -(((2 / N : ℝ) : ℂ)), 0;
     0, 0, -(((2 / N : ℝ) : ℂ)), 0, -((joinedDelta N : ℝ) : ℂ);
     0, 0, 0, -((joinedDelta N : ℝ) : ℂ), (-1 : ℂ)]

def blockIdx : Fin 3 → Fin 5 := ![0, 1, 4]

theorem sqrt_ratio (N : ℝ) (hN : 0 < N) :
    (2 / N) * Real.sqrt (N / 2) = Real.sqrt (2 / N) := by
  have hsq : ((2 / N) * Real.sqrt (N / 2)) ^ 2 = 2 / N := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N / 2)]
    field_simp
  have hnn : (0 : ℝ) ≤ (2 / N) * Real.sqrt (N / 2) := by positivity
  rw [← Real.sqrt_sq hnn, hsq]

theorem joinedH5_block (N : ℝ) :
    (joinedH5 N).submatrix blockIdx blockIdx = joinedEff3 N := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Qatlib.Papers.Connectivity14.MainResults
