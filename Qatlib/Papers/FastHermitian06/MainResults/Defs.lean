/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder

namespace Qatlib.Papers.FastHermitian06.MainResults.Defs

abbrev State2 := Fin 2 → ℂ

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def ket0 : State2 := ![1, 0]

def ket1 : State2 := ![0, 1]

def parity : Mat2 := !![0, 1; 1, 0]

def conjT (M : Mat2) : Mat2 := M.map (starRingEnd ℂ)

def PT (M : Mat2) : Mat2 := parity * conjT M * parity

def cis (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

theorem cis_eq (θ : ℝ) :
    cis θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  unfold cis
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem cis_neg (θ : ℝ) :
    cis (-θ) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [cis_eq]
  simp [Real.cos_neg, Real.sin_neg]
  ring

theorem I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  rw [pow_two, Complex.I_mul_I]

theorem cis_mul_cis_neg (θ : ℝ) : cis θ * cis (-θ) = 1 := by
  unfold cis
  rw [← Complex.exp_add]
  have h : Complex.I * (θ : ℂ) + Complex.I * ((-θ : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [h, Complex.exp_zero]

theorem conj_cis (θ : ℝ) : starRingEnd ℂ (cis θ) = cis (-θ) := by
  unfold cis
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I, Complex.conj_ofReal]

def H2 (r s θ : ℝ) : Mat2 :=
  !![(r : ℂ) * cis θ, (s : ℂ); (s : ℂ), (r : ℂ) * cis (-θ)]

def omegaSq (r s θ : ℝ) : ℝ := 4 * s ^ 2 - 4 * r ^ 2 * (Real.sin θ) ^ 2

def omega (r s θ : ℝ) : ℝ := Real.sqrt (omegaSq r s θ)

def unbrokenPT (r s θ : ℝ) : Prop := 0 < omegaSq r s θ

def alphaAngle (r s θ : ℝ) : ℝ := Real.arcsin ((r / s) * Real.sin θ)

theorem omega_sq (r s θ : ℝ) (h : unbrokenPT r s θ) :
    omega r s θ ^ 2 = omegaSq r s θ :=
  Real.sq_sqrt (le_of_lt h)

theorem H2_pt_symmetric (r s θ : ℝ) : PT (H2 r s θ) = H2 r s θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PT, parity, conjT, H2, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.map_apply, conj_cis, Complex.conj_ofReal]

theorem H2_centered (r s θ : ℝ) :
    H2 r s θ - (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2)
      = !![ (Real.sin θ : ℂ) * (r : ℂ) * Complex.I, (s : ℂ);
            (s : ℂ), -((Real.sin θ : ℂ) * (r : ℂ) * Complex.I) ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H2, cis_eq, Matrix.smul_apply] <;>
    ring

theorem H2_centered_sq (r s θ : ℝ) :
    (H2 r s θ - (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2)) *
        (H2 r s θ - (((r * Real.cos θ : ℝ) : ℂ)) • (1 : Mat2))
      = (((s : ℂ) ^ 2 - (r : ℂ) ^ 2 * (Real.sin θ) ^ 2)) • (1 : Mat2) := by
  rw [H2_centered]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  all_goals ring_nf
  all_goals rw [show Complex.I ^ 2 = (-1 : ℂ) from I_sq]
  all_goals ring

theorem H2_trace (r s θ : ℝ) :
    (H2 r s θ).trace = ((2 * r * Real.cos θ : ℝ) : ℂ) := by
  simp [H2, Matrix.trace, cis_eq, Fin.sum_univ_two]
  ring

theorem H2_det (r s θ : ℝ) : (H2 r s θ).det = ((r : ℂ) ^ 2 - (s : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp only [H2, Matrix.of_apply]
  have h : cis θ * cis (-θ) = 1 := cis_mul_cis_neg θ
  calc (r : ℂ) * cis θ * ((r : ℂ) * cis (-θ)) - (s : ℂ) * (s : ℂ)
      = (r : ℂ) ^ 2 * (cis θ * cis (-θ)) - (s : ℂ) ^ 2 := by ring
    _ = (r : ℂ) ^ 2 - (s : ℂ) ^ 2 := by rw [h]; ring

end Qatlib.Papers.FastHermitian06.MainResults.Defs
