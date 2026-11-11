/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Phase and basis-change gate widgets

This module defines the phase and basis-change matrices used by the quantum-walk gate
construction in [Childs2009]. It proves their unitary identities and a Hadamard synthesis
identity, then evaluates the widget transmission and reflection coefficients at momentum `-π /
4`.

## Main statements

* `Uphase_unitary`: The phase gate is unitary.
* `Ubasis_unitary`: The basis-change gate is unitary.
* `Uphase_sq_Ubasis_Uphase_sq`: Recover the Hadamard matrix up to a scalar phase.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.Gates

open Matrix

set_option autoImplicit false

/-- The eighth root of unity `exp(iπ / 4)`. -/
noncomputable def zeta : ℂ :=
  Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)

/-- The complex embedding of the real number `1 / √2`. -/
noncomputable def invSqrt2 : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- The diagonal phase matrix with diagonal entries one and `zeta`. -/
noncomputable def Uphase : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, zeta]

/-- The basis-change matrix `-invSqrt2` times the matrix with diagonal entries `i` and
off-diagonal entries one. -/
noncomputable def Ubasis : Matrix (Fin 2) (Fin 2) ℂ :=
  (-invSqrt2) • !![Complex.I, 1; 1, Complex.I]

/-- The normalized two-dimensional Hadamard matrix. -/
noncomputable def hadamard2 : Matrix (Fin 2) (Fin 2) ℂ :=
  invSqrt2 • !![1, 1; 1, -1]

/-- The square of `zeta` is `i`. -/
theorem zeta_mul_self : zeta * zeta = Complex.I := by
  unfold zeta
  rw [← Complex.exp_add]
  have h : (Real.pi / 4 : ℝ) * Complex.I + (Real.pi / 4 : ℝ) * Complex.I =
      (Real.pi / 2 : ℝ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- The product of `zeta` and its complex conjugate is one. -/
theorem zeta_mul_conj : zeta * (starRingEnd ℂ) zeta = 1 := by
  have hns : Complex.normSq zeta = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    unfold zeta
    rw [Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [Complex.mul_conj, hns]
  norm_num

/-- The product of the complex conjugate of `zeta` and `zeta` is one. -/
theorem zeta_conj_mul : (starRingEnd ℂ) zeta * zeta = 1 := by
  rw [mul_comm]
  exact zeta_mul_conj

/-- The cube of the imaginary unit is its negative. -/
theorem I_cube : Complex.I ^ 3 = -Complex.I := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, Complex.I_mul_I]
  ring

/-- The square of `invSqrt2` is `1 / 2`. -/
theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = (1 / 2 : ℂ) := by
  unfold invSqrt2
  rw [← Complex.ofReal_mul]
  have h : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h]
  norm_num

/-- The square of the phase matrix is the diagonal matrix with entries one and `i`. -/
theorem Uphase_mul_self : Uphase * Uphase = !![1, 0; 0, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Uphase, Matrix.mul_apply, Fin.sum_univ_two, zeta_mul_self]

/-- The phase matrix satisfies both unitary identities [Childs2009]. -/
theorem Uphase_unitary : Uphase * Uphaseᴴ = 1 ∧ Uphaseᴴ * Uphase = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Uphase, Matrix.mul_apply, Fin.sum_univ_two, zeta_mul_conj, zeta_conj_mul]

/-- The basis-change matrix satisfies both unitary identities [Childs2009]. -/
theorem Ubasis_unitary : Ubasis * Ubasisᴴ = 1 ∧ Ubasisᴴ * Ubasis = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Ubasis, Matrix.mul_apply, Fin.sum_univ_two, invSqrt2, Complex.ext_iff]
  all_goals
    (have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
     have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
     nlinarith [h2, hpos])

/-- Placing `Ubasis` between two copies of `Uphase * Uphase` yields `-i` times the Hadamard
matrix [Childs2009]. -/
theorem Uphase_sq_Ubasis_Uphase_sq :
    Uphase * Uphase * Ubasis * (Uphase * Uphase) = (-Complex.I) • hadamard2 := by
  rw [Uphase_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ubasis, hadamard2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    ring_nf
    try rw [I_cube]
    try ring

/-- The momentum-dependent phase-widget transmission coefficient. -/
noncomputable def phaseTrans (k : ℝ) : ℂ :=
  8 / (8 + Complex.I * (Real.cos (2 * k) / (Real.sin k) ^ 3) / Real.cos k)

/-- The common complex denominator for the basis-widget transmission and reflection
coefficients. -/
noncomputable def basisDenom (k : ℝ) : ℂ :=
  2 * (Real.cos k : ℂ) + Complex.I * ((Real.sin (3 * k) - Real.sin k : ℝ) : ℂ)

/-- The diagonal transmission coefficient of the basis widget at momentum `k`. -/
noncomputable def basisT00 (k : ℝ) : ℂ :=
  Complex.exp ((k : ℂ) * Complex.I) * ((Real.cos k : ℂ) + Complex.I * (Real.sin (3 * k) : ℂ)) /
    basisDenom k

/-- The off-diagonal transmission coefficient `-1 / basisDenom k` of the basis widget. -/
noncomputable def basisT01 (k : ℝ) : ℂ := -1 / basisDenom k

/-- The momentum-dependent reflection coefficient of the basis widget. -/
noncomputable def basisRefl (k : ℝ) : ℂ :=
  -(Complex.exp ((k : ℂ) * Complex.I) * (Real.cos (2 * k) : ℂ)) / basisDenom k

/-- The phase-widget transmission coefficient equals one at momentum `-π / 4` [Childs2009]. -/
theorem phaseTrans_at_working_momentum : phaseTrans (-(Real.pi / 4)) = 1 := by
  unfold phaseTrans
  have hcos : Real.cos (2 * (-(Real.pi / 4))) = 0 := by
    rw [show 2 * (-(Real.pi / 4)) = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  rw [hcos]
  simp

/-- The cosine of `-π / 4` is `√2 / 2`. -/
theorem cos_neg_pi_div_four : Real.cos (-(Real.pi / 4)) = Real.sqrt 2 / 2 := by
  rw [Real.cos_neg, Real.cos_pi_div_four]

/-- The sine of `-π / 4` is `-√2 / 2`. -/
theorem sin_neg_pi_div_four : Real.sin (-(Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  rw [Real.sin_neg, Real.sin_pi_div_four]

/-- The sine of three times `-π / 4` is `-√2 / 2`. -/
theorem sin_three_neg_pi_div_four :
    Real.sin (3 * (-(Real.pi / 4))) = -(Real.sqrt 2 / 2) := by
  have h : 3 * (-(Real.pi / 4)) = -(Real.pi - Real.pi / 4) := by ring
  rw [h, Real.sin_neg, Real.sin_pi_sub, Real.sin_pi_div_four]

/-- The cosine of twice `-π / 4` is zero. -/
theorem cos_two_neg_pi_div_four :
    Real.cos (2 * (-(Real.pi / 4))) = 0 := by
  rw [show 2 * (-(Real.pi / 4)) = -(Real.pi / 2) by ring, Real.cos_neg,
    Real.cos_pi_div_two]

/-- The basis-widget denominator equals complex `√2` at momentum `-π / 4`. -/
theorem basisDenom_at_working_momentum :
    basisDenom (-(Real.pi / 4)) = (Real.sqrt 2 : ℂ) := by
  unfold basisDenom
  rw [cos_neg_pi_div_four, sin_three_neg_pi_div_four, sin_neg_pi_div_four]
  push_cast
  ring

/-- The off-diagonal basis-widget transmission equals `-invSqrt2` at momentum `-π / 4`
[Childs2009]. -/
theorem basisT01_at_working_momentum :
    basisT01 (-(Real.pi / 4)) = -invSqrt2 := by
  unfold basisT01 invSqrt2
  rw [basisDenom_at_working_momentum]
  have hmain : (-1 : ℂ) / (Real.sqrt 2 : ℂ) =
      -(((1 : ℝ) / Real.sqrt 2 : ℝ) : ℂ) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div,
      show ((-1 : ℝ) / Real.sqrt 2) = -((1 : ℝ) / Real.sqrt 2) by ring]
    simp
  exact hmain

/-- The basis-widget reflection coefficient vanishes at momentum `-π / 4` [Childs2009]. -/
theorem basisRefl_at_working_momentum :
    basisRefl (-(Real.pi / 4)) = 0 := by
  unfold basisRefl
  rw [cos_two_neg_pi_div_four, basisDenom_at_working_momentum]
  simp

/-- The complex exponential `exp(-iπ / 4)` is `(√2 / 2) * (1 - i)`. -/
theorem exp_neg_pi_div_four :
    Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, cos_neg_pi_div_four, sin_neg_pi_div_four]
  push_cast
  ring

end Qatlib.Papers.UniversalWalk08.MainResults.Gates
