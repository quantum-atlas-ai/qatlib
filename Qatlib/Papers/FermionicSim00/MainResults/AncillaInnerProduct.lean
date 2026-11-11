/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Ancilla trace identities for inner-product estimation

`ancillaRho` is the equal-superposition ancilla state, and `controlledUV` places arbitrary
system matrices in its two diagonal blocks. Matrix-unit and trace calculations show how the
combined ancilla X and Y observable recovers `Matrix.trace (Uᴴ * V * ρ)`.

These constructions belong to the formalization of [OrtizEtAl2001].

## Main statements

* `controlledUV_conjugation`: computes the conjugated off-diagonal ancilla matrix unit.
* `ancilla_measurement_identity`: relates the ancilla observable to the system trace.

## References

* [Ortiz et al., 2001][OrtizEtAl2001]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.FermionicSim00.MainResults

/-- The two-dimensional density matrix with every entry equal to one half, representing the
equal-superposition ancilla state. -/
def ancillaRho : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), 1 / 2; 1 / 2, 1 / 2]

/-- The two-dimensional Pauli X matrix indexed by `Fin 2`. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The two-dimensional Pauli Y matrix indexed by `Fin 2`. -/
def pauliY2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The two-dimensional matrix unit with its only nonzero entry at row zero and column one. -/
def ketBra01 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The projection onto the ancilla basis state indexed by zero. -/
def ketBra00 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The projection onto the ancilla basis state indexed by one. -/
def ketBra11 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The block-diagonal matrix applying `U` in ancilla state zero and `V` in ancilla state one. -/
def controlledUV {n : ℕ} (U V : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Fin 2 × Reg n) (Fin 2 × Reg n) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then (if p.1 = 0 then U p.2 q.2 else V p.2 q.2) else 0

/-- The equal-superposition ancilla density matrix is half the sum of the identity and Pauli X. -/
theorem ancillaRho_eq : ancillaRho
    = (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + pauliX2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ancillaRho, pauliX2]

/-- Pauli X plus imaginary times Pauli Y is twice the matrix unit `ketBra01`. See
[OrtizEtAl2001]. -/
theorem pauliX_add_I_pauliY : pauliX2 + Complex.I • pauliY2 = (2 : ℂ) • ketBra01 := by
  ext i j
  (fin_cases i <;> fin_cases j <;> simp [pauliX2, pauliY2, ketBra01, Complex.I_mul_I]);
    norm_num

/-- The controlled block matrix is the sum of the two ancilla projections tensored with `U` and
`V`. -/
theorem controlledUV_eq_sum {n : ℕ} (U V : Matrix (Reg n) (Reg n) ℂ) :
    controlledUV U V = ketBra00 ⊗ₖ U + ketBra11 ⊗ₖ V := by
  ext p q
  rcases p with ⟨a, y⟩
  rcases q with ⟨b, x⟩
  fin_cases a <;> fin_cases b <;>
    simp [controlledUV, ketBra00, ketBra11, Matrix.add_apply]

/-- The controlled block matrix factors into separate block matrices applying `U` on the zero
branch and `V` on the one branch. See [OrtizEtAl2001]. -/
theorem controlledUV_eq_blocks {n : ℕ} (U V : Matrix (Reg n) (Reg n) ℂ) :
    controlledUV U V =
      (ketBra00 ⊗ₖ U + ketBra11 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ))
        * (ketBra00 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ) + ketBra11 ⊗ₖ V) := by
  rw [controlledUV_eq_sum]
  have e00 : (ketBra00 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra00 = ketBra00 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ketBra00, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (ketBra00 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra11 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ketBra00, ketBra11, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (ketBra11 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra00 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ketBra00, ketBra11, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (ketBra11 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra11 = ketBra11 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ketBra11, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul, e00, e01, e10, e11,
    Matrix.mul_one, Matrix.one_mul, zero_kronecker, add_zero, zero_add]

/-- The adjoint controlled block matrix has diagonal system blocks `Uᴴ` and `Vᴴ`. -/
theorem conjTranspose_controlledUV {n : ℕ} (U V : Matrix (Reg n) (Reg n) ℂ) :
    (controlledUV U V)ᴴ = ketBra00 ⊗ₖ Uᴴ + ketBra11 ⊗ₖ Vᴴ := by
  rw [controlledUV_eq_sum, conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker]
  have h0 : (ketBra00 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = ketBra00 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ketBra00]
  have h1 : (ketBra11 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = ketBra11 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ketBra11]
  rw [h0, h1]

/-- Conjugating the off-diagonal ancilla matrix unit by the controlled block matrix gives that
matrix unit tensored with `Uᴴ * V`. See [OrtizEtAl2001]. -/
theorem controlledUV_conjugation {n : ℕ} (U V : Matrix (Reg n) (Reg n) ℂ) :
    (controlledUV U V)ᴴ * (ketBra01 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ)) * controlledUV U V
      = ketBra01 ⊗ₖ (Uᴴ * V) := by
  rw [conjTranspose_controlledUV, controlledUV_eq_sum]
  have h000 : (ketBra00 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra01 * ketBra00 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ketBra00, ketBra01, Matrix.mul_apply, Fin.sum_univ_two]
  have h001 : (ketBra00 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra01 * ketBra11 = ketBra01 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ketBra00, ketBra01, ketBra11, Matrix.mul_apply, Fin.sum_univ_two]
  have h100 : (ketBra11 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra01 * ketBra00 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ketBra00, ketBra01, ketBra11, Matrix.mul_apply, Fin.sum_univ_two]
  have h101 : (ketBra11 : Matrix (Fin 2) (Fin 2) ℂ) * ketBra01 * ketBra11 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ketBra01, ketBra11, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul, h000, h001, h100, h101,
    zero_kronecker, add_zero, zero_add, Matrix.mul_one]

/-- The trace of `ketBra01 * ancillaRho` is one half. See [OrtizEtAl2001]. -/
theorem trace_ketBra01_ancillaRho :
    Matrix.trace (ketBra01 * ancillaRho) = (1 / 2 : ℂ) := by
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, ketBra01, ancillaRho, Fin.sum_univ_two]

/-- The combined ancilla X and imaginary Y trace after controlled evolution equals twice the
conjugated matrix-unit trace, which equals `Matrix.trace (Uᴴ * V * ρ)`. [OrtizEtAl2001] -/
theorem ancilla_measurement_identity {n : ℕ} (U V ρ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix.trace ((pauliX2 + Complex.I • pauliY2) ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ) *
        (controlledUV U V * (ancillaRho ⊗ₖ ρ) * (controlledUV U V)ᴴ))
      = 2 * Matrix.trace ((controlledUV U V)ᴴ
          * (ketBra01 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ)) * controlledUV U V
          * (ancillaRho ⊗ₖ ρ)) ∧
    2 * Matrix.trace ((controlledUV U V)ᴴ
          * (ketBra01 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ)) * controlledUV U V
          * (ancillaRho ⊗ₖ ρ))
      = Matrix.trace (Uᴴ * V * ρ) := by
  have hrot : ∀ A B C D : Matrix (Fin 2 × Reg n) (Fin 2 × Reg n) ℂ,
      Matrix.trace (A * B * C * D) = Matrix.trace (D * A * B * C) := by
    intro A B C D
    rw [Matrix.trace_mul_comm (A * B * C) D]
    simp only [Matrix.mul_assoc]
  constructor
  · rw [pauliX_add_I_pauliY, smul_kronecker, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    have hmul : (ketBra01 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ))
          * (controlledUV U V * (ancillaRho ⊗ₖ ρ) * (controlledUV U V)ᴴ)
        = (ketBra01 ⊗ₖ (1 : Matrix (Reg n) (Reg n) ℂ))
          * controlledUV U V * (ancillaRho ⊗ₖ ρ) * (controlledUV U V)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [hmul, hrot]
  · rw [controlledUV_conjugation]
    rw [← Matrix.mul_kronecker_mul]
    rw [Matrix.trace_kronecker, trace_ketBra01_ancillaRho]
    ring

end Qatlib.Papers.FermionicSim00.MainResults
