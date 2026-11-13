/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Mathlib.Tactic

/-!
# Tensor-product Pauli basis

This module constructs register Pauli matrices as products of single-qubit matrix entries and
proves that each is Hermitian and unitary. The matrix-entry completeness identity yields an
expansion of every complex register matrix using the normalized trace coefficients
`pauliCoefficient`.

The expansion is the standard Pauli-basis representation of operators discussed in
[NielsenChuang2010].

## Main statements

* `word_adjoint` and `word_unitary`: Hermitian and unitary properties of Pauli words.
* `word_resolution`: matrix-entry completeness of the tensor-product family.
* `word_expansion`: expansion of any register matrix in Pauli word matrices.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.GateVocab
open scoped Classical
namespace Qatlib.Concepts.PauliClifford.PauliBasis

/-- The tensor-product Pauli matrix specified by a four-valued letter at each register site. -/
noncomputable def pauliWord {n : ℕ} (w : Fin n → Fin 4) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y => ∏ j, pauliBool (w j) (x j) (y j)

/-- Every tensor-product Pauli word matrix is Hermitian. -/
theorem word_adjoint {n : ℕ} (w : Fin n → Fin 4) :
    (pauliWord w).conjTranspose = pauliWord w := by
  ext x y
  simp only [pauliWord, Matrix.conjTranspose_apply, star_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact congrArg (fun A : Matrix Bool Bool ℂ => A (x j) (y j)) (pauli_adjoint (w j))

/-- Every tensor-product Pauli word matrix belongs to the matrix unitary group. -/
theorem word_unitary {n : ℕ} (w : Fin n → Fin 4) :
    pauliWord w ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, word_adjoint]
  ext x y
  simp only [Matrix.mul_apply, pauliWord, Matrix.one_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j b => pauliBool (w j) (x j) b * pauliBool (w j) b (y j))]
  have hp (j : Fin n) :
      (∑ b, pauliBool (w j) (x j) b * pauliBool (w j) b (y j)) =
      if x j = y j then 1 else 0 := by
    exact congrArg (fun A : Matrix Bool Bool ℂ => A (x j) (y j)) (pauli_involution (w j))
  simp_rw [hp]
  simp only [Fintype.prod_boole, funext_iff]
  split_ifs <;> rfl

/-- The four single-qubit Pauli matrices satisfy the displayed matrix-entry completeness
identity with factor one half. -/
theorem bool_resolution (x y u v : Bool) :
    (∑ a : Fin 4, (1/2 : ℂ) * pauliBool a y x * pauliBool a u v) =
    (if u=x then 1 else 0) * (if v=y then 1 else 0) := by
  cases x <;> cases y <;> cases u <;> cases v <;>
    norm_num [Fin.sum_univ_succ, pauliBool, pauliYBool, PauliX, PauliZ, permMatrix] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The tensor-product Pauli matrices satisfy the matrix-entry completeness identity with factor
`(1 / 2) ^ n`. -/
theorem word_resolution {n : ℕ} (x y u v : Reg n) :
    (∑ w : Fin n → Fin 4, (1/2 : ℂ)^n * pauliWord w y x * pauliWord w u v) =
    (if u=x then 1 else 0) * (if v=y then 1 else 0) := by
  have hf (w : Fin n → Fin 4) :
      (1/2 : ℂ)^n * pauliWord w y x * pauliWord w u v =
      ∏ j, ((1/2 : ℂ) * pauliBool (w j) (y j) (x j) * pauliBool (w j) (u j) (v j)) := by
    simp only [Finset.prod_mul_distrib, pauliWord, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  simp_rw [hf]
  rw [← Fintype.prod_sum (fun j a => (1/2 : ℂ) * pauliBool a (y j) (x j) * pauliBool a (u j) (v j))]
  simp_rw [bool_resolution]
  rw [Finset.prod_mul_distrib]
  simp only [Fintype.prod_boole, funext_iff]
  split_ifs <;> rfl

/-- The normalized trace coefficient `2⁻ⁿ * trace (pauliWord w * A)` of a matrix in the Pauli
basis. -/
noncomputable def pauliCoefficient {n : ℕ} (A : Matrix (Reg n) (Reg n) ℂ)
    (w : Fin n → Fin 4) : ℂ := (1/2 : ℂ)^n * Matrix.trace (pauliWord w * A)

/-- Every complex register matrix equals the sum of its Pauli trace coefficients times the
corresponding Pauli word matrices. -/
theorem word_expansion {n : ℕ} (A : Matrix (Reg n) (Reg n) ℂ) :
    A = ∑ w, pauliCoefficient A w • pauliWord w := by
  ext u v
  simp only [pauliCoefficient, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Eq.symm
  calc
    _ = ∑ x, ∑ y, A y x *
        (∑ w : Fin n → Fin 4, (1/2 : ℂ)^n * pauliWord w x y * pauliWord w u v) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = A u v := by
      simp_rw [word_resolution]
      simp
end Qatlib.Concepts.PauliClifford.PauliBasis
