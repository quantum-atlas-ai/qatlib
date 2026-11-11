/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
# The two-qubit correlation inequality

This module defines explicit two-qubit Pauli matrices and proves `lemma3_zz_bound`, which bounds
the ZZ correlation of a density matrix by one minus twice the absolute mean XX/YY correlation.
The proof uses decompositions of `opII ± opXX ± opYY - opZZ` into doubled outer products
supported on the two odd-parity basis vectors.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `plus_decomp` and `minus_decomp`: give explicit outer-product decompositions.
* `lemma3_zz_bound`: proves the two-qubit correlation inequality.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped ComplexOrder

namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit

/-- The Pauli X matrix with off-diagonal entries one and diagonal entries zero. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli Y matrix with off-diagonal entries −i and i. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The diagonal Pauli Z matrix with entries one and −1. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Kronecker product of two one-qubit matrices, indexed by pairs of basis indices. -/
def kron (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => A i.1 j.1 * B i.2 j.2

/-- The two-qubit operator `pauliX ⊗ pauliX`. -/
def opXX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := kron pauliX pauliX

/-- The two-qubit operator `pauliY ⊗ pauliY`. -/
def opYY : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := kron pauliY pauliY

/-- The two-qubit operator `pauliZ ⊗ pauliZ`. -/
def opZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := kron pauliZ pauliZ

/-- The identity matrix on the two-qubit basis. -/
def opII : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1

/-- The real part of the trace of `O * ρ`. -/
def expect (O ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := ((O * ρ).trace).re

/-- The real expectation of `opXX` in the matrix `ρ`. -/
def corrXX (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := expect opXX ρ

/-- The real expectation of `opYY` in the matrix `ρ`. -/
def corrYY (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := expect opYY ρ

/-- The real expectation of `opZZ` in the matrix `ρ`. -/
def corrZZ (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ := expect opZZ ρ

/-- The arithmetic mean of the two-qubit XX and YY correlations. -/
def tParam (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (corrXX ρ + corrYY ρ) / 2

/-- The unnormalized vector with value one at basis indices `(0, 1)` and `(1, 0)` and zero
elsewhere. -/
def uPlus : Fin 2 × Fin 2 → ℂ := fun i => if i = (0, 1) ∨ i = (1, 0) then 1 else 0

/-- The unnormalized vector with values one at `(0, 1)`, −1 at `(1, 0)`, and zero elsewhere. -/
def uMinus : Fin 2 × Fin 2 → ℂ :=
  fun i => if i = (0, 1) then 1 else if i = (1, 0) then (-1 : ℂ) else 0

/-- The bilinear outer-product matrix with entry `u i * u j`, without complex conjugation. -/
def rankOne (u : Fin 2 × Fin 2 → ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => u i * u j

/-- The matrix `opII + opXX + opYY - opZZ` equals twice the outer product `rankOne uPlus`. -/
lemma plus_decomp :
    (opII + opXX + opYY - opZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      rankOne uPlus + rankOne uPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opII, opXX, opYY, opZZ, kron, pauliX, pauliY, pauliZ, rankOne, uPlus]

/-- The matrix `opII - opXX - opYY - opZZ` equals twice the outer product `rankOne uMinus`. -/
lemma minus_decomp :
    (opII - opXX - opYY - opZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      rankOne uMinus + rankOne uMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [opII, opXX, opYY, opZZ, kron, pauliX, pauliY, pauliZ, rankOne, uMinus] <;> norm_num

/-- The real trace expectation is additive in its operator argument. -/
lemma expect_add (A B ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    expect (A + B) ρ = expect A ρ + expect B ρ := by
  simp [expect, Matrix.add_mul, Matrix.trace_add, Complex.add_re]

/-- The real trace expectation preserves subtraction in its operator argument. -/
lemma expect_sub (A B ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    expect (A - B) ρ = expect A ρ - expect B ρ := by
  simp [expect, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

/-- The trace of `rankOne uPlus * ρ` is the sum of the four entries of `ρ` on the odd-parity
two-by-two block. -/
lemma trace_rankOne_mul_uPlus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (rankOne uPlus * ρ).trace =
      ρ (0, 1) (0, 1) + ρ (0, 1) (1, 0) + ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [Matrix.trace, Matrix.mul_apply, rankOne, uPlus, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  ring

/-- The quadratic form of `ρ` at `uPlus` is the sum of the four entries of the odd-parity
two-by-two block. -/
lemma dotProduct_uPlus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)) =
      ρ (0, 1) (0, 1) + ρ (0, 1) (1, 0) + ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [dotProduct, Matrix.mulVec, uPlus, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The trace of `rankOne uMinus * ρ` is the sum of the two odd-parity diagonal entries minus
the two cross entries. -/
lemma trace_rankOne_mul_uMinus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (rankOne uMinus * ρ).trace =
      ρ (0, 1) (0, 1) - ρ (0, 1) (1, 0) - ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [Matrix.trace, Matrix.mul_apply, rankOne, uMinus, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  ring

/-- The quadratic form of `ρ` at `uMinus` is the sum of the two odd-parity diagonal entries
minus the two cross entries. -/
lemma dotProduct_uMinus (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)) =
      ρ (0, 1) (0, 1) - ρ (0, 1) (1, 0) - ρ (1, 0) (0, 1) + ρ (1, 0) (1, 0) := by
  simp [dotProduct, Matrix.mulVec, uMinus, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- For a positive semidefinite two-qubit matrix of trace one, `corrZZ ρ ≤ 1 - 2 * |tParam ρ|`.
This is [Crosta et al., Lemma 3][CrostaSaubanereHuber2026]. -/
theorem lemma3_zz_bound
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    corrZZ ρ ≤ 1 - 2 * |tParam ρ| := by

  have hqPlus : 0 ≤ (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)).re := hρ.re_dotProduct_nonneg uPlus
  have hqMinus : 0 ≤ (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)).re := hρ.re_dotProduct_nonneg uMinus

  have hbridgePlus :
      expect (rankOne uPlus) ρ = (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)).re := by
    simp only [expect]
    rw [trace_rankOne_mul_uPlus, dotProduct_uPlus]
  have hbridgeMinus :
      expect (rankOne uMinus) ρ = (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)).re := by
    simp only [expect]
    rw [trace_rankOne_mul_uMinus, dotProduct_uMinus]

  have hlinPlus :
      expect (opII + opXX + opYY - opZZ) ρ
        = expect opII ρ + expect opXX ρ + expect opYY ρ - expect opZZ ρ := by
    rw [expect_sub, expect_add, expect_add]
  have hlinMinus :
      expect (opII - opXX - opYY - opZZ) ρ
        = expect opII ρ - expect opXX ρ - expect opYY ρ - expect opZZ ρ := by
    rw [expect_sub, expect_sub, expect_sub]
  have hII : expect opII ρ = 1 := by
    simp [expect, opII, htr]

  have hvalPlus :
      expect (opII + opXX + opYY - opZZ) ρ = 2 * (star uPlus ⬝ᵥ (ρ *ᵥ uPlus)).re := by
    rw [plus_decomp, expect_add, hbridgePlus]
    ring
  have hvalMinus :
      expect (opII - opXX - opYY - opZZ) ρ = 2 * (star uMinus ⬝ᵥ (ρ *ᵥ uMinus)).re := by
    rw [minus_decomp, expect_add, hbridgeMinus]
    ring

  have hplus : 0 ≤ 1 + corrXX ρ + corrYY ρ - corrZZ ρ := by
    simp only [corrXX, corrYY, corrZZ]
    rw [← hII, ← hlinPlus, hvalPlus]
    linarith
  have hminus : 0 ≤ 1 - corrXX ρ - corrYY ρ - corrZZ ρ := by
    simp only [corrXX, corrYY, corrZZ]
    rw [← hII, ← hlinMinus, hvalMinus]
    linarith

  have hle1 : corrZZ ρ ≤ 1 + (corrXX ρ + corrYY ρ) := by linarith
  have hle2 : corrZZ ρ ≤ 1 - (corrXX ρ + corrYY ρ) := by linarith
  have hkey : corrZZ ρ ≤ 1 - |corrXX ρ + corrYY ρ| := by
    rcases le_total 0 (corrXX ρ + corrYY ρ) with hs | hs
    · rw [abs_of_nonneg hs]; linarith
    · rw [abs_of_nonpos hs]; linarith

  have habs : 2 * |tParam ρ| = |corrXX ρ + corrYY ρ| := by
    simp only [tParam]
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    ring
  rwa [habs]

end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TwoQubit
