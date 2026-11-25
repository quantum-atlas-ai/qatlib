/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The two-state rate matrix exponential

Childs--Li, *Efficient simulation of sparse Markovian quantum dynamics*,
fixed arXiv:1611.05543v3 (9 Oct 2023), Section 4.3.1, Lemma 2, Eq. (90).

Lemma 2 solves the two-state relaxation of a strongly `1`-sparse coefficient
matrix explicitly. Writing `α, β` for the two transition rates, the rate matrix
is `[[-α, α], [β, -β]]`; its eigenvalues are `0` (eigenvector `(1,1)`) and
`-(α+β)` (eigenvector `(α,-β)`), so the matrix exponential at time `t` is
`[[β + αE, α - αE], [β - βE, α + βE]]/(α+β)` with `E = e^{-(α+β)t}`.

This module records the closed form and proves it by conjugating the rate matrix
to the diagonal matrix of its eigenvalues: with `U = [[1, α], [1, -β]]` one has
`U⁻¹ A U = diag(0, -(α+β))`, `exp` is invariant under conjugation, and the
exponential of a diagonal matrix is the diagonal of the scalar exponentials.

The card target writes the exponential as `Matrix.exp`; the library name of the
matrix exponential is `NormedSpace.exp`, which is what is stated below. The
degenerate case `α + β = 0` is excluded by a hypothesis, as in the paper, where
Lemma 2 assumes `ν(x) ≠ x` and a strongly `1`-sparse coefficient matrix.
-/
set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.SparseMarkov16.MainResults.TwoStateRateExp

/-- The two-state rate matrix `[[-α, α], [β, -β]]` of Lemma 2 (Eq. (88)). -/
def twoStateRate (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(-α), α; β, -β]

/-- The eigenvector matrix `[[1, α], [1, -β]]` of `twoStateRate`. -/
def eigenMat (α β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, α; 1, -β]

/-- The diagonalized rate matrix `diag(0, -(α+β)t)` of Lemma 2. -/
def diagRate (α β t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -(α + β) * t]

/-- `det [[1, α], [1, -β]] = -(α+β)` is nonzero when `α + β ≠ 0`, so the
eigenvector matrix is invertible. -/
theorem det_eigenMat {α β : ℝ} (h : α + β ≠ 0) : (eigenMat α β).det ≠ 0 := by
  intro hz
  apply h
  have := hz
  rw [eigenMat, Matrix.det_fin_two_of] at this
  linarith

/-- The explicit inverse of the eigenvector matrix: `(α+β)⁻¹ • [[β, α], [1, -1]]`. -/
theorem inv_eigenMat {α β : ℝ} (h : α + β ≠ 0) :
    (eigenMat α β)⁻¹ = (α + β)⁻¹ • !![β, α; 1, -1] := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Conjugating the rate matrix by the eigenvector matrix diagonalizes it. -/
theorem conj_diagRate {α β t : ℝ} (h : α + β ≠ 0) :
    eigenMat α β * diagRate α β t * (eigenMat α β)⁻¹ = t • twoStateRate α β := by
  rw [inv_eigenMat h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenMat, diagRate, twoStateRate] <;> field_simp <;> ring

/-- The exponential of the diagonalized rate matrix keeps the zero eigenvalue and
exponentiates the nonzero one. -/
theorem exp_diagRate {α β t : ℝ} :
    NormedSpace.exp (diagRate α β t) = !![1, 0; 0, Real.exp (-(α + β) * t)] := by
  have hd : diagRate α β t = Matrix.diagonal ![0, -(α + β) * t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagRate, Matrix.diagonal]
  rw [hd, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Real.exp_eq_exp_ℝ]

/-- Lemma 2, Eq. (90): the exact two-state rate matrix exponential. -/
theorem matrixExp_twoStateRate {α β : ℝ} (h : α + β ≠ 0) (t : ℝ) :
    NormedSpace.exp (t • twoStateRate α β) =
      !![β / (α + β) + α / (α + β) * Real.exp (-(α + β) * t),
          α / (α + β) - α / (α + β) * Real.exp (-(α + β) * t);
        β / (α + β) - β / (α + β) * Real.exp (-(α + β) * t),
          α / (α + β) + β / (α + β) * Real.exp (-(α + β) * t)] := by
  have hU : IsUnit (eigenMat α β) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (det_eigenMat h)
  rw [← conj_diagRate h, Matrix.exp_conj _ _ hU, exp_diagRate, inv_eigenMat h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eigenMat] <;> field_simp <;> ring

end Qatlib.Papers.SparseMarkov16.MainResults.TwoStateRateExp
