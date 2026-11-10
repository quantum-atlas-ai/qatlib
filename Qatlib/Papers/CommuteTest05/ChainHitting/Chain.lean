/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.Operator

namespace Qatlib.Papers.CommuteTest05.ChainHitting

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def absorbingBlock (Q : Matrix ι ι ℝ) (R : Matrix ι κ ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks Q R 0 1

theorem absorbingBlock_pow (Q : Matrix ι ι ℝ) (R : Matrix ι κ ℝ) :
    ∀ n : ℕ, absorbingBlock Q R ^ n =
      Matrix.fromBlocks (Q ^ n) ((∑ i ∈ Finset.range n, Q ^ i) * R) 0 1 := by
  intro n
  induction n with
  | zero =>
      simp [absorbingBlock, Matrix.fromBlocks_one]
  | succ n ih =>
      rw [pow_succ, ih, absorbingBlock, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [pow_succ]; simp
      · have hs : (∑ x ∈ Finset.range (n + 1), Q ^ x) =
            (∑ x ∈ Finset.range n, Q ^ x) + Q ^ n :=
          Finset.sum_range_succ (fun i => Q ^ i) n
        rw [hs]
        show Q ^ n * R + (∑ x ∈ Finset.range n, Q ^ x) * R * 1 =
          ((∑ x ∈ Finset.range n, Q ^ x) + Q ^ n) * R
        rw [Matrix.mul_one, Matrix.add_mul]
        abel
      · simp
      · simp

theorem lazification_eigen_nonneg (P : Matrix ι ι ℝ) (v : ι → ℝ) {lam : ℝ}
    (hv : P *ᵥ v = lam • v) (hlam : -1 ≤ lam) :
    ((1 / 2 : ℝ) • (P + 1)) *ᵥ v = ((1 / 2 : ℝ) * (lam + 1)) • v ∧
      0 ≤ (1 / 2 : ℝ) * (lam + 1) := by
  constructor
  · rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hv,
      smul_add, smul_smul, ← add_smul]
    congr 1
    ring
  · linarith

def johnsonEigen (r n j : ℝ) : ℝ := (r - j) * (n - r) - j * (r - j + 1)

theorem johnson_lambda_zero (r n : ℝ) : johnsonEigen r n 0 = r * (n - r) := by
  simp [johnsonEigen]

theorem johnson_lambda_one (r n : ℝ) :
    johnsonEigen r n 1 = r * (n - r) - n := by
  simp [johnsonEigen]
  ring

theorem johnson_gap (r n : ℝ) (hr : 0 < r) (hn : r < n) :
    (1 : ℝ) / r < n / (r * (n - r)) := by
  have hnr : 0 < n - r := by linarith
  have hrp : 0 < r * (n - r) := mul_pos hr hnr
  have hrne : r ≠ 0 := hr.ne'
  have hrpne : r * (n - r) ≠ 0 := hrp.ne'
  field_simp
  nlinarith

end Qatlib.Papers.CommuteTest05.ChainHitting
