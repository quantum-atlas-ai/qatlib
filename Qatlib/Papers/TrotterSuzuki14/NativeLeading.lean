/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.NestedComm

set_option autoImplicit false
open scoped BigOperators Matrix
namespace Qatlib.Papers.TrotterSuzuki14.NativeLeading
open Qatlib.Foundations.MatrixAlgebra
open NestedComm
noncomputable section
variable {D : Type*} [Fintype D]

def triples (m : ℕ) : Finset (Fin m × Fin m × Fin m) :=
  Finset.univ.filter (fun t => t.1 ≤ t.2.1 ∧ t.2.2 < t.2.1)

def weight {m : ℕ} (a b : Fin m) : ℝ := if a = b then 1 / 2 else 1

def leading {m : ℕ} (H : Fin m → Matrix D D ℂ) (dt : ℝ) : Matrix D D ℂ :=
  ∑ t ∈ triples m, (-(dt ^ 2 / 12) * weight t.1 t.2.1) • nested (H t.1) (H t.2.1) (H t.2.2)

theorem weighted_nested (w : ℝ) (X Y Z : Matrix D D ℂ) :
    w • nested X Y Z = NestedComm.comm (w • X) (NestedComm.comm Y Z) := by
  simp only [nested, NestedComm.comm, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem leading_trace {m : ℕ} (H : Fin m → Matrix D D ℂ) (dt : ℝ) :
    (leading H dt).trace = 0 := by
  simp only [leading, Matrix.trace_sum, Matrix.trace_smul, trace_nested, smul_zero,
      Finset.sum_const_zero]

theorem leading_hermitian {m : ℕ} (H : Fin m → Matrix D D ℂ)
    (hH : ∀ a, (H a).IsHermitian) (dt : ℝ) : (leading H dt).IsHermitian := by
  unfold leading
  apply isSelfAdjoint_sum
  intro t _
  exact (nested_hermitian _ _ _ (hH t.1) (hH t.2.1) (hH t.2.2)).smul
    (IsSelfAdjoint.all _)

variable [DecidableEq D]

theorem leading_opNorm_le {m : ℕ} (H : Fin m → Matrix D D ℂ) (dt : ℝ) :
    opNorm (leading H dt) ≤ (dt ^ 2 / 12) * 4 *
      ∑ t ∈ triples m, opNorm (H t.1) * opNorm (H t.2.1) * opNorm (H t.2.2) := by
  have hs : (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) (leading H dt) =
      ∑ t ∈ triples m, ((-(dt ^ 2 / 12) * weight t.1 t.2.1 : ℝ) : ℂ) •
        (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) (nested (H t.1) (H t.2.1) (H t.2.2)) := by
    simp only [leading, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← IsScalarTower.algebraMap_smul ℂ (_ : ℝ) (_ : Matrix D D ℂ), map_smul]
    rfl
  rw [opNorm, hs]
  calc ‖∑ t ∈ triples m, ((-(dt ^ 2 / 12) * weight t.1 t.2.1 : ℝ) : ℂ) •
          (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) (nested (H t.1) (H t.2.1) (H t.2.2))‖
      ≤ ∑ t ∈ triples m, ‖((-(dt ^ 2 / 12) * weight t.1 t.2.1 : ℝ) : ℂ) •
          (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) (nested (H t.1) (H t.2.1) (H t.2.2))‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ triples m, (dt ^ 2 / 12) * 4 *
        (opNorm (H t.1) * opNorm (H t.2.1) * opNorm (H t.2.2)) := by
      apply Finset.sum_le_sum
      intro t _
      have hw : |weight t.1 t.2.1| ≤ 1 := by unfold weight; split_ifs <;> norm_num
      have hn := nested_opNorm_le (H t.1) (H t.2.1) (H t.2.2)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg (show 0 ≤ dt ^ 2 / 12 by positivity)]
      change (dt ^ 2 / 12) * |weight t.1 t.2.1| * opNorm (nested _ _ _) ≤ _
      have hn0 : 0 ≤ opNorm (nested (H t.1) (H t.2.1) (H t.2.2)) := norm_nonneg _
      have hstep : (dt ^ 2 / 12) * |weight t.1 t.2.1| * opNorm (nested (H t.1) (H t.2.1) (H t.2.2))
          ≤ (dt ^ 2 / 12) * (4 * opNorm (H t.1) * opNorm (H t.2.1) * opNorm (H t.2.2)) := by
        calc _ ≤ (dt ^ 2 / 12) * opNorm (nested (H t.1) (H t.2.1) (H t.2.2)) := by
               nlinarith [mul_nonneg (show 0 ≤ dt ^ 2 / 12 by positivity) hn0]
             _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
      nlinarith [hstep]
    _ = _ := by rw [← Finset.mul_sum]

end
end Qatlib.Papers.TrotterSuzuki14.NativeLeading
