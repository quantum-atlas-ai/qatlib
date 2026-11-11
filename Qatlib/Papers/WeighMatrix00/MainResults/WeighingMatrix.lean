/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Weighing matrices and column sparsity

A `WeighingMatrix n k` is an integer matrix with entries in {-1, 0, 1} and row Gram matrix `k`
times the identity. Passing to rational matrices gives the transpose Gram identity and exact
column support counts; `problemFunction` exposes a selected row as an oracle.

This development forms part of the formalization of [VanDam2002].

## Main statements

* `WeighingMatrix`: An `n` by `n` integer matrix with entries in {-1, 0, 1} whose row Gram
  matrix is `k` times the identity.
* `ratMat_transpose_gram`: The rational column Gram matrix is `k` times the identity.
* `col_nonzero_card`: Each column contains exactly `k` nonzero entries.

## References

* [van Dam, 2002][VanDam2002]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

open Matrix

/-- An `n` by `n` integer matrix with entries in {-1, 0, 1} whose row Gram matrix is `k` times
the identity. -/
structure WeighingMatrix (n k : ℕ) where

  mat : Matrix (Fin n) (Fin n) ℤ

  entry : ∀ i j, mat i j = -1 ∨ mat i j = 0 ∨ mat i j = 1

  gram : mat * matᵀ = (k : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

namespace WeighingMatrix

variable {n k : ℕ} (M : WeighingMatrix n k)

/-- The pairing of two rows is `k` when their indices agree and zero otherwise. -/
theorem gram_apply (s r : Fin n) :
    ∑ i : Fin n, M.mat s i * M.mat r i = if s = r then (k : ℤ) else 0 := by
  have h := congrFun (congrFun M.gram s) r
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    mul_ite, ite_mul] using h

/-- The rational-valued row pairing is `k` on the diagonal and zero off the diagonal. -/
theorem gram_apply_rat (s r : Fin n) :
    ∑ i : Fin n, ((M.mat s i : ℚ) * (M.mat r i : ℚ)) =
      if s = r then (k : ℚ) else 0 := by
  have h := M.gram_apply s r
  by_cases hsr : s = r
  · rw [if_pos hsr] at h ⊢
    exact_mod_cast h
  · rw [if_neg hsr] at h ⊢
    exact_mod_cast h

/-- The weighing matrix with its entries cast to rational numbers. -/
def ratMat : Matrix (Fin n) (Fin n) ℚ := M.mat.map (Int.castRingHom ℚ)

/-- Each entry of `ratMat` is the rational cast of the corresponding integer entry. -/
theorem ratMat_apply (i j : Fin n) : M.ratMat i j = (M.mat i j : ℚ) := by
  simp [ratMat]

/-- The rational row Gram matrix is `k` times the identity. -/
theorem ratMat_gram : M.ratMat * M.ratMatᵀ = (k : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext s r
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    ratMat_apply, M.gram_apply_rat s r]
  split_ifs <;> simp

/-- The rational column Gram matrix is `k` times the identity. -/
theorem ratMat_transpose_gram :
    M.ratMatᵀ * M.ratMat = (k : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  by_cases hk : k = 0
  · have hAA : M.ratMat * M.ratMatᵀ = 0 := by simpa [hk] using M.ratMat_gram
    have hzero : ∀ s r : Fin n, ∑ i : Fin n, M.ratMat s i * M.ratMat r i = 0 := by
      intro s r
      have h := congrFun (congrFun hAA s) r
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using h
    have hrow : ∀ s i : Fin n, M.ratMat s i = 0 := by
      intro s i
      have h := hzero s s
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (M.ratMat s j))).mp h i (Finset.mem_univ i)
      exact mul_self_eq_zero.mp this
    have hA0 : M.ratMat = 0 := by
      ext s i
      exact hrow s i
    rw [hA0, hk]
    simp
  · have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    set A := M.ratMat
    have hAA : A * Aᵀ = (k : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := M.ratMat_gram
    set B : Matrix (Fin n) (Fin n) ℚ := (k : ℚ)⁻¹ • A with hB
    have hBA : B * Aᵀ = 1 := by
      rw [hB, Matrix.smul_mul, hAA, smul_smul, inv_mul_cancel₀ hkq, one_smul]
    have hAB : Aᵀ * B = 1 := mul_eq_one_comm.mp hBA
    have hmain : Aᵀ * A = (k : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
      calc Aᵀ * A = Aᵀ * ((k : ℚ) • B) := by
              rw [hB, smul_smul, mul_inv_cancel₀ hkq, one_smul]
        _ = (k : ℚ) • (Aᵀ * B) := by rw [Matrix.mul_smul]
        _ = (k : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by rw [hAB]
    simpa [A] using hmain

/-- Each column contains exactly `k` nonzero entries. -/
theorem col_nonzero_card (i : Fin n) :
    (Finset.univ.filter (fun s : Fin n => M.mat s i ≠ 0)).card = k := by
  have hdiag : ∀ j : Fin n, ∑ s : Fin n, (M.ratMat s j) * (M.ratMat s j) = (k : ℚ) := by
    intro j
    have h := congrFun (congrFun M.ratMat_transpose_gram j) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] using h
  have hcol := hdiag i
  have hterm : ∀ s : Fin n,
      (M.ratMat s i) * (M.ratMat s i) = if M.mat s i ≠ 0 then (1 : ℚ) else 0 := by
    intro s
    rw [ratMat_apply]
    rcases M.entry s i with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)] at hcol
  have hcast : ((∑ s : Fin n, if M.mat s i ≠ 0 then (1 : ℕ) else 0) : ℚ) = (k : ℚ) := by
    push_cast
    exact hcol
  have hnat : (∑ s : Fin n, if M.mat s i ≠ 0 then (1 : ℕ) else 0) = k := by
    exact_mod_cast hcast
  rw [Finset.card_filter]
  simpa using hnat

/-- Each column contains exactly `n - k` zero entries. -/
theorem col_zero_card (i : Fin n) :
    (Finset.univ.filter (fun s : Fin n => M.mat s i = 0)).card = n - k := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun s => M.mat s i ≠ 0)
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  have hk := M.col_nonzero_card i
  have hnot : (Finset.univ.filter (fun s : Fin n => ¬ (M.mat s i ≠ 0))) =
      (Finset.univ.filter (fun s : Fin n => M.mat s i = 0)) := by
    apply Finset.filter_congr
    intro s _
    simp
  rw [hnot] at hsplit
  omega

end WeighingMatrix

/-- The oracle function returning the entries of row `s` of the weighing matrix. -/
def problemFunction {n k : ℕ} (M : WeighingMatrix n k) (s : Fin n) : Fin n → ℤ :=
  fun i => M.mat s i

end Qatlib.Papers.WeighMatrix00.MainResults
