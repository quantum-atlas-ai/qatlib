/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Qatlib.Papers.StabilizerSim04.MainResults.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StabilizerSim04.MainResults

open Matrix

def lowerBlock {n : ℕ} (v : Fin n → ZMod 2) (N : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases (1 : ZMod 2) (fun _ => 0) j)
      (fun i' => Fin.cases (v i') (fun j' => N i' j') j) i

@[simp] theorem lowerBlock_zero_zero {n : ℕ} (v : Fin n → ZMod 2)
    (N : Matrix (Fin n) (Fin n) (ZMod 2)) : lowerBlock v N 0 0 = 1 := rfl

@[simp] theorem lowerBlock_zero_succ {n : ℕ} (v : Fin n → ZMod 2)
    (N : Matrix (Fin n) (Fin n) (ZMod 2)) (j : Fin n) :
    lowerBlock v N 0 j.succ = 0 := rfl

@[simp] theorem lowerBlock_succ_zero {n : ℕ} (v : Fin n → ZMod 2)
    (N : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) :
    lowerBlock v N i.succ 0 = v i := rfl

@[simp] theorem lowerBlock_succ_succ {n : ℕ} (v : Fin n → ZMod 2)
    (N : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    lowerBlock v N i.succ j.succ = N i j := rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = 2 * x := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem exists_unit_lower_decomposition :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)), Aᵀ = A →
      ∃ (Λ M : Matrix (Fin n) (Fin n) (ZMod 2)),
        (∀ i j : Fin n, i ≠ j → Λ i j = 0) ∧
          M.BlockTriangular OrderDual.toDual ∧
          (∀ i : Fin n, M i i = 1) ∧ A + Λ = M * Mᵀ := by
  intro n
  induction n with
  | zero =>
      intro A _
      refine ⟨0, 1, ?_, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i j _; exact i.elim0
      · intro i; exact i.elim0
      · ext i; exact i.elim0
  | succ n ih =>
      intro A hA
      set a : ZMod 2 := A 0 0 with ha
      set v : Fin n → ZMod 2 := fun i => A i.succ 0 with hv
      set B : Matrix (Fin n) (Fin n) (ZMod 2) := fun i j => A i.succ j.succ with hB
      have hBsym : Bᵀ = B := by
        ext i j
        simp only [hB, Matrix.transpose_apply]
        exact (congrFun (congrFun hA (Fin.succ j)) (Fin.succ i)).symm
      have hB'sym : (B + Matrix.vecMulVec v v)ᵀ = B + Matrix.vecMulVec v v := by
        rw [Matrix.transpose_add, hBsym, Matrix.transpose_vecMulVec]
      obtain ⟨Λ', N, hΛ'diag, hNtri, hNdiag, hBN⟩ := ih (B + Matrix.vecMulVec v v) hB'sym
      set d : Fin (n + 1) → ZMod 2 :=
        fun i => Fin.cases (a + 1) (fun i' => Λ' i' i') i with hd
      let Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := Matrix.diagonal d
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := lowerBlock v N
      have hΛdiag : ∀ i j : Fin (n + 1), i ≠ j → Λ i j = 0 := by
        intro i j hij
        exact Matrix.diagonal_apply_ne d hij
      have hMtri : M.BlockTriangular OrderDual.toDual := by
        intro i j hij
        have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact absurd hlt (by simp)
            | succ j' => simp [M, lowerBlock]
        | succ i' =>
            cases j using Fin.cases with
            | zero => exact absurd hlt (by simp)
            | succ j' =>
                have hlt' : i' < j' := by simpa using! hlt
                have hzero : N i' j' = 0 :=
                  hNtri (OrderDual.toDual_lt_toDual.mpr hlt')
                simpa [M, lowerBlock] using! hzero
      have hMdiag : ∀ i : Fin (n + 1), M i i = 1 := by
        intro i
        cases i using Fin.cases with
        | zero => simp [M, lowerBlock]
        | succ i' => simpa [M, lowerBlock] using! hNdiag i'
      refine ⟨Λ, M, hΛdiag, hMtri, hMdiag, ?_⟩
      ext i j
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
              have hΛ00 : Λ 0 0 = a + 1 := by
                simp [Λ, hd]
              have hA00 : A 0 0 = a := ha.symm
              rw [hΛ00, hA00, Fin.sum_univ_succ]
              simp [M, lowerBlock]
              calc a + (a + 1) = (a + a) + 1 := by ring
                _ = 1 := by rw [zmod2_add_self, zero_add]
          | succ j' =>
              simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
              have h0 : (0 : Fin (n + 1)) ≠ j'.succ := by
                intro hh
                have hval := congrArg Fin.val hh
                simp at hval
              have hΛ0j : Λ 0 j'.succ = 0 :=
                Matrix.diagonal_apply_ne d h0
              have hsym : A 0 j'.succ = v j' := by
                have h := congrFun (congrFun hA j'.succ) 0
                simpa [hv, Matrix.transpose_apply] using! h
              rw [hΛ0j, add_zero, hsym, Fin.sum_univ_succ]
              simp [M, lowerBlock]
      | succ i' =>
          cases j using Fin.cases with
          | zero =>
              simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
              have hΛi0 : Λ i'.succ 0 = 0 :=
                Matrix.diagonal_apply_ne d (by simp)
              have hsym : A i'.succ 0 = v i' := rfl
              rw [hΛi0, add_zero, hsym, Fin.sum_univ_succ]
              simp [M, lowerBlock]
          | succ j' =>
              have hΛij : Λ i'.succ j'.succ =
                  if i' = j' then Λ' i' j' else 0 := by
                by_cases h : i' = j'
                · subst h
                  simp [Λ, hd]
                · have hne : i'.succ ≠ j'.succ := fun hs => h (Fin.succ_injective _ hs)
                  rw [show Λ i'.succ j'.succ = 0 from Matrix.diagonal_apply_ne d hne,
                    if_neg h]
              have hsum : (∑ k : Fin (n + 1), M i'.succ k * Mᵀ k j'.succ)
                  = v i' * v j' + ∑ k : Fin n, N i' k * N j' k := by
                rw [Fin.sum_univ_succ]
                simp [M, lowerBlock, Matrix.transpose_apply]
              have hNN : (∑ k : Fin n, N i' k * N j' k) = (N * Nᵀ) i' j' := by
                simp [Matrix.mul_apply, Matrix.transpose_apply]
              have hBN' : B i' j' + v i' * v j' + Λ' i' j' = (N * Nᵀ) i' j' := by
                have h := congrFun (congrFun hBN i') j'
                simpa [Matrix.add_apply, Matrix.vecMulVec_apply, add_assoc] using! h
              have hkey : v i' * v j' + (N * Nᵀ) i' j' = B i' j' + Λ' i' j' := by
                calc v i' * v j' + (N * Nᵀ) i' j'
                    = v i' * v j' + (B i' j' + v i' * v j' + Λ' i' j') := by rw [hBN']
                  _ = (B i' j' + Λ' i' j') + (v i' * v j' + v i' * v j') := by ring
                  _ = B i' j' + Λ' i' j' := by
                        rw [zmod2_add_self, add_zero]
              have hAij : A i'.succ j'.succ = B i' j' := rfl
              simp only [Matrix.add_apply, Matrix.mul_apply]
              rw [hAij, hΛij, hsum, hNN, hkey]
              by_cases h : i' = j'
              · subst h; simp
              · simp [h, hΛ'diag i' j' h]

theorem det_one_of_unit_lower {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (htri : M.BlockTriangular OrderDual.toDual) (hdiag : ∀ i : Fin n, M i i = 1) :
    M.det = 1 := by
  rw [Matrix.det_of_lowerTriangular M htri]
  simp [hdiag]

theorem exists_invertible_decomposition (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : Aᵀ = A) :
    ∃ (Λ M : Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ i j : Fin n, i ≠ j → Λ i j = 0) ∧ IsUnit M ∧ A + Λ = M * Mᵀ := by
  obtain ⟨Λ, M, hΛ, htri, hdiag, hMM⟩ := exists_unit_lower_decomposition n A hA
  have hdet : M.det = 1 := det_one_of_unit_lower M htri hdiag
  have hunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  exact ⟨Λ, M, hΛ, hunit, hMM⟩

theorem lemma7_symmetric_decomposition : lemma7_symmetric_decomposition_statement := by
  intro n A hA
  exact exists_invertible_decomposition n A hA

end Qatlib.Papers.StabilizerSim04.MainResults
