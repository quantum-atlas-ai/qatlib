/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Qatlib.Papers.WeighMatrix00.MainResults.WeighingMatrix
import Qatlib.Papers.WeighMatrix00.MainResults.Theorem1WeighingProcedure
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

open Matrix
open scoped Kronecker

theorem kronecker_entry {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℤ)
    (B : Matrix (Fin b) (Fin b) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hB : ∀ i j, B i j = -1 ∨ B i j = 0 ∨ B i j = 1) :
    ∀ i j, (A ⊗ₖ B) i j = -1 ∨ (A ⊗ₖ B) i j = 0 ∨ (A ⊗ₖ B) i j = 1 := by
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [Matrix.kronecker_apply]
  rcases hA i₁ j₁ with h | h | h <;> rcases hB i₂ j₂ with h' | h' | h' <;> simp [h, h']

theorem kronecker_gram {a b k l : ℕ} (A : Matrix (Fin a) (Fin a) ℤ)
    (B : Matrix (Fin b) (Fin b) ℤ)
    (hA : A * Aᵀ = (k : ℤ) • (1 : Matrix (Fin a) (Fin a) ℤ))
    (hB : B * Bᵀ = (l : ℤ) • (1 : Matrix (Fin b) (Fin b) ℤ)) :
    (A ⊗ₖ B) * (A ⊗ₖ B)ᵀ =
      ((k * l : ℕ) : ℤ) • (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℤ) := by
  have htr : (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    simp [Matrix.transpose_apply, Matrix.kronecker_apply]
  rw [htr, ← Matrix.mul_kronecker_mul A Aᵀ B Bᵀ, hA, hB]
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  rw [Matrix.kronecker_apply]
  by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;>
    simp [Matrix.smul_apply, Matrix.one_apply, h1, h2, Prod.mk.injEq, Nat.cast_mul]

theorem submatrix_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {N k : ℕ}
    (A : Matrix ι ι ℤ) (hA : A * Aᵀ = (k : ℤ) • (1 : Matrix ι ι ℤ)) (e : ι ≃ Fin N) :
    (A.submatrix e.symm e.symm) * (A.submatrix e.symm e.symm)ᵀ =
      (k : ℤ) • (1 : Matrix (Fin N) (Fin N) ℤ) := by
  have hb : Function.Bijective (e.symm : Fin N → ι) := e.symm.bijective
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul A Aᵀ e.symm e.symm e.symm hb, hA]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.natCast_apply, Matrix.intCast_apply, e.symm.injective.eq_iff]

def oneWeighingMatrix : WeighingMatrix 1 1 where
  mat := fun _ _ => 1
  entry := fun _ _ => Or.inr (Or.inr rfl)
  gram := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      Fin.sum_univ_one]

def tensorStep {n k : ℕ} (M : WeighingMatrix n k) {a b : ℕ} (A : WeighingMatrix a b) :
    WeighingMatrix (a * n) (b * k) where
  mat := (A.mat ⊗ₖ M.mat).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  entry := fun i j =>
    kronecker_entry A.mat M.mat A.entry M.entry (finProdFinEquiv.symm i)
      (finProdFinEquiv.symm j)
  gram := submatrix_gram (A.mat ⊗ₖ M.mat)
    (kronecker_gram A.mat M.mat A.gram M.gram) finProdFinEquiv

def tPow (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => tPow n t * n

theorem tPow_eq_pow (n t : ℕ) : tPow n t = n ^ t := by
  induction t with
  | zero => simp [tPow]
  | succ t ih => rw [tPow, ih, Nat.pow_succ]

def tensorPow {n k : ℕ} (M : WeighingMatrix n k) : (t : ℕ) → WeighingMatrix (tPow n t) (tPow k t)
  | 0 => oneWeighingMatrix
  | t + 1 => tensorStep M (tensorPow M t)

theorem tPow_pos {k : ℕ} (hk : 0 < k) (t : ℕ) : 0 < tPow k t := by
  induction t with
  | zero => simp [tPow]
  | succ t ih => rw [tPow]; exact Nat.mul_pos ih hk

theorem tPow_le {n k : ℕ} (hkn : k ≤ n) (t : ℕ) : tPow k t ≤ tPow n t := by
  induction t with
  | zero => simp [tPow]
  | succ t ih => rw [tPow, tPow]; exact Nat.mul_le_mul ih hkn

def WeighingMatrix.castSize {N N' k : ℕ} (h : N = N') (M : WeighingMatrix N k) :
    WeighingMatrix N' k := by
  subst h
  exact M

def WeighingMatrix.castWeight {N k k' : ℕ} (h : k = k') (M : WeighingMatrix N k) :
    WeighingMatrix N k' := by
  subst h
  exact M

theorem source_corollary1_tensorFamily {n k : ℕ} (M : WeighingMatrix n k)
    (hk : 0 < k) (hkn : k ≤ n) (t : ℕ) :
    ∃ MN : WeighingMatrix (n ^ t) (k ^ t), ∃ P : WeighingProcedure MN,
      P.oracleCalls ≤
        Nat.ceil (Real.pi / 4 * Real.sqrt ((n ^ t : ℝ) / (k ^ t : ℝ))) + 1 := by
  have hN : tPow n t = n ^ t := tPow_eq_pow n t
  have hK : tPow k t = k ^ t := tPow_eq_pow k t
  let MN : WeighingMatrix (n ^ t) (k ^ t) :=
    (tensorPow M t).castSize hN |>.castWeight hK
  have hKpos : 0 < k ^ t := pow_pos hk t
  have hKN : k ^ t ≤ n ^ t := Nat.pow_le_pow_left hkn t
  obtain ⟨P, hP, -⟩ := source_theorem1_weighingProcedure MN hKpos hKN
  exact ⟨MN, P, by simpa [Nat.cast_pow] using hP⟩

theorem queryBound_rpow {n k : ℕ} (hn : 1 < n) (hk : 0 < k) (t : ℕ) :
    Real.sqrt ((n : ℝ) ^ t / (k : ℝ) ^ t) =
      ((n : ℝ) ^ t) ^ ((1 - Real.log (k : ℝ) / Real.log (n : ℝ)) / 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hNpos : (0 : ℝ) < (n : ℝ) ^ t := pow_pos hn0 t
  have hKpos : (0 : ℝ) < (k : ℝ) ^ t := pow_pos hk0 t
  have hn1 : (n : ℝ) ≠ 1 := by
    have hn1' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hn0 hn1
  have hNlog : Real.log ((n : ℝ) ^ t) = (t : ℝ) * Real.log (n : ℝ) := by
    rw [Real.log_pow]
  have hKlog : Real.log ((k : ℝ) ^ t) = (t : ℝ) * Real.log (k : ℝ) := by
    rw [Real.log_pow]
  have eL : Real.sqrt ((n : ℝ) ^ t / (k : ℝ) ^ t) =
      Real.exp (Real.log ((n : ℝ) ^ t / (k : ℝ) ^ t) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hNpos hKpos) (1 / 2)]
  have eR : ((n : ℝ) ^ t) ^ ((1 - Real.log (k : ℝ) / Real.log (n : ℝ)) / 2) =
      Real.exp (Real.log ((n : ℝ) ^ t) *
        ((1 - Real.log (k : ℝ) / Real.log (n : ℝ)) / 2)) := by
    rw [Real.rpow_def_of_pos hNpos]
  rw [eL, eR, Real.exp_injective.eq_iff,
    Real.log_div (ne_of_gt hNpos) (ne_of_gt hKpos), hNlog, hKlog]
  field_simp

end Qatlib.Papers.WeighMatrix00.MainResults
