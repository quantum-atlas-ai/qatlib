/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset Matrix

def gammaBlock (a : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if a = 0 then 0 else if a = 1 then 1 else !![0, 1; 1, 0]

def phiPlus : Fin 2 → ℝ := fun _ => 1 / Real.sqrt 2

def phiMinus : Fin 2 → ℝ := fun s => if s = 0 then 1 / Real.sqrt 2 else -(1 / Real.sqrt 2)

def liftVec {N : ℕ} (φ : Fin 2 → ℝ) (v : Fin N → ℝ) : Fin 2 × Fin N → ℝ :=
  fun p => v p.2 * φ p.1

def psiMinus {N : ℕ} (j : Fin N) : Fin 2 × Fin N → ℝ := liftVec phiMinus (Pi.single j 1)

def psiPlus {N : ℕ} (j : Fin N) : Fin 2 × Fin N → ℝ := liftVec phiPlus (Pi.single j 1)

def realCast {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℝ :=
  A.map (Int.cast)

def blockConvert {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  fun p q => gammaBlock (A p.2 q.2) p.1 q.1

def dot {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

def laplacian {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := d • (1 : Matrix (Fin N) (Fin N) ℝ) - A

def cqr {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (q r : Fin N) : ℝ :=
  M q q - M q r

def deltaPath {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (q r : Fin N) : ℝ :=
  M q q - M q r

@[simp] lemma gammaBlock_zero : gammaBlock 0 = 0 := by
  simp [gammaBlock]

@[simp] lemma gammaBlock_one : gammaBlock 1 = 1 := by
  simp [gammaBlock]

lemma gammaBlock_neg_one : gammaBlock (-1) = !![0, 1; 1, 0] := by
  simp [gammaBlock]

lemma gammaBlock_zero_apply (s t : Fin 2) : gammaBlock 0 s t = 0 := by
  simp [gammaBlock]

lemma gammaBlock_one_apply (s t : Fin 2) : gammaBlock 1 s t = if s = t then 1 else 0 := by
  simp [gammaBlock, Matrix.one_apply]

lemma gammaBlock_neg_one_apply (s t : Fin 2) :
    gammaBlock (-1) s t = if s = 0 ∧ t = 1 then 1 else if s = 1 ∧ t = 0 then 1 else 0 := by
  fin_cases s <;> fin_cases t <;> simp [gammaBlock]

lemma gammaBlock_row_nz (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (univ.filter (fun t : Fin 2 => gammaBlock a s t ≠ 0)).card =
      if a = 0 then 0 else 1 := by
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock]
  · rcases hs with rfl | rfl
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock 1 (0:Fin 2) t ≠ 0)) = {0} by
        ext t; fin_cases t <;> simp [gammaBlock, Matrix.one_apply]]
      simp
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock 1 (1:Fin 2) t ≠ 0)) = {1} by
        ext t; fin_cases t <;> simp [gammaBlock, Matrix.one_apply]]
      simp
  · rcases hs with rfl | rfl
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock (-1) (0:Fin 2) t ≠ 0)) = {1} by
        ext t; fin_cases t <;> simp [gammaBlock]]
      simp
    · rw [show (univ.filter (fun t : Fin 2 => gammaBlock (-1) (1:Fin 2) t ≠ 0)) = {0} by
        ext t; fin_cases t <;> simp [gammaBlock]]
      simp

lemma gammaBlock_mulVec_phiMinus (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (∑ t : Fin 2, gammaBlock a s t * phiMinus t) = (a : ℝ) * phiMinus s := by
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock, phiMinus]
  · fin_cases s <;> simp [gammaBlock, phiMinus, Matrix.one_apply]
  · fin_cases s <;> simp [gammaBlock, phiMinus]

lemma gammaBlock_mulVec_phiPlus (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (∑ t : Fin 2, gammaBlock a s t * phiPlus t) = ((a : ℝ) ^ 2) * phiPlus s := by
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock, phiPlus]
  · fin_cases s <;> simp [gammaBlock, phiPlus, Matrix.one_apply]
  · fin_cases s <;> simp [gammaBlock, phiPlus]

lemma hsq_sqrt_two : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← mul_inv, h2]
  norm_num

theorem phiMinus_expectation_gammaBlock (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) :
    (∑ s : Fin 2, ∑ t : Fin 2, phiMinus s * gammaBlock a s t * phiMinus t) = (a : ℝ) := by
  rcases ha with rfl | rfl | rfl <;>
    simp [gammaBlock, phiMinus, Fin.sum_univ_two, Matrix.one_apply] <;>
    nlinarith [hsq_sqrt_two]

lemma phiMinus_product (s t : Fin 2) :
    phiMinus s * phiMinus t = if s = t then (1/2 : ℝ) else (-1/2 : ℝ) := by
  fin_cases s <;> fin_cases t <;> simp [phiMinus, hsq_sqrt_two] <;> norm_num

lemma dot_psiMinus_expand {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (j : Fin N) :
    dot (psiMinus j) (M *ᵥ psiMinus j) =
      ∑ s : Fin 2, ∑ t : Fin 2, phiMinus s * M (s, j) (t, j) * phiMinus t := by
  classical
  have hinner : ∀ p : Fin 2 × Fin N,
      (∑ q, M p q * psiMinus j q) = ∑ t : Fin 2, M p (t, j) * phiMinus t := by
    intro p
    rw [Fintype.sum_prod_type]
    have hx : ∀ x : Fin 2, (∑ y, M p (x, y) * psiMinus j (x, y)) =
        M p (x, j) * phiMinus x := by
      intro x
      rw [Finset.sum_eq_single j]
      · simp [psiMinus, liftVec, Pi.single_eq_same]
      · intro k _ hk
        simp [psiMinus, liftVec, Pi.single_eq_of_ne hk]
      · intro h
        exact absurd (Finset.mem_univ j) h
    simp only [hx]
  unfold dot Matrix.mulVec
  simp only [dotProduct, hinner]
  have houter : ∀ s : Fin 2,
      (∑ i, psiMinus j (s, i) * (∑ t, M (s, i) (t, j) * phiMinus t)) =
        ∑ t, phiMinus s * M (s, j) (t, j) * phiMinus t := by
    intro s
    rw [Finset.sum_eq_single j]
    · simp only [psiMinus, liftVec, Pi.single_eq_same]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    · intro i _ hi
      simp [psiMinus, liftVec, Pi.single_eq_of_ne hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun s _ => houter s

theorem phiMinus_bilinear_eq {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (j : Fin N)
    (hsym : M (0, j) (1, j) = M (1, j) (0, j))
    (hdiag : M (0, j) (0, j) = M (1, j) (1, j)) :
    dot (psiMinus j) (M *ᵥ psiMinus j) = M (0, j) (0, j) - M (0, j) (1, j) := by
  rw [dot_psiMinus_expand]
  have hrew : ∀ s t : Fin 2, phiMinus s * M (s, j) (t, j) * phiMinus t =
      (if s = t then (1/2:ℝ) else (-1/2:ℝ)) * M (s, j) (t, j) := by
    intro s t
    rw [show phiMinus s * M (s, j) (t, j) * phiMinus t =
        (phiMinus s * phiMinus t) * M (s, j) (t, j) by ring]
    rw [phiMinus_product]
  simp only [hrew, Fin.sum_univ_two]
  norm_num
  linarith [hsym, hdiag]

end Qatlib.Papers.BQPMixSparse06.MainResults
