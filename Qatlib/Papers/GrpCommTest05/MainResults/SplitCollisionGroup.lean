/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.Submonoid.Centralizer
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Matrix

noncomputable def I2 : Matrix (Fin 2) (Fin 2) ℂ := 1

noncomputable def X2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

noncomputable def Z2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

noncomputable def Y2 : Matrix (Fin 2) (Fin 2) ℂ := X2 * Z2

theorem X2_mul_Z2_ne : X2 * Z2 ≠ Z2 * X2 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [X2, Z2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

theorem Y2_ne_one : Y2 ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [Y2, X2, Z2, Matrix.mul_apply, Fin.sum_univ_two] at h01

abbrev BlockMat (k : ℕ) := (Fin k ⊕ Fin k) → Matrix (Fin 2) (Fin 2) ℂ

noncomputable def aGen {k : ℕ} (i j : Fin k) : BlockMat k :=
  fun b =>
    match b with
    | Sum.inl c => if c = i then Y2 else 1
    | Sum.inr c => if c = j then Z2 else 1

noncomputable def bGen {k : ℕ} (i j : Fin k) : BlockMat k :=
  fun b =>
    match b with
    | Sum.inl c => if c = i then Y2 else 1
    | Sum.inr c => if c = j then X2 else 1

noncomputable def splitGen {k : ℕ} (F : Fin k → Fin k) (P : Fin k → Bool) (i : Fin k) : BlockMat k :=
  fun b =>
    match b with
    | Sum.inl c => if c = i then Y2 else 1
    | Sum.inr c =>
        if c = F i then (if P i then Z2 else X2) else 1

theorem aGen_bGen_noncomm {k : ℕ} (i j : Fin k) :
    aGen i j * bGen i j ≠ bGen i j * aGen i j := by
  intro h
  have hb := congrFun h (Sum.inr j)
  have : Z2 * X2 = X2 * Z2 := by simpa [aGen, bGen, Pi.mul_apply] using hb
  exact X2_mul_Z2_ne this.symm

theorem splitGen_comm_of_injective {k : ℕ} (F : Fin k → Fin k) (P : Fin k → Bool)
    (hF : Function.Injective F) (i j : Fin k) :
    splitGen F P i * splitGen F P j = splitGen F P j * splitGen F P i := by
  funext b
  rcases b with c | c
  · simp only [Pi.mul_apply, splitGen]
    by_cases hci : c = i
    · subst hci
      by_cases hcj : c = j
      · subst hcj; simp
      · simp [hcj]
    · by_cases hcj : c = j
      · subst hcj; simp [hci]
      · simp [hci, hcj]
  · by_cases hci : c = F i <;> by_cases hcj : c = F j
    · have hij : i = j := hF (hci.symm.trans hcj)
      subst hij; simp
    · have hFij : F i ≠ F j := fun h => hcj (hci.trans h)
      simp [splitGen, hci, hFij]
    · have hFji : F j ≠ F i := fun h => hci (hcj.trans h)
      simp [splitGen, hcj, hFji]
    · simp [splitGen, hci, hcj]

theorem splitGen_noncomm_of_split {k : ℕ} (F : Fin k → Fin k) (P : Fin k → Bool)
    {i j : Fin k} (_hij : i ≠ j) (hFi : F i = F j) (hi : P i = true) (hj : P j = false) :
    splitGen F P i * splitGen F P j ≠ splitGen F P j * splitGen F P i := by
  intro h
  have hb := congrFun h (Sum.inr (F i))
  have : Z2 * X2 = X2 * Z2 := by
    simpa [splitGen, Pi.mul_apply, hFi, hi, hj] using hb
  exact X2_mul_Z2_ne this.symm

theorem splitGen_injective {k : ℕ} (F : Fin k → Fin k) (P : Fin k → Bool) :
    Function.Injective (splitGen F P) := by
  intro i j h
  by_contra hij
  have hb := congrFun h (Sum.inl i)
  have : Y2 = 1 := by
    simpa [splitGen, hij] using hb
  exact Y2_ne_one this

theorem splitGen_closure_commutative {k : ℕ} (F : Fin k → Fin k) (P : Fin k → Bool)
    (hF : Function.Injective F) :
    IsMulCommutative (Submonoid.closure (Set.range (splitGen F P))) := by
  apply Submonoid.isMulCommutative_closure
  intro a ha b hb _
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact splitGen_comm_of_injective F P hF i j

end Qatlib.Papers.GrpCommTest05.MainResults
