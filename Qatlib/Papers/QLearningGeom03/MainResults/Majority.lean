/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.QLearningGeom03.MainResults.GroupAlgebraZN2
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

def wt {n : ℕ} (b : Bits n) : ℕ := (Finset.univ.filter (fun i => b i ≠ 0)).card

def ones (n : ℕ) : Bits n := fun _ => 1

lemma wt_le {n : ℕ} (b : Bits n) : wt b ≤ n := by
  unfold wt
  calc (Finset.univ.filter (fun i => b i ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have h : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h0 | h1
  · left; rw [h, h0]; norm_num
  · right; rw [h, h1]; norm_num

lemma wt_add_ones {n : ℕ} (b : Bits n) : wt (b + ones n) = n - wt b := by
  have hp : Finset.univ.filter (fun i : Fin n => (b + ones n) i ≠ 0)
      = Finset.univ.filter (fun i : Fin n => b i = 0) := by
    apply Finset.filter_congr
    intro i _
    simp only [ones, Pi.add_apply]
    constructor
    · intro h
      rcases zmod2_eq_zero_or_one (b i) with h0 | h1
      · exact h0
      · exfalso
        apply h
        rw [h1]
        decide
    · intro h0
      rw [h0]; norm_num
  unfold wt
  rw [hp]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => b i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hnot : Finset.univ.filter (fun i : Fin n => ¬ (b i = 0))
      = Finset.univ.filter (fun i : Fin n => b i ≠ 0) := rfl
  rw [hnot] at hcard
  omega

lemma wt_neg {n : ℕ} (b : Bits n) : wt (-b) = wt b := by
  unfold wt
  congr 1
  apply Finset.filter_congr
  intro i _
  simp

noncomputable def majPhi {n : ℕ} (b : Bits n) : ℂ :=
  if 2 * wt b ≤ n then -1 else 1

lemma majPhi_neg {n : ℕ} (b : Bits n) : majPhi (-b) = majPhi b := by
  unfold majPhi
  rw [wt_neg]

lemma majPhi_add_ones {n m : ℕ} (hn : n = 2 * m + 1) (b : Bits n) :
    majPhi (b + ones n) = - majPhi b := by
  have harith : 2 * (n - wt b) ≤ n ↔ ¬ (2 * wt b ≤ n) := by
    have hw : wt b ≤ n := wt_le b
    omega
  have hiff : 2 * wt (b + ones n) ≤ n ↔ ¬ (2 * wt b ≤ n) := by
    rw [wt_add_ones]
    exact harith
  unfold majPhi
  by_cases h : 2 * wt b ≤ n
  · have h' : ¬ 2 * wt (b + ones n) ≤ n := by
      rw [hiff]
      intro hc
      exact hc h
    rw [if_neg h', if_pos h]
    norm_num
  · have h' : 2 * wt (b + ones n) ≤ n := by
      rw [hiff]
      exact h
    rw [if_pos h', if_neg h]

noncomputable def majCoeff {n : ℕ} (b : Bits n) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * majPhi b

noncomputable def majMatrix {n : ℕ} : Matrix (Bits n) (Bits n) ℂ :=
  fun a x => majCoeff (a - x)

theorem majMatrix_eq_groupAlgebraElem {n : ℕ} :
    majMatrix (n := n) = groupAlgebraElem (majCoeff (n := n)) := by
  ext a x
  rw [groupAlgebraElem_apply]
  rfl

noncomputable def majEigen {n : ℕ} (c : Bits n) : ℂ :=
  ∑ x, majCoeff x * chi c x

lemma majEigen_eq {n : ℕ} (c : Bits n) :
    majEigen c = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * ∑ x, majPhi x * chi c x := by
  unfold majEigen majCoeff
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem maj_diagonalization {n : ℕ} :
    hadamard n * majMatrix (n := n) * hadamard n
      = Matrix.diagonal (majEigen (n := n)) := by
  rw [majMatrix_eq_groupAlgebraElem]
  exact hadamard_conj_groupAlgebraElem _

lemma majMatrix_add_ones {n m : ℕ} (hn : n = 2 * m + 1) (a x : Bits n) :
    majMatrix (a + ones n) x = - majMatrix a x := by
  unfold majMatrix majCoeff
  rw [show a + ones n - x = (a - x) + ones n by abel]
  rw [majPhi_add_ones hn]
  ring

lemma majMatrix_diag {n : ℕ} (x : Bits n) :
    majMatrix x x = majCoeff (0 : Bits n) := by
  unfold majMatrix
  rw [sub_self]

lemma majMatrix_symmetric {n : ℕ} : (majMatrix (n := n))ᵀ = majMatrix := by
  ext a x
  rw [Matrix.transpose_apply]
  unfold majMatrix majCoeff
  rw [show x - a = -(a - x) by abel, majPhi_neg]

end Qatlib.Papers.QLearningGeom03.MainResults
