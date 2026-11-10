/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Defs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset Matrix

lemma reorder_entry {N : ℕ} {A : Matrix (Fin N) (Fin N) ℤ}
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (i j : Fin N) :
    A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
  rcases hA i j with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

lemma gammaBlock_entry_zero_or_one (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (s t : Fin 2) : gammaBlock a s t = 0 ∨ gammaBlock a s t = 1 := by
  rcases ha with rfl | rfl | rfl
  · exact Or.inl (by simp [gammaBlock])
  · fin_cases s <;> fin_cases t <;> simp [gammaBlock, Matrix.one_apply]
  · fin_cases s <;> fin_cases t <;> simp [gammaBlock]

theorem blockConvert_entry_zero_or_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (p q : Fin 2 × Fin N) :
    blockConvert A p q = 0 ∨ blockConvert A p q = 1 := by
  unfold blockConvert
  exact gammaBlock_entry_zero_or_one (A p.2 q.2) (reorder_entry hA p.2 q.2) p.1 q.1

lemma gammaBlock_row_sum (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s : Fin 2) :
    (∑ t : Fin 2, if gammaBlock a s t ≠ 0 then (1 : ℕ) else 0) =
      (if a ≠ 0 then 1 else 0) := by
  have hc := gammaBlock_row_nz a ha s
  rw [Finset.card_eq_sum_ones, Finset.sum_filter] at hc
  rw [hc]
  by_cases h : a = 0 <;> simp [h]

theorem blockConvert_row_card {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (s : Fin 2) (i : Fin N) :
    (univ.filter (fun x : Fin 2 × Fin N => blockConvert A (s, i) x ≠ 0)).card =
      (univ.filter (fun j : Fin N => A i j ≠ 0)).card := by
  classical
  have hAi : ∀ j : Fin N, A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := fun j => reorder_entry hA i j
  have hL : (univ.filter (fun x : Fin 2 × Fin N => blockConvert A (s, i) x ≠ 0)).card
      = ∑ j : Fin N, (if A i j ≠ 0 then (1 : ℕ) else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [blockConvert]
    exact gammaBlock_row_sum (A i j) (hAi j) s
  have hR : (univ.filter (fun j : Fin N => A i j ≠ 0)).card
      = ∑ j : Fin N, (if A i j ≠ 0 then (1 : ℕ) else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hL, hR]

theorem lemma3_sparse_conversion {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ i, (univ.filter (fun j : Fin N => A i j ≠ 0)).card = 4)
    (s : Fin 2) (i : Fin N) :
    (univ.filter (fun x : Fin 2 × Fin N => blockConvert A (s, i) x ≠ 0)).card = 4 := by
  rw [blockConvert_row_card A hA s i, hdeg]

theorem add_transpose_row_card_le {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    (univ.filter (fun j : Fin N => W i j + W j i ≠ 0)).card ≤
      (univ.filter (fun j : Fin N => W i j ≠ 0)).card +
        (univ.filter (fun j : Fin N => W j i ≠ 0)).card := by
  classical
  have hsub : (univ.filter (fun j : Fin N => W i j + W j i ≠ 0)) ⊆
      (univ.filter (fun j : Fin N => W i j ≠ 0)) ∪
        (univ.filter (fun j : Fin N => W j i ≠ 0)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨-, hj⟩ := hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : W i j = 0
    · by_cases h2 : W j i = 0
      · exact absurd hj (by rw [h1, h2]; norm_num)
      · exact Or.inr ⟨Finset.mem_univ _, h2⟩
    · exact Or.inl ⟨Finset.mem_univ _, h1⟩
  calc (univ.filter (fun j : Fin N => W i j + W j i ≠ 0)).card
      ≤ ((univ.filter (fun j : Fin N => W i j ≠ 0)) ∪
          (univ.filter (fun j : Fin N => W j i ≠ 0))).card := Finset.card_le_card hsub
    _ ≤ _ + _ := Finset.card_union_le _ _

theorem add_transpose_row_card_le_four {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ)
    (hrow : ∀ i, (univ.filter (fun j : Fin N => W i j ≠ 0)).card ≤ 2)
    (hcol : ∀ i, (univ.filter (fun j : Fin N => W j i ≠ 0)).card ≤ 2) (i : Fin N) :
    (univ.filter (fun j : Fin N => W i j + W j i ≠ 0)).card ≤ 4 := by
  have h := add_transpose_row_card_le W i
  have h1 := hrow i
  have h2 := hcol i
  omega

end Qatlib.Papers.BQPMixSparse06.MainResults
