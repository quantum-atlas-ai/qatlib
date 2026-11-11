/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs

/-!
# Descending spectra and majorization

This module proves sorting and prefix-sum identities used in the spectral criterion of
[Nielsen1999]. The lemmas for `sortedDesc` preserve the values, length, and sum while
establishing descending order.

It also proves reflexivity and transitivity of `Majorizes` and gives its two-dimensional
characterization by inequalities for the maximum and total sum. For vectors of sum one, only the
maximum inequality remains.

## Main statements

* `majorizes_two_iff`: characterizes two-dimensional majorization by maximum and total-sum
  inequalities.
* `majorizes_two_iff_max_of_sum_one`: specializes the criterion to vectors of sum one.
* `majorizes_trans`: proves transitivity.

## References

* [Nielsen, 1999][Nielsen1999]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Majorization

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open scoped BigOperators

/-- The Boolean comparator that returns true exactly when `y < x`, for sorting real numbers in
descending order. -/
def descLe (x y : ℝ) : Bool := decide (y < x)

/-- Merging two weakly descending lists with `descLe` produces a weakly descending list. -/
theorem merge_weakDesc {l₁ l₂ : List ℝ}
    (h₁ : l₁.Pairwise (fun x y => ¬ x < y)) (h₂ : l₂.Pairwise (fun x y => ¬ x < y)) :
    (l₁.merge l₂ descLe).Pairwise (fun x y => ¬ x < y) := by
  induction l₁ generalizing l₂ with
  | nil => simpa [List.merge] using h₂
  | cons x l₁ ih₁ =>
    induction l₂ with
    | nil => simpa [List.merge] using h₁
    | cons y l₂ ih₂ =>
      rw [List.merge]
      split <;> rename_i h
      · have hyx : y < x := of_decide_eq_true h
        refine List.Pairwise.cons ?_ (ih₁ h₁.tail h₂)
        · intro z hz
          rw [List.mem_merge] at hz
          rcases hz with hz | hz
          · exact List.rel_of_pairwise_cons h₁ hz
          · rw [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact not_lt.2 (le_of_lt hyx)
            · exact fun hxz => List.rel_of_pairwise_cons h₂ hz (lt_trans hyx hxz)
      · have hxy : ¬ y < x := by simpa [descLe] using h
        have hxyle : x ≤ y := le_of_not_gt hxy
        refine List.Pairwise.cons ?_ (ih₂ h₂.tail)
        · intro z hz
          rw [List.mem_merge] at hz
          rcases hz with hz | hz
          · rw [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact hxy
            · exact fun hyz => List.rel_of_pairwise_cons h₁ hz (lt_of_le_of_lt hxyle hyz)
          · exact List.rel_of_pairwise_cons h₂ hz

/-- Merge sort with `descLe` produces a weakly descending list of real numbers. -/
theorem mergeSort_weakDesc (l : List ℝ) :
    (l.mergeSort descLe).Pairwise (fun x y => ¬ x < y) := by
  refine List.mergeSort.induct (motive := fun l _ =>
    (l.mergeSort descLe).Pairwise (fun x y => ¬ x < y)) ?_ ?_ ?_ l descLe
  · intro le
    simp
  · intro le a
    simp
  · intro a b xs le _ _ _ ih₂ ih₃
    change ((a :: b :: xs).mergeSort descLe).Pairwise (fun x y => ¬ x < y)
    rw [List.mergeSort.eq_3]
    exact merge_weakDesc ih₂ ih₃

/-- The list `sortedDesc a` is weakly descending. -/
theorem sortedDesc_weakDesc {n : ℕ} (a : Fin n → ℝ) :
    (sortedDesc a).Pairwise (fun x y => ¬ x < y) :=
  mergeSort_weakDesc _

/-- Listing the values of a function on `Fin n`, with multiplicity, gives a list of length `n`. -/
theorem length_univ_map_toList {n : ℕ} (a : Fin n → ℝ) :
    ((Finset.univ.val.map a).toList).length = n := by
  rw [Multiset.length_toList]
  simp

/-- The descending list `sortedDesc a` is a permutation of the list of values of `a`. -/
theorem sortedDesc_perm {n : ℕ} (a : Fin n → ℝ) :
    (sortedDesc a).Perm (Finset.univ.val.map a).toList :=
  List.mergeSort_perm _ _

/-- The descending list of values of a function on `Fin n` has length `n`. -/
theorem sortedDesc_length {n : ℕ} (a : Fin n → ℝ) : (sortedDesc a).length = n := by
  rw [(sortedDesc_perm a).length_eq, length_univ_map_toList]

/-- A real number belongs to `sortedDesc a` exactly when it is a value of `a`. -/
theorem sortedDesc_mem_iff {n : ℕ} (a : Fin n → ℝ) (x : ℝ) :
    x ∈ sortedDesc a ↔ ∃ i, a i = x := by
  rw [(sortedDesc_perm a).mem_iff, Multiset.mem_toList, Multiset.mem_map]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simp, hi⟩

/-- Sorting the values of `a` in descending order preserves their sum. -/
theorem sortedDesc_sum {n : ℕ} (a : Fin n → ℝ) : (sortedDesc a).sum = ∑ i, a i := by
  have hperm : (sortedDesc a).Perm (Finset.univ.val.map a).toList := sortedDesc_perm a
  rw [hperm.sum_eq, Multiset.sum_toList]
  rfl

/-- The first sorted prefix sum of a two-entry vector is its larger entry. -/
theorem prefixSum_sortedDesc_one (a : Fin 2 → ℝ) :
    prefixSum (sortedDesc a) 1 = max (a 0) (a 1) := by
  classical
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.1 (sortedDesc_length a)
  have hpair : ¬ x < y := by
    have h := sortedDesc_weakDesc a
    rw [hxy] at h
    exact List.rel_of_pairwise_cons h (by simp)
  have hyle : y ≤ x := le_of_not_gt hpair
  have hkey : ∀ i : Fin 2, a i ≤ x := by
    intro i
    have hmem : a i ∈ sortedDesc a := (sortedDesc_mem_iff a (a i)).2 ⟨i, rfl⟩
    rw [hxy] at hmem
    rcases (by simpa using hmem : a i = x ∨ a i = y) with h | h
    · exact le_of_eq h
    · exact le_of_eq h |>.trans hyle
  have hxle : x ≤ max (a 0) (a 1) := by
    have hmem : x ∈ sortedDesc a := by rw [hxy]; simp
    obtain ⟨i, hi⟩ := (sortedDesc_mem_iff a x).1 hmem
    rw [← hi]
    exact (Fin.forall_fin_two.2 ⟨le_max_left _ _, le_max_right _ _⟩ :
      ∀ i : Fin 2, a i ≤ max (a 0) (a 1)) i
  have heq : x = max (a 0) (a 1) := le_antisymm hxle (max_le (hkey 0) (hkey 1))
  rw [prefixSum, hxy, heq]
  simp

/-- The second sorted prefix sum of a two-entry vector is the sum of its entries. -/
theorem prefixSum_sortedDesc_two (a : Fin 2 → ℝ) :
    prefixSum (sortedDesc a) 2 = a 0 + a 1 := by
  have hlen : (sortedDesc a).length ≤ 2 := le_of_eq (sortedDesc_length a)
  rw [prefixSum, List.take_of_length_le hlen, sortedDesc_sum]
  rw [Fin.sum_univ_two]

/-- For two-entry real vectors, `Majorizes a b` is equivalent to the maximum and total sum of
`b` being at most those of `a` [Nielsen1999]. -/
theorem majorizes_two_iff (a b : Fin 2 → ℝ) :
    Majorizes a b ↔ max (b 0) (b 1) ≤ max (a 0) (a 1) ∧ b 0 + b 1 ≤ a 0 + a 1 := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    rw [prefixSum_sortedDesc_one b, prefixSum_sortedDesc_one a] at h1
    rw [prefixSum_sortedDesc_two b, prefixSum_sortedDesc_two a] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hmax, hsum⟩ k hk
    interval_cases k
    · simp [prefixSum]
    · simpa [prefixSum_sortedDesc_one b, prefixSum_sortedDesc_one a] using hmax
    · simpa [prefixSum_sortedDesc_two b, prefixSum_sortedDesc_two a] using hsum

/-- For two-entry real vectors whose entries sum to one, `Majorizes a b` is equivalent to the
maximum of `b` being at most the maximum of `a` [Nielsen1999]. -/
theorem majorizes_two_iff_max_of_sum_one {a b : Fin 2 → ℝ}
    (ha : a 0 + a 1 = 1) (hb : b 0 + b 1 = 1) :
    Majorizes a b ↔ max (b 0) (b 1) ≤ max (a 0) (a 1) := by
  rw [majorizes_two_iff]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, by rw [ha, hb]⟩

/-- Every finite real vector majorizes itself. -/
theorem majorizes_refl {n : ℕ} (a : Fin n → ℝ) : Majorizes a a := by
  intro k _
  exact le_rfl

/-- The relation `Majorizes` is transitive. -/
theorem majorizes_trans {n : ℕ} {a b c : Fin n → ℝ}
    (hab : Majorizes a b) (hbc : Majorizes b c) : Majorizes a c := by
  intro k hk
  exact (hbc k hk).trans (hab k hk)

end Qatlib.Papers.EntangleTrans99.MainResults.Majorization
