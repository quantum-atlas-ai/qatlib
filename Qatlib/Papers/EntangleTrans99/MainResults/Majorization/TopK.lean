/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EntangleTrans99.MainResults.Majorization.Basic

/-!
# Subset sums and sorted spectral prefixes

This module gives a variational description of sorted prefix sums: the first `k` entries of
`sortedDesc a` sum to the maximum over sets of `k` coordinates. The proofs compare submultisets
with descending initial segments and construct a set attaining the bound.

The theorem `majorizes_iff_forall_subset_sum` recasts `Majorizes` as inequalities over all
coordinate subsets, providing a tool for the spectral arguments of [Nielsen1999].

## Main statements

* `finset_sum_le_prefixSum`: bounds any coordinate subset sum by the matching sorted prefix.
* `exists_finset_sum_eq_prefixSum`: constructs a subset attaining that prefix sum.
* `majorizes_iff_forall_subset_sum`: characterizes majorization by subset-sum bounds.

## References

* [Nielsen, 1999][Nielsen1999]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.Majorization

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open scoped BigOperators

/-- The sum of a submultiset of a weakly descending list is bounded by the sum of the equally
long initial segment. -/
theorem take_sum_le_of_le {l : List ℝ} (hl : l.Pairwise (fun x y => ¬ x < y))
    {m : Multiset ℝ} (hm : m ≤ (l : Multiset ℝ)) :
    m.sum ≤ (l.take m.card).sum := by
  induction l generalizing m with
  | nil =>
    have hm0 : m = 0 := Multiset.le_zero.1 (by simpa using hm)
    subst hm0
    simp
  | cons x xs ih =>
    rw [← Multiset.cons_coe] at hm
    have htail : xs.Pairwise (fun x y => ¬ x < y) := hl.tail
    have hxle : ∀ y ∈ xs, y ≤ x := fun y hy =>
      le_of_not_gt (List.rel_of_pairwise_cons hl hy)
    rcases Nat.eq_zero_or_pos m.card with hc | hc
    · have hm0 : m = 0 := Multiset.card_eq_zero.1 hc
      subst hm0
      simp
    · by_cases hcount : Multiset.count x m ≤ Multiset.count x (xs : Multiset ℝ)
      · have hle : m ≤ (xs : Multiset ℝ) := by
          rw [Multiset.le_iff_count] at hm ⊢
          intro y
          by_cases hy : y = x
          · subst hy; exact hcount
          · have h1 := hm y
            rwa [Multiset.count_cons_of_ne hy] at h1
        have hlen : m.card ≤ xs.length := by
          have h2 := Multiset.card_le_card hle
          simpa using h2
        have hIH := ih htail hle
        have hkpos : 0 < m.card := hc
        have hklt : m.card - 1 < xs.length := by omega
        have hstep : (xs.take m.card).sum
            = (xs.take (m.card - 1)).sum + xs[m.card - 1] := by
          have hk : m.card = (m.card - 1) + 1 := by omega
          conv_lhs => rw [hk]
          exact List.sum_take_succ xs (m.card - 1) hklt
        have hlast : xs[m.card - 1] ≤ x := hxle _ (List.getElem_mem hklt)
        have hR : ((x :: xs).take m.card).sum
            = x + (xs.take (m.card - 1)).sum := by
          have hk : m.card = (m.card - 1) + 1 := by omega
          conv_lhs => rw [hk]
          rw [List.take_succ_cons, List.sum_cons]
        rw [hR]
        linarith
      · push Not at hcount
        have hxmem : x ∈ m := Multiset.count_pos.1 (by omega)
        let m' : Multiset ℝ := m.erase x
        have hm' : m = x ::ₘ m' := (Multiset.cons_erase hxmem).symm
        have hcard' : m'.card + 1 = m.card :=
          Multiset.card_erase_add_one hxmem
        have hle' : m' ≤ (xs : Multiset ℝ) := by
          rw [Multiset.le_iff_count] at hm ⊢
          intro y
          by_cases hy : y = x
          · have h1 := hm x
            rw [Multiset.count_cons_self] at h1
            have h2 : Multiset.count x m' = Multiset.count x m - 1 :=
              Multiset.count_erase_self x m
            rw [hy]
            omega
          · have h1 := hm y
            rw [Multiset.count_cons_of_ne hy] at h1
            have h2 : Multiset.count y m' = Multiset.count y m :=
              Multiset.count_erase_of_ne hy m
            omega
        have hIH := ih htail hle'
        have hR : ((x :: xs).take m.card).sum = x + (xs.take m'.card).sum := by
          rw [← hcard', List.take_succ_cons, List.sum_cons]
        rw [hR, hm', Multiset.sum_cons]
        linarith

/-- The sum over any `k` coordinates of `a` is at most the sum of the first `k` entries of
`sortedDesc a`. -/
theorem finset_sum_le_prefixSum {n : ℕ} (a : Fin n → ℝ) {k : ℕ} (_hk : k ≤ n)
    {s : Finset (Fin n)} (hcard : s.card = k) :
    ∑ i ∈ s, a i ≤ prefixSum (sortedDesc a) k := by
  rw [Finset.sum_eq_multiset_sum]
  have hsub : s.val ≤ (Finset.univ : Finset (Fin n)).val := by
    rw [Finset.val_le_iff]
    exact Finset.subset_univ s
  have hmap : s.val.map a ≤ (Finset.univ.val.map a : Multiset ℝ) :=
    Multiset.map_le_map hsub
  have heq : ((sortedDesc a) : Multiset ℝ) = Finset.univ.val.map a := by
    rw [← Multiset.coe_toList (Finset.univ.val.map a)]
    exact Multiset.coe_eq_coe.2 (sortedDesc_perm a)
  have hm : s.val.map a ≤ ((sortedDesc a) : Multiset ℝ) := by
    rwa [heq]
  have hmain := take_sum_le_of_le (sortedDesc_weakDesc a) hm
  have hcard' : (s.val.map a).card = k := by
    rw [Multiset.card_map]
    exact hcard
  rw [hcard'] at hmain
  simpa [prefixSum] using hmain

/-- Every submultiset of the values of `a` on a finite set is the multiset of values on some
subset of that set. -/
theorem exists_finset_map_eq {ι : Type*} [DecidableEq ι] (a : ι → ℝ) :
    ∀ t : Finset ι, ∀ m : Multiset ℝ, m ≤ t.val.map a →
      ∃ s : Finset ι, s ⊆ t ∧ s.val.map a = m := by
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro m hm
    have hm0 : m = 0 := Multiset.le_zero.1 (by simpa using hm)
    exact ⟨∅, by simp, by simp [hm0]⟩
  · intro i t' hi ih m hm
    rw [Finset.insert_val, Multiset.ndinsert_of_notMem, Multiset.map_cons] at hm
    swap
    · simpa using hi
    by_cases hcount : Multiset.count (a i) m ≤ Multiset.count (a i) (t'.val.map a)
    · have hle : m ≤ t'.val.map a := by
        rw [Multiset.le_iff_count] at hm ⊢
        intro y
        by_cases hy : y = a i
        · subst hy; exact hcount
        · have h1 := hm y
          rwa [Multiset.count_cons_of_ne hy] at h1
      rcases ih m hle with ⟨s, hsub, hs⟩
      exact ⟨s, hsub.trans (Finset.subset_insert i t'), hs⟩
    · push Not at hcount
      have hxmem : a i ∈ m := Multiset.count_pos.1 (by omega)
      let m' : Multiset ℝ := m.erase (a i)
      have hm' : m = a i ::ₘ m' := (Multiset.cons_erase hxmem).symm
      have hle' : m' ≤ t'.val.map a := by
        rw [Multiset.le_iff_count] at hm ⊢
        intro y
        by_cases hy : y = a i
        · subst hy
          have h1 := hm (a i)
          rw [Multiset.count_cons_self] at h1
          have h2 : Multiset.count (a i) m' = Multiset.count (a i) m - 1 :=
            Multiset.count_erase_self (a i) m
          omega
        · have h1 := hm y
          rw [Multiset.count_cons_of_ne hy] at h1
          have h2 : Multiset.count y m' = Multiset.count y m :=
            Multiset.count_erase_of_ne hy m
          omega
      rcases ih m' hle' with ⟨s', hsub', hs'⟩
      refine ⟨insert i s', ?_, ?_⟩
      · exact Finset.insert_subset (by simp) (hsub'.trans (Finset.subset_insert i t'))
      · rw [Finset.insert_val, Multiset.ndinsert_of_notMem]
        · rw [Multiset.map_cons, hs', ← hm']
        · exact fun hmem => hi (hsub' hmem)

/-- For `k ≤ n`, some set of `k` coordinates realizes the first `k` sorted prefix sum of `a`. -/
theorem exists_finset_sum_eq_prefixSum {n : ℕ} (a : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) :
    ∃ s : Finset (Fin n), s.card = k ∧ ∑ i ∈ s, a i = prefixSum (sortedDesc a) k := by
  have hm : (((sortedDesc a).take k : List ℝ) : Multiset ℝ) ≤ (Finset.univ.val.map a : Multiset ℝ) := by
    have htake : (((sortedDesc a).take k : List ℝ) : Multiset ℝ) ≤ ((sortedDesc a) : Multiset ℝ) := by
      rw [Multiset.le_iff_exists_add]
      refine ⟨(((sortedDesc a).drop k : List ℝ) : Multiset ℝ), ?_⟩
      rw [Multiset.coe_add, List.take_append_drop]
    have heq : ((sortedDesc a) : Multiset ℝ) = Finset.univ.val.map a := by
      rw [← Multiset.coe_toList (Finset.univ.val.map a)]
      exact Multiset.coe_eq_coe.2 (sortedDesc_perm a)
    rwa [heq] at htake
  obtain ⟨s, -, hs⟩ := exists_finset_map_eq a Finset.univ _ hm
  refine ⟨s, ?_, ?_⟩
  · have h1 : s.card = ((sortedDesc a).take k).length := by
      rw [Finset.card_def, ← Multiset.card_map, hs, Multiset.coe_card]
    rw [h1, List.length_take, sortedDesc_length]
    omega
  · rw [Finset.sum_eq_multiset_sum, hs, Multiset.sum_coe]
    rfl

/-- If every `k`-coordinate sum of `b` is bounded by the first `k` sorted prefix sum of `a`, the
same bound holds for the first `k` sorted prefix sum of `b`. -/
theorem prefixSum_le_of_forall_subset {n : ℕ} {a b : Fin n → ℝ} {k : ℕ} (hk : k ≤ n)
    (h : ∀ s : Finset (Fin n), s.card = k →
      ∑ i ∈ s, b i ≤ prefixSum (sortedDesc a) k) :
    prefixSum (sortedDesc b) k ≤ prefixSum (sortedDesc a) k := by
  obtain ⟨s, hcard, hsum⟩ := exists_finset_sum_eq_prefixSum b hk
  rw [← hsum]
  exact h s hcard

/-- The relation `Majorizes a b` is equivalent to bounding every `k`-coordinate sum of `b` by
the first `k` sorted prefix sum of `a`, for every `k ≤ n` [Nielsen1999]. -/
theorem majorizes_iff_forall_subset_sum {n : ℕ} (a b : Fin n → ℝ) :
    Majorizes a b ↔ ∀ k, k ≤ n → ∀ s : Finset (Fin n), s.card = k →
      ∑ i ∈ s, b i ≤ prefixSum (sortedDesc a) k := by
  constructor
  · intro h k hk s hcard
    exact le_trans (finset_sum_le_prefixSum b hk hcard) (h k hk)
  · intro h k hk
    exact prefixSum_le_of_forall_subset hk (h k hk)

end Qatlib.Papers.EntangleTrans99.MainResults.Majorization
