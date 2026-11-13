/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

/-!
# Counting ordered group products outside a subgroup

`chainProd` multiplies a selected set of generators in increasing index order. The module
develops insertion and subgroup membership identities, then uses the least generator outside a
proper subgroup to pair index subsets.

With an identity generator at index zero, `lemma1_counting` and `lemma1_prob` bound the number
of fixed size subsets whose ordered product lies outside the subgroup. The intervening counting
lemmas evaluate the number of subsets containing both or neither of two distinguished indices.
See [MagniezNayak2005].

## Main statements

* `chainProd_insert`: Inserting `i ∉ A` factors the ordered product into the product below `i`,
  the generator `g i`, and the product above `i`.
* `lemma1_counting`: For a generating family with identity at index zero and `l ≥ 1`, the number
  of `l` element subsets is at most twice the number with product outside `K` plus the number
  satisfying `sameSide` for `badIndex`.
* `lemma1_prob`: For a generating family with identity at index zero and `2 ≤ l ≤ k`, at least
  the displayed fraction `(1 - p)/2` of the `l` element index subsets have ordered product
  outside the proper subgroup `K`.

## References

* [Magniez and Nayak, 2005][MagniezNayak2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Finset

variable {G : Type*} [Group G]

/-- The product of the generators indexed by `A`, taken in increasing index order. -/
noncomputable def chainProd {k : ℕ} (g : Fin k → G) (A : Finset (Fin k)) : G :=
  ((A.sort (· ≤ ·)).map g).prod

/-- The ordered product over the empty index set is the group identity. -/
@[simp]
theorem chainProd_empty {k : ℕ} (g : Fin k → G) : chainProd g ∅ = 1 := by
  simp [chainProd]

/-- The ordered product over a singleton index set is the corresponding generator. -/
theorem chainProd_singleton {k : ℕ} (g : Fin k → G) (i : Fin k) :
    chainProd g {i} = g i := by
  simp [chainProd]

/-- If every index in `B` is smaller than every index in `C`, sorting their union concatenates
the sorted lists of `B` and `C`. -/
theorem sort_union_separated {k : ℕ} {B C : Finset (Fin k)}
    (h : ∀ b ∈ B, ∀ c ∈ C, b < c) :
    (B ∪ C).sort (· ≤ ·) = B.sort (· ≤ ·) ++ C.sort (· ≤ ·) := by
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    exact fun a ha ha' => absurd (h a ha a ha') (lt_irrefl a)
  have hperm : List.Perm ((B ∪ C).sort (· ≤ ·)) (B.sort (· ≤ ·) ++ C.sort (· ≤ ·)) := by
    rw [List.perm_iff_count]
    intro a
    rw [List.count_append]
    have hL : ((B ∪ C).sort (· ≤ ·)).count a = (B ∪ C).val.count a := by
      rw [← Multiset.coe_count, Finset.sort_eq]
    have hB : (B.sort (· ≤ ·)).count a = B.val.count a := by
      rw [← Multiset.coe_count, Finset.sort_eq]
    have hC : (C.sort (· ≤ ·)).count a = C.val.count a := by
      rw [← Multiset.coe_count, Finset.sort_eq]
    rw [hL, hB, hC, Finset.union_val, Multiset.count_union]
    have hz : B.val.count a = 0 ∨ C.val.count a = 0 := by
      by_cases hb : a ∈ B
      · refine Or.inr ?_
        rw [Multiset.count_eq_zero]
        intro hc
        exact (Finset.disjoint_left.mp hdisj hb) hc
      · refine Or.inl ?_
        rw [Multiset.count_eq_zero]
        exact hb
    rcases hz with hz | hz
    · rw [hz]; simp
    · rw [hz]; simp
  refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _) ?_ hperm
  rw [List.pairwise_append]
  exact ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _,
    fun a ha b hb => le_of_lt (h a (Finset.mem_sort (· ≤ ·) |>.mp ha) b
      (Finset.mem_sort (· ≤ ·) |>.mp hb))⟩

/-- The ordered product over two separated index sets is the product of their ordered products. -/
theorem chainProd_union_separated {k : ℕ} (g : Fin k → G) {B C : Finset (Fin k)}
    (h : ∀ b ∈ B, ∀ c ∈ C, b < c) :
    chainProd g (B ∪ C) = chainProd g B * chainProd g C := by
  rw [chainProd, sort_union_separated h, List.map_append, List.prod_append]
  rfl

/-- If `i ∉ A`, the subsets of `A` below and above `i` have union `A`. -/
theorem filter_lt_union_filter_gt {k : ℕ} (A : Finset (Fin k)) {i : Fin k} (hi : i ∉ A) :
    A.filter (· < i) ∪ A.filter (i < ·) = A := by
  have hsplit := Finset.filter_union_filter_not_eq (fun x : Fin k => x < i) A
  have hcongr : A.filter (fun x => ¬ x < i) = A.filter (i < ·) := by
    refine Finset.filter_congr ?_
    intro x hx
    have hne : x ≠ i := fun h => hi (h ▸ hx)
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) hne.symm, fun h => not_lt.mpr (le_of_lt h)⟩
  rw [← hcongr]
  exact hsplit

/-- Inserting a new index into a sorted index set places it between the sorted indices below and
above it. -/
theorem sort_insert_split {k : ℕ} (A : Finset (Fin k)) {i : Fin k} (hi : i ∉ A) :
    (insert i A).sort (· ≤ ·) =
      (A.filter (· < i)).sort (· ≤ ·) ++ [i] ++ (A.filter (i < ·)).sort (· ≤ ·) := by
  set B := A.filter (· < i) with hB
  set C := A.filter (i < ·) with hC
  have hA : A = B ∪ C := by
    rw [hB, hC]
    exact (filter_lt_union_filter_gt A hi).symm
  have hiB : i ∉ B := by
    rw [hB]
    simp
  have hins : insert i A = B ∪ insert i C := by
    rw [hA]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have hsep : ∀ b ∈ B, ∀ c ∈ insert i C, b < c := by
    intro b hb c hc
    have hb' : b < i := by
      rw [hB] at hb
      exact (Finset.mem_filter.mp hb).2
    rcases Finset.mem_insert.mp hc with hc | hc
    · rw [hc]; exact hb'
    · rw [hC] at hc
      exact lt_trans hb' (Finset.mem_filter.mp hc).2
  have hiC : i ∉ C := by
    rw [hC]
    simp
  have hrest : (insert i C).sort (· ≤ ·) = [i] ++ C.sort (· ≤ ·) := by
    rw [Finset.sort_insert (r := (· ≤ ·)) (fun b hb => le_of_lt (by
      rw [hC] at hb
      exact (Finset.mem_filter.mp hb).2)) hiC]
    rfl
  rw [hins, sort_union_separated hsep, hrest, hB, hC]
  simp only [List.append_assoc]

/-- Inserting `i ∉ A` factors the ordered product into the product below `i`, the generator `g
i`, and the product above `i`. -/
theorem chainProd_insert {k : ℕ} (g : Fin k → G) (A : Finset (Fin k)) {i : Fin k}
    (hi : i ∉ A) :
    chainProd g (insert i A) =
      chainProd g (A.filter (· < i)) * g i * chainProd g (A.filter (i < ·)) := by
  rw [chainProd, sort_insert_split A hi, List.map_append, List.map_append, List.prod_append,
    List.prod_append]
  simp [chainProd, mul_assoc]

/-- A list product lies in a subgroup when every factor lies in that subgroup. -/
theorem list_prod_mem_subgroup (K : Subgroup G) {L : List G} (h : ∀ x ∈ L, x ∈ K) :
    L.prod ∈ K := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact K.mul_mem (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- An ordered generator product lies in a subgroup when every selected generator lies in it. -/
theorem chainProd_mem_subgroup {k : ℕ} (g : Fin k → G) (K : Subgroup G) {A : Finset (Fin k)}
    (h : ∀ a ∈ A, g a ∈ K) : chainProd g A ∈ K := by
  refine list_prod_mem_subgroup K ?_
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  exact h a ((Finset.mem_sort (· ≤ ·)).mp ha)

/-- A generating family for the whole group contains a generator outside any proper subgroup. -/
theorem exists_generator_not_mem {k : ℕ} (g : Fin k → G) (K : Subgroup G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) : ∃ j, g j ∉ K := by
  by_contra h
  push Not at h
  have hle : Subgroup.closure (Set.range g) ≤ K := by
    rw [Subgroup.closure_le]
    rintro x ⟨j, rfl⟩
    exact h j
  rw [hgen] at hle
  exact hK (top_le_iff.mp hle)

/-- The least index whose generator lies outside the proper subgroup `K`. -/
noncomputable def badIndex {k : ℕ} (g : Fin k → G) (K : Subgroup G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) : Fin k := by
  classical
  exact ((univ : Finset (Fin k)).filter (fun j => g j ∉ K)).min'
    (by
      obtain ⟨j, hj⟩ := exists_generator_not_mem g K hgen hK
      exact ⟨j, Finset.mem_filter.mpr ⟨mem_univ j, hj⟩⟩)

/-- The generator at `badIndex` lies outside `K`. -/
theorem badIndex_not_mem {k : ℕ} (g : Fin k → G) (K : Subgroup G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) :
    g (badIndex g K hgen hK) ∉ K := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem ((univ : Finset (Fin k)).filter
    (fun j => g j ∉ K)) _)).2

/-- Every generator with index below `badIndex` lies in `K`. -/
theorem mem_subgroup_of_lt_badIndex {k : ℕ} (g : Fin k → G) (K : Subgroup G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) {j : Fin k}
    (hj : j < badIndex g K hgen hK) : g j ∈ K := by
  classical
  by_contra h
  have hj' : j ∈ (univ : Finset (Fin k)).filter (fun j => g j ∉ K) :=
    Finset.mem_filter.mpr ⟨mem_univ j, h⟩
  exact absurd (Finset.min'_le _ _ hj') (not_le.mpr hj)

/-- If `A` omits `badIndex`, the products for `A` and for its insertion of `badIndex` cannot
both lie in `K`. -/
theorem not_both_chainProd_mem {k : ℕ} (g : Fin k → G) (K : Subgroup G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) {A : Finset (Fin k)}
    (hi : badIndex g K hgen hK ∉ A) :
    ¬ (chainProd g A ∈ K ∧ chainProd g (insert (badIndex g K hgen hK) A) ∈ K) := by
  classical
  set i := badIndex g K hgen hK
  set B := A.filter (· < i)
  set C := A.filter (i < ·)
  have hA : A = B ∪ C := (filter_lt_union_filter_gt A hi).symm
  have hBC : ∀ b ∈ B, ∀ c ∈ C, b < c := by
    intro b hb c hc
    exact lt_trans (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
  have hB : chainProd g B ∈ K := by
    refine chainProd_mem_subgroup g K ?_
    intro a ha
    exact mem_subgroup_of_lt_badIndex g K hgen hK (Finset.mem_filter.mp ha).2
  have hprodA : chainProd g A = chainProd g B * chainProd g C := by
    rw [hA, chainProd_union_separated g hBC]
  have hprodI : chainProd g (insert i A) = chainProd g B * g i * chainProd g C := by
    rw [chainProd_insert g A hi]
  rintro ⟨h1, h2⟩
  rw [hprodA] at h1
  rw [hprodI] at h2
  have hb : chainProd g C ∈ K := by
    have := K.mul_mem (K.inv_mem hB) h1
    simpa [mul_assoc] using this
  have hgi : g i ∈ K := by
    have := K.mul_mem (K.mul_mem (K.inv_mem hB) h2) (K.inv_mem hb)
    simpa [mul_assoc] using this
  exact badIndex_not_mem g K hgen hK hgi

section Counting

/-- The finite collection of all `l` element subsets of `Fin k`. -/
def lIndexSets (k l : ℕ) : Finset (Finset (Fin k)) := (univ : Finset (Fin k)).powersetCard l

/-- Membership in `lIndexSets k l` is equivalent to having cardinality `l`. -/
@[simp]
theorem mem_lIndexSets {k l : ℕ} {A : Finset (Fin k)} :
    A ∈ lIndexSets k l ↔ A.card = l := by
  simp [lIndexSets]

/-- There are `k.choose l` subsets in `lIndexSets k l`. -/
theorem card_lIndexSets (k l : ℕ) : (lIndexSets k l).card = k.choose l := by
  simp [lIndexSets, Finset.card_powersetCard]

/-- The zero index of `Fin k`, using the hypothesis `0 < k`. -/
abbrev idIdx {k : ℕ} (hk : 0 < k) : Fin k := ⟨0, hk⟩

/-- The property that `A` contains both `idIdx hk` and `i`, or contains neither. -/
def sameSide {k : ℕ} (hk : 0 < k) (i : Fin k) (A : Finset (Fin k)) : Prop :=
  (idIdx hk ∈ A ∧ i ∈ A) ∨ (idIdx hk ∉ A ∧ i ∉ A)

/-- The zero index `idIdx hk` is at most every index in `Fin k`. -/
theorem idIdx_le {k : ℕ} (hk : 0 < k) (b : Fin k) : idIdx hk ≤ b := by
  rw [Fin.le_def]
  simp

/-- Every index different from `idIdx hk` is strictly greater than it. -/
theorem idIdx_lt {k : ℕ} (hk : 0 < k) {i : Fin k} (hi : i ≠ idIdx hk) : idIdx hk < i := by
  rcases lt_or_gt_of_ne hi with h' | h'
  · exact absurd h' (not_lt.mpr (idIdx_le hk i))
  · exact h'

/-- The subset obtained by erasing `idIdx hk` and inserting `i`. -/
def partner {k : ℕ} (hk : 0 < k) (i : Fin k) (A : Finset (Fin k)) : Finset (Fin k) :=
  insert i (A.erase (idIdx hk))

/-- Erasing the zero index does not change the ordered product if its generator is the identity. -/
theorem chainProd_erase_idIdx {k : ℕ} (g : Fin k → G) (hk : 0 < k)
    (hg0 : g (idIdx hk) = 1) {A : Finset (Fin k)} (hA : idIdx hk ∈ A) :
    chainProd g (A.erase (idIdx hk)) = chainProd g A := by
  have hins : A = insert (idIdx hk) (A.erase (idIdx hk)) := (Finset.insert_erase hA).symm
  rw [hins, chainProd, chainProd,
    Finset.sort_insert (r := (· ≤ ·)) (fun b _ => idIdx_le hk b) (by simp)]
  simp [hg0]

end Counting

section LemmaOne

/-- If the generator at the zero index is the identity, `badIndex` is different from that index. -/
theorem badIndex_ne_idIdx {k : ℕ} (g : Fin k → G) (K : Subgroup G) {hk : 0 < k}
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) (hg0 : g (idIdx hk) = 1) :
    badIndex g K hgen hK ≠ idIdx hk := by
  intro h
  have hbad := badIndex_not_mem g K hgen hK
  rw [h, hg0] at hbad
  exact hbad K.one_mem

/-- For distinct zero and distinguished indices and `l ≥ 1`, equally many `l` element subsets
contain exactly the zero index as contain exactly the distinguished index. -/
theorem card_partQ_eq_partR {k l : ℕ} (hk : 0 < k) {i : Fin k} (hne : i ≠ idIdx hk)
    (hl1 : 1 ≤ l) :
    ((lIndexSets k l).filter (fun A => idIdx hk ∈ A ∧ i ∉ A)).card
      = ((lIndexSets k l).filter (fun A => idIdx hk ∉ A ∧ i ∈ A)).card := by
  classical
  set T := lIndexSets k l with hT
  have hne' : idIdx hk ≠ i := Ne.symm hne
  have hi_erase : ∀ A : Finset (Fin k), i ∉ A → i ∉ A.erase (idIdx hk) := by
    intro A hA h
    exact hA (Finset.mem_of_mem_erase h)
  refine Finset.card_bij'
    (fun A _ => insert i (A.erase (idIdx hk)))
    (fun B _ => insert (idIdx hk) (B.erase i)) ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hA ⊢
    obtain ⟨hAcard, hzA, hiA⟩ := hA
    have hie : i ∉ A.erase (idIdx hk) := hi_erase A hiA
    refine ⟨?_, ?_, by simp⟩
    · rw [Finset.card_insert_of_notMem hie, Finset.card_erase_of_mem hzA, hAcard]
      omega
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hne' h
      · exact (Finset.ne_of_mem_erase h) rfl
  · intro B hB
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hB ⊢
    obtain ⟨hBcard, hzB, hiB⟩ := hB
    have hze : idIdx hk ∉ B.erase i := by
      intro h
      exact hzB (Finset.mem_of_mem_erase h)
    refine ⟨?_, by simp, ?_⟩
    · rw [Finset.card_insert_of_notMem hze, Finset.card_erase_of_mem hiB, hBcard]
      omega
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hne h
      · exact (Finset.ne_of_mem_erase h) rfl
  · intro A hA
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hA
    obtain ⟨-, hzA, hiA⟩ := hA
    have hie : i ∉ A.erase (idIdx hk) := hi_erase A hiA
    try dsimp only
    rw [Finset.erase_insert hie, Finset.insert_erase hzA]
  · intro B hB
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hB
    obtain ⟨-, hzB, hiB⟩ := hB
    have hze : idIdx hk ∉ B.erase i := by
      intro h
      exact hzB (Finset.mem_of_mem_erase h)
    try dsimp only
    rw [Finset.erase_insert hze, Finset.insert_erase hiB]

end LemmaOne

section LemmaOneCounting

/-- Replacing the distinguished index by the zero index gives equal counts for the two displayed
families with subgroup membership tested on the corresponding partner products. -/
theorem card_partR_filter_eq {k l : ℕ} (g : Fin k → G) (K : Subgroup G) {hk : 0 < k}
    {i : Fin k} (hne : i ≠ idIdx hk) (hl1 : 1 ≤ l) :
    (((lIndexSets k l).filter (fun A => idIdx hk ∉ A ∧ i ∈ A)).filter
        (fun A => chainProd g A ∈ K)).card
      = (((lIndexSets k l).filter (fun A => idIdx hk ∈ A ∧ i ∉ A)).filter
        (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K)).card := by
  classical
  have hne' : idIdx hk ≠ i := Ne.symm hne
  set T := lIndexSets k l with hT
  refine Finset.card_bij' (fun B _ => insert (idIdx hk) (B.erase i))
    (fun A _ => insert i (A.erase (idIdx hk))) ?_ ?_ ?_ ?_
  · intro B hB
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hB ⊢
    obtain ⟨⟨hBcard, hzB, hiB⟩, hKB⟩ := hB
    have hze : idIdx hk ∉ B.erase i := fun h => hzB (Finset.mem_of_mem_erase h)
    have hie : i ∉ B.erase i := fun h => (Finset.ne_of_mem_erase h) rfl
    refine ⟨⟨?_, by simp, ?_⟩, ?_⟩
    · rw [Finset.card_insert_of_notMem hze, Finset.card_erase_of_mem hiB, hBcard]
      omega
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hne h
      · exact (Finset.ne_of_mem_erase h) rfl
    · show chainProd g (insert i ((insert (idIdx hk) (B.erase i)).erase (idIdx hk))) ∈ K
      rw [Finset.erase_insert hze, Finset.insert_erase hiB]
      exact hKB
  · intro A hA
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hA ⊢
    obtain ⟨⟨hAcard, hzA, hiA⟩, hKA⟩ := hA
    have hie : i ∉ A.erase (idIdx hk) := fun h => hiA (Finset.mem_of_mem_erase h)
    have hze : idIdx hk ∉ A.erase (idIdx hk) :=
      fun h => (Finset.ne_of_mem_erase h) rfl
    refine ⟨⟨?_, ?_, by simp⟩, ?_⟩
    · rw [Finset.card_insert_of_notMem hie, Finset.card_erase_of_mem hzA, hAcard]
      omega
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hne' h
      · exact (Finset.ne_of_mem_erase h) rfl
    · exact hKA
  · intro B hB
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hB
    obtain ⟨⟨-, hzB, hiB⟩, -⟩ := hB
    have hze : idIdx hk ∉ B.erase i := fun h => hzB (Finset.mem_of_mem_erase h)
    try dsimp only
    rw [Finset.erase_insert hze, Finset.insert_erase hiB]
  · intro A hA
    simp only [Finset.mem_filter, hT, mem_lIndexSets] at hA
    obtain ⟨⟨-, hzA, hiA⟩, -⟩ := hA
    have hie : i ∉ A.erase (idIdx hk) := fun h => hiA (Finset.mem_of_mem_erase h)
    try dsimp only
    rw [Finset.erase_insert hie, Finset.insert_erase hzA]

end LemmaOneCounting

section MainCounting

/-- For a generating family with identity at index zero and `l ≥ 1`, the number of `l` element
subsets is at most twice the number with product outside `K` plus the number satisfying
`sameSide` for `badIndex`. See [MagniezNayak2005]. -/
theorem lemma1_counting {k l : ℕ} (g : Fin k → G) (K : Subgroup G) {hk : 0 < k}
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤) (hg0 : g (idIdx hk) = 1)
    (hl1 : 1 ≤ l) :
    (lIndexSets k l).card ≤ 2 * ((lIndexSets k l).filter (fun A => chainProd g A ∉ K)).card
      + ((lIndexSets k l).filter (sameSide hk (badIndex g K hgen hK))).card := by
  classical
  set i := badIndex g K hgen hK with hi
  have hne : i ≠ idIdx hk := badIndex_ne_idIdx g K hgen hK hg0
  set T := lIndexSets k l with hT
  set P := T.filter (fun A => idIdx hk ∈ A ∧ i ∈ A) with hP
  set Q := T.filter (fun A => idIdx hk ∈ A ∧ i ∉ A) with hQ
  set R := T.filter (fun A => idIdx hk ∉ A ∧ i ∈ A) with hR
  set S := T.filter (fun A => idIdx hk ∉ A ∧ i ∉ A) with hS
  set Kf : Finset (Fin k) → Prop := fun A => chainProd g A ∈ K with hKf

  have hT_eq : T = ((P ∪ Q) ∪ R) ∪ S := by
    rw [hP, hQ, hR, hS]
    ext A
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdPQ : Disjoint P Q := by
    rw [hP, hQ, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.2 h.2
  have hdPR : Disjoint P R := by
    rw [hP, hR, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.1 h.1
  have hdPS : Disjoint P S := by
    rw [hP, hS, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.2 h.2
  have hdQR : Disjoint Q R := by
    rw [hQ, hR, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.1 h.1
  have hdQS : Disjoint Q S := by
    rw [hQ, hS, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.1 h.1
  have hdRS : Disjoint R S := by
    rw [hR, hS, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.2 h.2
  have hdPQR : Disjoint (P ∪ Q) R := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdPR, hdQR⟩
  have hdPQRS : Disjoint ((P ∪ Q) ∪ R) S := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rw [Finset.disjoint_union_left]; exact ⟨hdPS, hdQS⟩, hdRS⟩
  have hcardT : T.card = P.card + Q.card + R.card + S.card := by
    rw [hT_eq, Finset.card_union_of_disjoint hdPQRS, Finset.card_union_of_disjoint hdPQR,
      Finset.card_union_of_disjoint hdPQ]

  have hsame_eq : T.filter (sameSide hk i) = P ∪ S := by
    rw [hP, hS]
    ext A
    simp only [Finset.mem_filter, Finset.mem_union, sameSide]
    tauto
  have hcard_same : (T.filter (sameSide hk i)).card = P.card + S.card := by
    rw [hsame_eq, Finset.card_union_of_disjoint hdPS]

  have hQR : Q.card = R.card := by
    rw [hQ, hR, hT]
    exact card_partQ_eq_partR hk hne hl1

  have hKsplit : T.filter Kf = ((P.filter Kf ∪ Q.filter Kf) ∪ R.filter Kf) ∪ S.filter Kf := by
    rw [hT_eq]
    simp only [Finset.filter_union]
  have hdPQ' : Disjoint (P.filter Kf) (Q.filter Kf) :=
      hdPQ.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdQR' : Disjoint (Q.filter Kf) (R.filter Kf) :=
      hdQR.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdPR' : Disjoint (P.filter Kf) (R.filter Kf) :=
      hdPR.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdRS' : Disjoint (R.filter Kf) (S.filter Kf) :=
      hdRS.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdQS' : Disjoint (Q.filter Kf) (S.filter Kf) :=
      hdQS.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdPS' : Disjoint (P.filter Kf) (S.filter Kf) :=
      hdPS.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdPQR' : Disjoint ((P.filter Kf) ∪ (Q.filter Kf)) (R.filter Kf) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdPR', hdQR'⟩
  have hdPQRS' : Disjoint (((P.filter Kf) ∪ (Q.filter Kf)) ∪ (R.filter Kf)) (S.filter Kf) := by
    rw [Finset.disjoint_union_left]
    exact ⟨by rw [Finset.disjoint_union_left]; exact ⟨hdPS', hdQS'⟩, hdRS'⟩
  have hKcard : (T.filter Kf).card =
      (P.filter Kf).card + (Q.filter Kf).card + (R.filter Kf).card + (S.filter Kf).card := by
    rw [hKsplit, Finset.card_union_of_disjoint hdPQRS', Finset.card_union_of_disjoint hdPQR',
      Finset.card_union_of_disjoint hdPQ']

  have htrans : (R.filter Kf).card =
      (Q.filter (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K)).card := by
    have h := card_partR_filter_eq g K hne hl1
    rw [← hT] at h
    exact h

  have hdisjQ : Disjoint (Q.filter Kf)
      (Q.filter (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K)) := by
    rw [Finset.disjoint_filter]
    intro A hA h1 h2
    obtain ⟨-, hzA, hiA⟩ := Finset.mem_filter.mp hA
    have hie : i ∉ A.erase (idIdx hk) := fun h => hiA (Finset.mem_of_mem_erase h)
    have hnot := not_both_chainProd_mem g K hgen hK (A := A.erase (idIdx hk)) hie
    rw [chainProd_erase_idIdx g hk hg0 hzA] at hnot
    exact hnot ⟨h1, h2⟩
  have hQbound : (Q.filter Kf).card +
      (Q.filter (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K)).card ≤ Q.card := by
    have hsub : Q.filter Kf ∪ Q.filter (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K) ⊆ Q :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    calc (Q.filter Kf).card + (Q.filter (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K)).card
        = (Q.filter Kf ∪ Q.filter (fun A => chainProd g (insert i (A.erase (idIdx hk))) ∈ K)).card :=
          (Finset.card_union_of_disjoint hdisjQ).symm
      _ ≤ Q.card := Finset.card_le_card hsub

  have hbound : (T.filter Kf).card ≤ P.card + S.card + Q.card := by
    have hP' : (P.filter Kf).card ≤ P.card := Finset.card_filter_le _ _
    have hS' : (S.filter Kf).card ≤ S.card := Finset.card_filter_le _ _
    omega

  have hsum : (T.filter Kf).card + (T.filter (fun A => chainProd g A ∉ K)).card = T.card :=
    Finset.card_filter_add_card_filter_not Kf
  rw [hcard_same, hcardT]
  omega

end MainCounting

section SameSideCount

/-- The `l` element index subsets containing both `i` and `j`. -/
def bothIn (k l : ℕ) (i j : Fin k) : Finset (Finset (Fin k)) :=
  (lIndexSets k l).filter (fun A => i ∈ A ∧ j ∈ A)

/-- The `l` element index subsets containing neither `i` nor `j`. -/
def bothOut (k l : ℕ) (i j : Fin k) : Finset (Finset (Fin k)) :=
  (lIndexSets k l).filter (fun A => i ∉ A ∧ j ∉ A)

/-- The set of indices in `Fin k` other than `i` and `j`. -/
def pairCompl {k : ℕ} (i j : Fin k) : Finset (Fin k) :=
  ((univ : Finset (Fin k)).erase i).erase j

/-- An index belongs to `pairCompl i j` exactly when it differs from both `i` and `j`. -/
theorem mem_pairCompl {k : ℕ} {i j x : Fin k} :
    x ∈ pairCompl i j ↔ x ≠ i ∧ x ≠ j := by
  simp [pairCompl, and_comm]

/-- For distinct `i,j`, their complement in `Fin k` has cardinality `k - 2`. -/
theorem card_pairCompl {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    (pairCompl i j).card = k - 2 := by
  have hj : j ∈ (univ : Finset (Fin k)).erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hi : i ∈ (univ : Finset (Fin k)) := Finset.mem_univ i
  rw [pairCompl, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi,
    Finset.card_univ, Fintype.card_fin]
  omega

/-- For distinct `i,j` and `k,l ≥ 2`, there are `(k-2).choose (l-2)` subsets of size `l`
containing both indices. -/
theorem card_bothIn {k l : ℕ} (_hk : 2 ≤ k) (hl : 2 ≤ l) {i j : Fin k} (hij : i ≠ j) :
    (bothIn k l i j).card = (k - 2).choose (l - 2) := by
  classical
  have hmem : ∀ A ∈ bothIn k l i j,
      (A.erase i).erase j ∈ (pairCompl i j).powersetCard (l - 2) := by
    intro A hA
    simp only [bothIn, Finset.mem_filter, mem_lIndexSets] at hA
    obtain ⟨hAcard, hiA, hjA⟩ := hA
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      rw [mem_pairCompl]
      exact ⟨Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx),
        Finset.ne_of_mem_erase hx⟩
    · have hj' : j ∈ A.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjA⟩
      rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hiA, hAcard]
      omega
  have hinj : ∀ A ∈ bothIn k l i j, ∀ B ∈ bothIn k l i j,
      (A.erase i).erase j = (B.erase i).erase j → A = B := by
    intro A hA B hB heq
    simp only [bothIn, Finset.mem_filter, mem_lIndexSets] at hA hB
    obtain ⟨-, hiA, hjA⟩ := hA
    obtain ⟨-, hiB, hjB⟩ := hB
    have hj' : j ∈ A.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjA⟩
    have hj'' : j ∈ B.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjB⟩
    have hA' : A = insert i (insert j ((A.erase i).erase j)) := by
      calc A = insert i (A.erase i) := (Finset.insert_erase hiA).symm
        _ = insert i (insert j ((A.erase i).erase j)) := by rw [Finset.insert_erase hj']
    have hB' : B = insert i (insert j ((B.erase i).erase j)) := by
      calc B = insert i (B.erase i) := (Finset.insert_erase hiB).symm
        _ = insert i (insert j ((B.erase i).erase j)) := by rw [Finset.insert_erase hj'']
    rw [hA', hB', heq]
  have hsurj : ∀ B ∈ (pairCompl i j).powersetCard (l - 2),
      ∃ A ∈ bothIn k l i j, (A.erase i).erase j = B := by
    intro B hB
    obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB
    have hiB : i ∉ B := by
      intro h
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hBsub h)).2).1 rfl
    have hjB : j ∉ B := by
      intro h
      exact (Finset.mem_erase.mp (hBsub h)).1 rfl
    have hijnB : i ∉ insert j B := by
      intro h
      rcases Finset.mem_insert.mp h with h' | h'
      · exact hij h'
      · exact hiB h'
    refine ⟨insert i (insert j B), ?_, ?_⟩
    · simp only [bothIn, Finset.mem_filter, mem_lIndexSets]
      refine ⟨?_, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
      · rw [Finset.card_insert_of_notMem hijnB, Finset.card_insert_of_notMem hjB, hBcard]
        omega
      · exact Finset.mem_insert_self _ _
    · rw [Finset.erase_insert hijnB, Finset.erase_insert hjB]
  rw [← card_pairCompl hij, ← Finset.card_powersetCard]
  refine Finset.card_bij (fun A _ => (A.erase i).erase j) hmem hinj ?_
  intro b hb
  obtain ⟨a, ha, hfa⟩ := hsurj b hb
  exact ⟨a, ha, hfa⟩

/-- For distinct `i,j` with `k ≥ 2` and `l ≤ k`, there are `(k-2).choose l` subsets of size `l`
containing neither index. -/
theorem card_bothOut {k l : ℕ} (_hk : 2 ≤ k) (_hlk : l ≤ k) {i j : Fin k} (hij : i ≠ j) :
    (bothOut k l i j).card = (k - 2).choose l := by
  classical
  have hmem : ∀ A ∈ bothOut k l i j, A ∈ (pairCompl i j).powersetCard l := by
    intro A hA
    simp only [bothOut, Finset.mem_filter, mem_lIndexSets] at hA
    obtain ⟨hAcard, hiA, hjA⟩ := hA
    refine Finset.mem_powersetCard.mpr ⟨?_, hAcard⟩
    intro x hx
    rw [mem_pairCompl]
    exact ⟨fun h => hiA (h ▸ hx), fun h => hjA (h ▸ hx)⟩
  have hinj : ∀ A ∈ bothOut k l i j, ∀ B ∈ bothOut k l i j, A = B → A = B :=
    fun _ _ _ _ h => h
  have hsurj : ∀ B ∈ (pairCompl i j).powersetCard l,
      ∃ A ∈ bothOut k l i j, A = B := by
    intro B hB
    obtain ⟨hBsub, hBcard⟩ := Finset.mem_powersetCard.mp hB
    have hiB : i ∉ B := by
      intro h
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hBsub h)).2).1 rfl
    have hjB : j ∉ B := by
      intro h
      exact (Finset.mem_erase.mp (hBsub h)).1 rfl
    exact ⟨B, by simp [bothOut, hBcard, hiB, hjB], rfl⟩
  rw [← card_pairCompl hij, ← Finset.card_powersetCard]
  refine Finset.card_bij (fun A _ => A) hmem hinj ?_
  intro b hb
  obtain ⟨a, ha, hfa⟩ := hsurj b hb
  exact ⟨a, ha, hfa⟩

/-- For `2 ≤ l ≤ k` and distinct `i,j`, the number of `l` element subsets containing both or
neither is `(k-2).choose (l-2) + (k-2).choose l`. -/
theorem card_sameSideSets {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hlk : l ≤ k)
    {i j : Fin k} (hij : i ≠ j) :
    ((lIndexSets k l).filter (fun A => (i ∈ A ∧ j ∈ A) ∨ (i ∉ A ∧ j ∉ A))).card
      = (k - 2).choose (l - 2) + (k - 2).choose l := by
  classical
  have hunion : (lIndexSets k l).filter (fun A => (i ∈ A ∧ j ∈ A) ∨ (i ∉ A ∧ j ∉ A))
      = bothIn k l i j ∪ bothOut k l i j := by
    ext A
    simp only [bothIn, bothOut, Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisj : Disjoint (bothIn k l i j) (bothOut k l i j) := by
    rw [bothIn, bothOut, Finset.disjoint_filter]
    intro A _ h h'
    exact h'.1 h.1
  rw [hunion, Finset.card_union_of_disjoint hdisj, card_bothIn hk hl hij,
    card_bothOut hk hlk hij]

/-- For `2 ≤ l ≤ k`, the ratio of the same side subset count to `k.choose l` equals `(l*(l-1) +
(k-l)*(k-l-1)) / (k*(k-1))` over the rationals. See [MagniezNayak2005]. -/
theorem p_eq_sameSide_ratio {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hlk : l ≤ k)
    {i j : Fin k} (_hij : i ≠ j) :
    (((k - 2).choose (l - 2) + (k - 2).choose l : ℕ) : ℚ) / (k.choose l : ℚ)
      = (((l : ℚ) * (l - 1) + ((k : ℚ) - l) * ((k : ℚ) - l - 1)) /
          ((k : ℚ) * (k - 1))) := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (k : ℚ) - 1 ≠ 0 := by
    have h2 : (2 : ℚ) ≤ k := by exact_mod_cast hk
    intro h; linarith
  have hkl : (k.choose l : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hlk).ne'

  have h1nat : k.choose l * l.choose 2 = k.choose 2 * (k - 2).choose (l - 2) := by
    have := Nat.choose_mul (n := k) (k := l) (s := 2) hl
    simpa [Nat.sub_sub] using this
  have h2nat : k.choose l * (k - l).choose 2 = k.choose 2 * (k - 2).choose l := by
    by_cases h2kl : 2 ≤ k - l
    · have hsym : k.choose l = k.choose (k - l) := (Nat.choose_symm hlk).symm
      have hstep := Nat.choose_mul (n := k) (k := k - l) (s := 2) h2kl
      rw [hsym]
      calc k.choose (k - l) * (k - l).choose 2
          = k.choose 2 * (k - 2).choose (k - l - 2) := hstep
        _ = k.choose 2 * (k - 2).choose l := by
            have : k - l - 2 = k - 2 - l := by omega
            rw [this, Nat.choose_symm (by omega)]
    · have hzero1 : (k - l).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hzero2 : (k - 2).choose l = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hzero1, hzero2, mul_zero, mul_zero]
  have h1 : ((k - 2).choose (l - 2) : ℚ) =
      ((k.choose l : ℚ) * ((l : ℚ) * (l - 1)) / ((k : ℚ) * (k - 1))) := by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) h1nat
    push_cast at hcast
    rw [Nat.cast_choose_two (K := ℚ) k, Nat.cast_choose_two (K := ℚ) l] at hcast
    field_simp at hcast ⊢
    linarith [hcast]
  have h2 : ((k - 2).choose l : ℚ) =
      ((k.choose l : ℚ) * (((k : ℚ) - l) * ((k : ℚ) - l - 1)) /
        ((k : ℚ) * (k - 1))) := by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) h2nat
    push_cast at hcast
    rw [Nat.cast_choose_two (K := ℚ) k, Nat.cast_choose_two (K := ℚ) (k - l)] at hcast
    have hsub : ((k - l : ℕ) : ℚ) = (k : ℚ) - l := by
      rw [Nat.cast_sub hlk]
    rw [hsub] at hcast
    field_simp at hcast ⊢
    linarith [hcast]
  push_cast
  rw [h1, h2]
  field_simp

/-- For a generating family with identity at index zero and `2 ≤ l ≤ k`, at least the displayed
fraction `(1 - p)/2` of the `l` element index subsets have ordered product outside the
proper subgroup `K`. See [MagniezNayak2005]. -/
theorem lemma1_prob {k l : ℕ} (g : Fin k → G) (K : Subgroup G) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hlk : l ≤ k) (hgen : Subgroup.closure (Set.range g) = ⊤) (hK : K ≠ ⊤)
    (hg0 : g (idIdx (by omega : 0 < k)) = 1) :
    (1 - (((l : ℚ) * (l - 1) + ((k : ℚ) - l) * ((k : ℚ) - l - 1)) /
        ((k : ℚ) * (k - 1)))) / 2 * ((lIndexSets k l).card : ℚ)
      ≤ (((lIndexSets k l).filter (fun A => chainProd g A ∉ K)).card : ℚ) := by
  classical
  have hkpos : 0 < k := by omega
  set i := badIndex g K hgen hK with hi
  set p : ℚ := ((l : ℚ) * (l - 1) + ((k : ℚ) - l) * ((k : ℚ) - l - 1)) /
      ((k : ℚ) * (k - 1)) with hp
  have hne : i ≠ idIdx hkpos := badIndex_ne_idIdx g K hgen hK hg0
  have hcount := lemma1_counting (l := l) g K hgen hK hg0 (by omega)
  have hsame : ((lIndexSets k l).filter (sameSide hkpos i)).card
      = (k - 2).choose (l - 2) + (k - 2).choose l := by
    have hfilter : (lIndexSets k l).filter (sameSide hkpos i)
        = (lIndexSets k l).filter
            (fun A => (i ∈ A ∧ idIdx hkpos ∈ A) ∨ (i ∉ A ∧ idIdx hkpos ∉ A)) := by
      apply Finset.filter_congr
      intro A _
      simp only [sameSide]
      tauto
    rw [hfilter]
    exact card_sameSideSets hk hl hlk hne
  have hratio : ((((k - 2).choose (l - 2) + (k - 2).choose l : ℕ) : ℚ) /
      (k.choose l : ℚ)) = p := by
    rw [hp]
    exact p_eq_sameSide_ratio hk hl hlk hne
  rw [hsame] at hcount
  have hcl : ((k.choose l : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hlk).ne'
  have hratio' : (((k - 2).choose (l - 2) + (k - 2).choose l : ℕ) : ℚ)
      = p * (k.choose l : ℚ) := by
    have h := hratio
    field_simp at h
    linarith
  have hcountQ : ((lIndexSets k l).card : ℚ) ≤
      2 * (((lIndexSets k l).filter (fun A => chainProd g A ∉ K)).card : ℚ) +
        (((k - 2).choose (l - 2) + (k - 2).choose l : ℕ) : ℚ) := by
    exact_mod_cast hcount
  have hTq : ((lIndexSets k l).card : ℚ) = (k.choose l : ℚ) := by
    rw [card_lIndexSets]
  rw [hratio', hTq] at hcountQ
  rw [hTq]
  nlinarith [hcountQ]

end SameSideCount

end Qatlib.Papers.GrpCommTest05.MainResults
