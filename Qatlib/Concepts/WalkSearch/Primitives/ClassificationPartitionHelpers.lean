/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan

/-!
# Partition operations for classification

Defines `partitionPayload`, the disjoint-partition invariant for the remaining pairs and the two
moved components of a classification run. Helper results recover subset bounds and extend the
invariant when pairs are added to the edge bucket or prepended to the removal trace; see
[Ambainis2005] for the graph-search setting.

## Main statements

* `partitionPayload`: The assertion that `left`, `T.toFinset`, and `E` cover `S`, are pairwise
  disjoint, and the trace list `T` has no repetitions.
* `partitionPayload_addT`: A partition of `Sd` extends to one of `S` by prepending a
  repetition-free trace `D` when `Sd` and `D.toFinset` are disjoint and cover `S`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

/-- The assertion that `left`, `T.toFinset`, and `E` cover `S`, are pairwise disjoint, and the
trace list `T` has no repetitions. -/
def partitionPayload (S left : Finset (Fin n×Fin n)) (T : List (Fin n×Fin n))
    (E : Finset (Fin n×Fin n)) : Prop :=
  left∪T.toFinset∪E=S ∧ Disjoint left T.toFinset ∧ Disjoint left E ∧
    Disjoint T.toFinset E ∧ T.Nodup

/-- Each of the three components of a partition payload is a subset of its original set. -/
theorem partitionPayload_subsets {S left : Finset (Fin n×Fin n)} {T : List (Fin n×Fin n)}
    {E : Finset (Fin n×Fin n)} (h : partitionPayload S left T E) :
    left⊆S ∧ T.toFinset⊆S ∧ E⊆S := by
  rw [← h.1]
  exact ⟨Finset.subset_union_left.trans Finset.subset_union_left,
    Finset.subset_union_right.trans Finset.subset_union_left,Finset.subset_union_right⟩

/-- A partition of `S \ D` extends to a partition of `S` by adding `D ⊆ S` to the edge bucket. -/
theorem partitionPayload_addE {S left D E : Finset (Fin n×Fin n)} {T : List (Fin n×Fin n)}
    (hD : D⊆S) (h : partitionPayload (S\D) left T E) :
    partitionPayload S left T (D∪E) := by
  obtain ⟨hL,hT,hE⟩:=partitionPayload_subsets h
  refine ⟨?_,h.2.1,?_,?_,h.2.2.2.2⟩
  · ext e
    have hu : (e∈left ∨ e∈T.toFinset ∨ e∈E)↔e∈S ∧ e∉D := by
      simpa only [Finset.mem_union,Finset.mem_sdiff,or_assoc] using (Finset.ext_iff.mp h.1 e)
    simp only [Finset.mem_union]
    constructor
    · rintro ((hl | ht) | hd | he)
      · exact (hu.mp (Or.inl hl)).1
      · exact (hu.mp (Or.inr (Or.inl ht))).1
      · exact hD hd
      · exact (hu.mp (Or.inr (Or.inr he))).1
    · intro he
      by_cases hd : e∈D
      · exact Or.inr (Or.inl hd)
      · rcases hu.mpr ⟨he,hd⟩ with hl | ht | he
        · exact Or.inl (Or.inl hl)
        · exact Or.inl (Or.inr ht)
        · exact Or.inr (Or.inr he)
  · apply Finset.disjoint_left.mpr
    intro e hl he
    rcases Finset.mem_union.mp he with hd | he
    · exact (Finset.mem_sdiff.mp (hL hl)).2 hd
    · exact Finset.disjoint_left.mp h.2.2.1 hl he
  · apply Finset.disjoint_left.mpr
    intro e ht he
    rcases Finset.mem_union.mp he with hd | he
    · exact (Finset.mem_sdiff.mp (hT ht)).2 hd
    · exact Finset.disjoint_left.mp h.2.2.2.1 ht he

/-- A partition of `Sd` extends to one of `S` by prepending a repetition-free trace `D` when
`Sd` and `D.toFinset` are disjoint and cover `S`. -/
theorem partitionPayload_addT {S Sd left E : Finset (Fin n×Fin n)} {D T : List (Fin n×Fin n)}
    (hU : Sd∪D.toFinset=S) (hDis : Disjoint Sd D.toFinset) (hDN : D.Nodup)
    (h : partitionPayload Sd left T E) : partitionPayload S left (D++T) E := by
  obtain ⟨hL,hT,hE⟩:=partitionPayload_subsets h
  have hLD : Disjoint left D.toFinset := hDis.mono_left hL
  have hTD : Disjoint T.toFinset D.toFinset := hDis.mono_left hT
  have hED : Disjoint E D.toFinset := hDis.mono_left hE
  refine ⟨?_,?_,h.2.2.1,?_,?_⟩
  · rw [List.toFinset_append,← hU,← h.1]
    ext e
    simp only [Finset.mem_union]
    tauto
  · rw [List.toFinset_append]
    exact disjoint_sup_right.mpr ⟨hLD,h.2.1⟩
  · rw [List.toFinset_append]
    exact disjoint_sup_left.mpr ⟨hED.symm,h.2.2.2.1⟩
  · apply List.nodup_append.mpr
    refine ⟨hDN,h.2.2.2.2,?_⟩
    intro a ha b hb hab
    subst b
    exact Finset.disjoint_left.mp hTD (List.mem_toFinset.mpr hb) (List.mem_toFinset.mpr ha)
end Qatlib.Concepts.WalkSearch.Primitives
