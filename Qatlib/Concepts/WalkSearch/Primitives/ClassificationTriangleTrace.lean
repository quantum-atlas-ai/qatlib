/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationPartition

/-!
# Triangle counts from classification traces

Shows that the triangle-removal list produced by classification satisfies `removalTraceBound`,
including when traces from recursive stages are concatenated. This gives a triangle-count bound
of `n.choose 2 * τ` for the moved pair set, a combinatorial component of the graph-search
analysis; see [Ambainis2005].

## Main statements

* `classifyScan_triangle_trace`: The classification scan's moved triangle trace satisfies the
  removal threshold `τ` relative to its remaining pair set.
* `classifyScan_triCount_bound`: The triangle count of the scan's moved triangle pair set is at
  most `n.choose 2 * τ`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

/-- Concatenating the two removal traces preserves the threshold `τ` when their residual sets
satisfy the stated containment condition. -/
theorem removalTraceBound_append {Sd left : Finset (Fin n×Fin n)} {D T : List (Fin n×Fin n)} {τ : ℕ}
    (hD : removalTraceBound Sd D τ) (hT : removalTraceBound left T τ)
    (hsub : left∪T.toFinset⊆Sd) : removalTraceBound left (D++T) τ := by
  intro i hi
  by_cases hp : i < D.length
  · have hs : left∪((D++T).drop i).toFinset⊆Sd∪(D.drop i).toFinset := by
      rw [List.drop_append_of_le_length hp.le,List.toFinset_append]
      intro e he
      simp only [Finset.mem_union] at he ⊢
      rcases he with hl | hd | ht
      · exact Or.inl (hsub (Finset.mem_union_left _ hl))
      · exact Or.inr hd
      · exact Or.inl (hsub (Finset.mem_union_right _ ht))
    rw [List.getElem_append_left hp]
    exact (tOf_mono hs _ _).trans (hD i hp)
  · have hge : D.length ≤ i := by omega
    have hi' : i-D.length < T.length := by rw [List.length_append] at hi;omega
    rw [List.getElem_append_right hge,List.drop_append,List.drop_eq_nil_iff.mpr hge,List.nil_append]
    exact hT (i-D.length) hi'

/-- The classification scan's moved triangle trace satisfies the removal threshold `τ` relative
to its remaining pair set. -/
theorem classifyScan_triangle_trace (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) :
    removalTraceBound (classifyScan G sgs τ K c ttape stape vs S).left
      (classifyScan G sgs τ K c ttape stape vs S).movedT τ := by
  induction vs generalizing S with
  | nil => simp [classifyScan,removalTraceBound]
  | cons v vs ih =>
    have hd:=drainPaired_trace_bound S.edges τ S.edges.card
    rw [classifyScan]
    (try dsimp only)
    split_ifs with he hl
    · have hp:=partitionPayload_subsets (classifyScan_partition G sgs τ K c ttape stape vs (drainedPairSet S τ))
      exact removalTraceBound_append hd (ih (drainedPairSet S τ)) (Finset.union_subset hp.1 hp.2.1)
    · have hp:=partitionPayload_subsets (classifyScan_partition G sgs τ K c ttape stape vs (lowRemaining (drainedPairSet S τ) v))
      exact removalTraceBound_append hd (ih (lowRemaining (drainedPairSet S τ) v))
        (Finset.union_subset (hp.1.trans Finset.sdiff_subset) (hp.2.1.trans Finset.sdiff_subset))
    · cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | none =>
        have hp:=partitionPayload_subsets
            (classifyScan_partition G sgs τ K c ttape stape vs (highRemaining G (drainedPairSet S τ) v))
        exact removalTraceBound_append hd (ih (highRemaining G (drainedPairSet S τ) v))
          (Finset.union_subset (hp.1.trans Finset.sdiff_subset) (hp.2.1.trans Finset.sdiff_subset))
      | some p =>
        rcases p with ⟨w,w'⟩
        exact hd

/-- The triangle count of the scan's moved triangle pair set is at most `n.choose 2 * τ`. -/
theorem classifyScan_triCount_bound (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) :
    triCount (classifyScan G sgs τ K c ttape stape vs S).movedT.toFinset≤n.choose 2*τ := by
  have hp:=classifyScan_partition G sgs τ K c ttape stape vs S
  have ht:=classifyScan_triangle_trace G sgs τ K c ttape stape vs S
  apply fact5_removal n τ _ _
  · intro p
    exact List.mem_toFinset
  · exact hp.2.2.2.2
  · intro i hi
    exact (tOf_mono Finset.subset_union_right _ _).trans (ht i hi)
end Qatlib.Concepts.WalkSearch.Primitives
