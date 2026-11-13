/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationPartition

/-!
# Exhaustion of classification remainders

Defines `avoidsVertex` and proves that a classification scan returning no triangle leaves no
pair incident to a processed vertex. Scanning all vertices therefore leaves the remaining pair
set empty, completing a termination invariant for graph classification; see [Ambainis2005] for
the search setting.

## Main statements

* `classifyScan_processed`: If a classification scan returns no triangle, its remaining pairs
  avoid every vertex in the processed list.
* `classifyScan_full_left_empty`: If the scan over all vertices returns no triangle, its
  remaining pair set is empty.

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

/-- The condition that neither endpoint of any pair in `S` equals `v`. -/
def avoidsVertex (S : Finset (Fin n×Fin n)) (v : Fin n) : Prop :=
  ∀ a b,(a,b)∈S→a≠v ∧ b≠v

/-- A subset of a pair set avoiding `v` also avoids `v`. -/
theorem avoidsVertex_mono {S T : Finset (Fin n×Fin n)} {v : Fin n} (h : S⊆T)
    (ht : avoidsVertex T v) : avoidsVertex S v := fun a b hab=>ht a b (h hab)

/-- If `pairsAt S v` is empty, no pair in `S` has `v` as an endpoint. -/
theorem avoidsVertex_of_no_pairs (S : Finset (Fin n×Fin n)) (v : Fin n) (h : pairsAt S v=∅) :
    avoidsVertex S v := by
  intro a b hab
  have hn : ¬(a=v ∨ b=v) := by
    intro hv
    have hm : (a,b)∈pairsAt S v :=Finset.mem_filter.mpr ⟨hab,hv⟩
    rw [h] at hm
    exact Finset.notMem_empty _ hm
  exact not_or.mp hn

/-- The low-degree remainder contains no pair incident to the processed vertex. -/
theorem lowRemaining_avoids (S : SymmetricPairSet n) (v : Fin n) : avoidsVertex (lowRemaining S v).edges v := by
  intro a b hab
  have hh:=Finset.mem_sdiff.mp hab
  constructor
  · intro hv;exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,Or.inl hv⟩)
  · intro hv;exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,Or.inr hv⟩)

/-- The high-degree remainder contains no pair incident to the processed vertex. -/
theorem highRemaining_avoids (G : UGraph n) (S : SymmetricPairSet n) (v : Fin n) : avoidsVertex (highRemaining G S v).edges v := by
  intro a b hab
  have hh:=Finset.mem_sdiff.mp hab
  constructor
  · intro hv;exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,Or.inl hv⟩)
  · intro hv;exact hh.2 (Finset.mem_filter.mpr ⟨hh.1,Or.inr (Or.inl hv)⟩)

/-- If a classification scan returns no triangle, its remaining pairs avoid every vertex in the
processed list. -/
theorem classifyScan_processed (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n)
    (hnone : (classifyScan G sgs τ K c ttape stape vs S).triangle=none) :
    ∀ v∈vs,avoidsVertex (classifyScan G sgs τ K c ttape stape vs S).left v := by
  induction vs generalizing S with
  | nil => simp
  | cons v vs ih =>
    rw [classifyScan] at hnone ⊢
    dsimp only at hnone ⊢
    split_ifs with he hl
    · simp only [if_pos he] at hnone
      have hp:=partitionPayload_subsets
          (classifyScan_partition G sgs τ K c ttape stape vs (drainedPairSet S τ))
      have ha:=avoidsVertex_mono hp.1 (avoidsVertex_of_no_pairs (drainedPairSet S τ).edges v he)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih _ hnone x hx
    · simp only [if_neg he,if_pos hl] at hnone
      have hp:=partitionPayload_subsets
          (classifyScan_partition G sgs τ K c ttape stape vs (lowRemaining (drainedPairSet S τ) v))
      have ha:=avoidsVertex_mono hp.1 (lowRemaining_avoids (drainedPairSet S τ) v)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact ih _ hnone x hx
    · simp only [if_neg he,if_neg hl] at hnone
      cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | some p =>
        rw [hrun] at hnone
        rcases p with ⟨w,w'⟩
        cases hnone
      | none =>
        rw [hrun] at hnone
        have hp:=partitionPayload_subsets
            (classifyScan_partition G sgs τ K c ttape stape vs (highRemaining G (drainedPairSet S τ) v))
        have ha:=avoidsVertex_mono hp.1 (highRemaining_avoids G (drainedPairSet S τ) v)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact ih _ hnone x hx

/-- If the scan over all vertices returns no triangle, its remaining pair set is empty. -/
theorem classifyScan_full_left_empty (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (S : SymmetricPairSet n)
    (hnone : (classifyScan G sgs τ K c ttape stape Finset.univ.toList S).triangle=none) :
    (classifyScan G sgs τ K c ttape stape Finset.univ.toList S).left=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨a,b⟩ hab
  exact (classifyScan_processed G sgs τ K c ttape stape Finset.univ.toList S hnone a
    (Finset.mem_toList.mpr (Finset.mem_univ a)) a b hab).1 rfl
end Qatlib.Concepts.WalkSearch.Primitives
